"""Read-only Dash display for explicitly started QCAL-EXP01 acquisition.

Importing this module or creating the application never opens a UDP socket or
starts acquisition. The CLI owns the receiver lifecycle.
"""

from __future__ import annotations

import argparse
import math
import os
import threading
import time
from collections import deque
from collections.abc import Callable, Mapping
from dataclasses import asdict, dataclass
from typing import Any

from dash import Dash, Input, Output, dcc, html
import numpy as np
import plotly.graph_objects as go
from scipy import signal


SnapshotProvider = Callable[[], Mapping[str, Any] | None]


def _finite(value: Any) -> float | None:
    """Return a finite numeric measurement, or None for unavailable data."""
    if isinstance(value, bool):
        return None
    try:
        number = float(value)
    except (TypeError, ValueError, OverflowError):
        return None
    return number if math.isfinite(number) else None


def _read_snapshot(provider: SnapshotProvider | None) -> Mapping[str, Any] | None:
    """Read acquisition state without allowing provider failures to crash the UI."""
    if provider is None:
        return None
    try:
        snapshot = provider()
    except Exception:
        return None
    return snapshot if isinstance(snapshot, Mapping) else None


def _empty_spectrum(message: str) -> go.Figure:
    """Create an explicitly unavailable phase spectrum, never synthetic traces."""
    figure = go.Figure()
    figure.update_layout(
        title=message,
        xaxis_title="Frecuencia de fase demodulada (Hz)",
        yaxis_title="PSD de fase (rad²/Hz)",
        template="plotly_dark",
    )
    return figure


def display_state(
    snapshot: Mapping[str, Any] | None,
    *,
    stale_after: float = 2.0,
    now: float | None = None,
) -> dict[str, Any]:
    """Translate immutable acquisition snapshots into conservative display state.

    Missing, rejected, disconnected, or stale measurements cannot provide an
    evidence verdict. Source provenance is an operator declaration, not hardware
    authentication.
    """
    now = time.monotonic() if now is None else now
    snapshot = snapshot or {}
    receiver = snapshot.get("receiver", {})
    dsp = snapshot.get("dsp", {})
    receiver = receiver if isinstance(receiver, Mapping) else {}
    dsp = dsp if isinstance(dsp, Mapping) else {}
    timestamp = _finite(receiver.get("last_valid_monotonic"))
    age = None if timestamp is None else now - timestamp
    fresh = age is not None and 0 <= age <= stale_after
    if "data_received_at_monotonic" in dsp:
        data_timestamp = _finite(dsp.get("data_received_at_monotonic"))
        data_age = None if data_timestamp is None else now - data_timestamp
        fresh = fresh and data_age is not None and 0 <= data_age <= stale_after
    healthy = (
        receiver.get("state") == "receiving"
        and fresh
        and (_finite(receiver.get("packets_received")) or 0) > 0
        and receiver.get("last_error") is None
        and dsp.get("valid") is True
    )
    if not snapshot:
        status = "Desconectado · sin adquisición"
    elif not fresh and timestamp is not None:
        status = "Datos obsoletos · evidencia suspendida"
    elif healthy:
        status = "Adquisición fresca y validada"
    else:
        status = "Adquisición no disponible o inválida · evidencia suspendida"
    source_kind = snapshot.get("source_kind", "unknown")
    sources = {
        "synthetic": "Fuente SINTÉTICA declarada · hardware no confirmado",
        "calibrated": (
            "Fuente con calibración declarada por el operador · "
            "hardware no confirmado"
        ),
        "unknown": "Fuente DESCONOCIDA · hardware no confirmado",
    }
    source = sources.get(source_kind, sources["unknown"])
    reference_label = dsp.get("reference_model_label")
    calibration_label = dsp.get("calibration_label")
    if (
        healthy and isinstance(reference_label, str) and reference_label.strip()
        and isinstance(calibration_label, str) and calibration_label.strip()
    ):
        source += (
            f" · Referencia externa declarada, no ajustada: {reference_label}. "
            f"Calibración: {calibration_label}; declaración no verificada."
        )
    metrics = {
        "Modulación de fase (Hz)": None,
        "Resolución espectral (Hz)": None,
        "κ (unidades de referencia declaradas)": None,
        "Error estándar κ (OLS descriptivo)": None,
        "Concentración residual de ajuste OLS (no fidelidad cuántica)": None,
        "ln BF₁₀ (modelo condicional)": None,
    }
    evidence_label = "Modelo condicional no disponible"
    figure = _empty_spectrum("Sin ventana de fase válida de al menos 1 s")
    if healthy:
        metrics["Modulación de fase (Hz)"] = _finite(dsp.get("modulation_hz"))
        metrics["Resolución espectral (Hz)"] = _finite(dsp.get("resolution_hz"))
        metrics["κ (unidades de referencia declaradas)"] = _finite(dsp.get("kappa"))
        metrics["Error estándar κ (OLS descriptivo)"] = _finite(dsp.get("kappa_se"))
        metrics[
            "Concentración residual de ajuste OLS (no fidelidad cuántica)"
        ] = _finite(dsp.get("phase_concentration"))
        duration = _finite(dsp.get("duration_s"))
        try:
            frequency = np.asarray(dsp.get("frequency_hz", []), dtype=float)
            psd = np.asarray(dsp.get("phase_psd_rad2_hz", []), dtype=float)
            usable_spectrum = (
                duration is not None and duration >= 1.0
                and frequency.ndim == psd.ndim == 1
                and frequency.size > 1 and frequency.shape == psd.shape
                and np.all(np.isfinite(frequency)) and np.all(np.isfinite(psd))
                and np.all(np.diff(frequency) > 0) and np.all(psd >= 0)
            )
        except (ValueError, TypeError):
            usable_spectrum = False
        if usable_spectrum:
            figure = _empty_spectrum(
                f"PSD de fase demodulada · ventana {duration:.3f} s"
            )
            figure.add_trace(go.Scatter(x=frequency, y=psd, mode="lines"))
            figure.update_xaxes(range=[0, 500])
        ln_bf = _finite(dsp.get("ln_bayes_factor"))
        noise = _finite(dsp.get("noise_sigma_rad"))
        calibration = dsp.get("calibration_label")
        model_label = dsp.get("evidence_model_label")
        assumptions = (
            noise is not None and noise > 0
            and isinstance(calibration, str) and bool(calibration.strip())
            and dsp.get("independent_samples_assumed") is True
            and dsp.get("evidence_valid") is True
            and isinstance(model_label, str) and bool(model_label.strip())
            and duration is not None and duration >= 1.0
        )
        if assumptions and ln_bf is not None:
            metrics["ln BF₁₀ (modelo condicional)"] = ln_bf
            preference = (
                "favorece H₁" if ln_bf > 0 else "favorece H₀" if ln_bf < 0
                else "no distingue H₁/H₀"
            )
            evidence_label = (
                f"Modelo condicional: ln BF₁₀ = {ln_bf:.6g}; {preference}. "
                f"{model_label}. "
                f"Calibración declarada: {calibration}; σ = {noise:.6g} rad; "
                "errores gaussianos independientes asumidos, no verificados. "
                "No es confirmación física ni prueba QCAL."
            )
    return {
        "healthy": healthy,
        "status": status,
        "source": source,
        "metrics": metrics,
        "evidence_label": evidence_label,
        "figure": figure,
    }


def create_app(
    snapshot_provider: SnapshotProvider | None = None,
    *,
    stale_after: float = 2.0,
    clock: Callable[[], float] = time.monotonic,
) -> Dash:
    """Create a passive dashboard; acquisition must be started by its owner.

    Args:
        snapshot_provider: Thread-safe callable returning the receiver snapshot.
            None leaves all measured quantities unavailable.
        stale_after: Maximum permitted age in seconds for validated telemetry.
        clock: Monotonic clock matching the receiver's reception timestamps.

    Returns:
        Dash application with a freshness-sensitive ``/health`` endpoint.

    Raises:
        ValueError: If stale_after is not finite and strictly positive.
    """
    if _finite(stale_after) is None or stale_after <= 0:
        raise ValueError("stale_after must be finite and positive")

    app = Dash(__name__)
    app.layout = html.Main(
        [
            html.H1("QCAL-EXP01 · Telemetría experimental"),
            html.P(
                "Los datos sintéticos y el modelo estadístico condicional no "
                "demuestran una señal física. Hardware no confirmado."
            ),
            html.P(
                "Análisis espectral limitado a 1 Hz; adquisición best-effort, "
                "sin garantía de caudal."
            ),
            html.Div(id="acquisition-status"),
            html.Div(id="source-status"),
            html.Div(id="measurement-summary"),
            html.Div(id="evidence-status"),
            dcc.Graph(id="phase-spectrum", figure=_empty_spectrum("Sin datos")),
            dcc.Interval(id="refresh", interval=500, n_intervals=0),
        ]
    )

    @app.server.get("/health")
    def health() -> tuple[dict[str, Any], int]:
        """Return 503 unless acquisition contains fresh validated measurements."""
        state = display_state(
            _read_snapshot(snapshot_provider), stale_after=stale_after, now=clock()
        )
        return (
            {
                "status": state["status"],
                "healthy": state["healthy"],
                "source": state["source"],
                "hardware_confirmed": False,
            },
            200 if state["healthy"] else 503,
        )

    @app.callback(
        Output("acquisition-status", "children"),
        Output("source-status", "children"),
        Output("measurement-summary", "children"),
        Output("evidence-status", "children"),
        Output("phase-spectrum", "figure"),
        Input("refresh", "n_intervals"),
    )
    def refresh(_: int) -> tuple[str, str, str, str, go.Figure]:
        """Refresh only from actual acquisition; offline values remain absent."""
        state = display_state(
            _read_snapshot(snapshot_provider), stale_after=stale_after, now=clock()
        )
        metrics = state["metrics"]
        summary = " · ".join(
            f"{label}: {'N/D' if value is None else format(value, '.6g')}"
            for label, value in metrics.items()
        )
        return (
            state["status"],
            state["source"],
            summary,
            state["evidence_label"],
            state["figure"],
        )

    return app


@dataclass(frozen=True)
class _ReferenceModel:
    """Operator-declared sinusoidal calibration and conditional point models.

    amplitude is in reference_units; frequency_hz is in Hz and phase_rad is
    the phase at sample-clock zero. None of these parameters are fitted to the
    acquired phase. Physical use requires independent calibration of x0 and
    the chosen FIR transfer response. A matching synthetic injection describes
    known generation parameters, not independent physical evidence.
    """

    amplitude: float
    frequency_hz: float
    phase_rad: float
    calibration_label: str
    reference_units: str = "unidades declaradas"
    noise_sigma_rad: float | None = None
    independent_samples_assumed: bool = False
    known_drift_rad_s: float | None = None
    slope_h1: float = 13.4034
    slope_h0: float = 13.3
    intercept_prior_mean: float = 0.0
    intercept_prior_sd: float = 1.0

    def __post_init__(self) -> None:
        """Reject incomplete calibration and nonfinite conditional parameters."""
        values = (
            self.amplitude, self.frequency_hz, self.phase_rad, self.slope_h1,
            self.slope_h0, self.intercept_prior_mean, self.intercept_prior_sd,
        )
        if any(_finite(value) is None for value in values):
            raise ValueError("reference/model parameters must be finite")
        if self.amplitude <= 0 or self.frequency_hz <= 0:
            raise ValueError("reference amplitude and frequency must be positive")
        if (
            not self.calibration_label.strip() or not self.reference_units.strip()
            or self.intercept_prior_sd < 0
        ):
            raise ValueError("provide a calibration label and nonnegative prior SD")
        if self.noise_sigma_rad is not None and (
            _finite(self.noise_sigma_rad) is None or self.noise_sigma_rad <= 0
        ):
            raise ValueError("known noise sigma must be positive and finite")
        if self.known_drift_rad_s is not None and _finite(self.known_drift_rad_s) is None:
            raise ValueError("known drift must be finite")


class _Acquisition:
    """Bounded paired-IF phase history, created only by the explicit CLI.

    The wire channels are reference IF (A) and signal IF (B), not calibrated
    displacement. A reference waveform must therefore be independently supplied
    before coupling regression or conditional evidence can be computed.
    """

    def __init__(
        self, config: Any, *, window_seconds: float = 2.0,
        reference_model: _ReferenceModel | None = None,
        clock: Callable[[], float] = time.monotonic,
    ) -> None:
        """Allocate demodulators and a bounded contiguous phase history."""
        from .dsp import StreamingDemodulator

        if _finite(window_seconds) is None or window_seconds < 1.0:
            raise ValueError("phase history must cover at least one finite second")
        if (
            reference_model is not None
            and reference_model.frequency_hz >= config.cutoff_hz
        ):
            raise ValueError("calibrated reference must lie inside the demodulation band")
        self.config = config
        self.reference_model = reference_model
        self._clock = clock
        self._a = StreamingDemodulator(config)
        self._b = StreamingDemodulator(config)
        self._lock = threading.Lock()
        self._analysis_lock = threading.Lock()
        self._blocks: deque[tuple[np.ndarray, np.ndarray]] = deque()
        self._pending: list[Any] = []
        self._pending_count = 0
        self._count = 0
        self._maximum = int(math.ceil(config.fs * window_seconds))
        self._valid = False
        self._generation = 0
        self._cached_snapshot: dict[str, Any] | None = None
        self._cached_at: float | None = None
        self._latest_input_monotonic: float | None = None

    def _invalidate_analysis(self) -> None:
        """Invalidate derived results immediately; caller holds the history lock."""
        self._generation += 1
        self._cached_snapshot = None
        self._cached_at = None

    def reset(self, first_sample_index: int) -> None:
        """Discard phase/filter continuity after a missing or reordered interval."""
        with self._lock:
            self._a.reset(first_sample_index)
            self._b.reset(first_sample_index)
            self._blocks.clear()
            self._pending.clear()
            self._pending_count = 0
            self._count = 0
            self._valid = False
            self._latest_input_monotonic = None
            self._invalidate_analysis()

    def accept(self, packet: Any) -> None:
        """Demodulate real ADC-count channels using their absolute sample clock."""
        if packet.sample_rate != self.config.fs:
            raise ValueError("packet sample rate differs from configured DSP rate")
        with self._lock:
            self._pending.append(packet)
            self._pending_count += packet.channel_a.size
            self._latest_input_monotonic = self._clock()
            # Amortize FIR/unwrap allocation over bounded batches, not UDP frames.
            if self._pending_count >= 16_384:
                self._process_pending()

    def _process_pending(self) -> None:
        """Process buffered ordered frames; caller holds the acquisition lock."""
        if not self._pending:
            return
        first_sample_index = self._pending[0].first_sample_index
        raw_a = np.concatenate([packet.channel_a for packet in self._pending])
        raw_b = np.concatenate([packet.channel_b for packet in self._pending])
        self._pending.clear()
        self._pending_count = 0
        a = self._a.process(raw_a.astype(float) / 32768.0, start_index=first_sample_index)
        b = self._b.process(raw_b.astype(float) / 32768.0, start_index=first_sample_index)
        valid = a.valid & b.valid
        invalid = np.flatnonzero(~valid)
        start = int(invalid[-1] + 1) if invalid.size else 0
        if invalid.size:
            self._blocks.clear()
            self._count = 0
            self._invalidate_analysis()
        self._valid = bool(start < valid.size)
        if not self._valid:
            return
        times = b.time_s[start:].copy()
        phase = (b.phase_rad[start:] - a.phase_rad[start:]).copy()
        self._blocks.append((times, phase))
        self._count += times.size
        while self._count > self._maximum:
            excess = self._count - self._maximum
            first_times, first_phase = self._blocks.popleft()
            remove = min(excess, first_times.size)
            self._count -= remove
            if remove < first_times.size:
                self._blocks.appendleft((first_times[remove:], first_phase[remove:]))

    def snapshot(self) -> dict[str, Any]:
        """Publish cached analysis at most once per second, without decimation.

        PSD uses a Hann periodogram without zero padding; frequency spacing is
        fs/N in Hz and power density has units rad²/Hz. No carrier FFT or dBm
        conversion is implied. Regression/evidence remain absent without an
        independent reference calibration and noise model. Gaps and invalid phase
        invalidate cached results immediately. Reception time belongs to the
        analyzed samples, not newer packets arriving after the analysis.
        """
        with self._analysis_lock:
            with self._lock:
                self._process_pending()
                result = {
                    "valid": self._valid,
                    "duration_s": self._count / self.config.fs,
                    "data_received_at_monotonic": self._latest_input_monotonic,
                }
                if not self._valid or self._count / self.config.fs < 1.0:
                    return result
                now = self._clock()
                if (
                    self._cached_snapshot is not None
                    and self._cached_at is not None
                    and 0 <= now - self._cached_at < 1.0
                ):
                    return dict(self._cached_snapshot)
                blocks = tuple(self._blocks)
                generation = self._generation
            self._analyze_history(result, blocks)
            with self._lock:
                if generation != self._generation or not self._valid:
                    return {"valid": False, "duration_s": 0.0}
                self._cached_snapshot = result
                self._cached_at = now
            return dict(result)

    def _analyze_history(
        self, result: dict[str, Any],
        blocks: tuple[tuple[np.ndarray, np.ndarray], ...],
    ) -> None:
        """Analyze one fixed contiguous history outside the receiver's lock."""
        times = np.concatenate([block[0] for block in blocks])
        phase = np.concatenate([block[1] for block in blocks])
        result["resolution_hz"] = self.config.fs / phase.size
        centered_time = times - times[0]
        centered_time -= np.mean(centered_time)
        centered_phase = phase - np.mean(phase)
        slope = np.sum(centered_time * centered_phase) / np.sum(centered_time**2)
        residual = centered_phase - slope * centered_time
        frequency, psd = signal.periodogram(
            residual, fs=self.config.fs, window="hann", scaling="density",
            detrend=False,
        )
        selected = frequency <= 500.0
        result["frequency_hz"] = frequency[selected]
        result["phase_psd_rad2_hz"] = psd[selected]
        band = (frequency >= 50.0) & (frequency <= 500.0)
        result["modulation_hz"] = float(frequency[band][np.argmax(psd[band])])
        if self.reference_model is not None:
            self._add_calibrated_model(result, times, phase)

    def _add_calibrated_model(
        self, result: dict[str, Any], times: np.ndarray, phase: np.ndarray
    ) -> None:
        """Evaluate a declared reference; fitted nuisance drift is never BF input."""
        from .dsp import fit_phase_regression, phase_concentration
        from .statistics import gaussian_log_bayes_factor

        model = self.reference_model
        if model is None:
            return
        x0 = model.amplitude * np.sin(
            2 * np.pi * model.frequency_hz * times + model.phase_rad
        )
        fit = fit_phase_regression(
            times, phase, x0, noise_sigma=model.noise_sigma_rad
        )
        result["calibration_label"] = model.calibration_label
        result["reference_model_label"] = (
            f"x₀(t)={model.amplitude:.12g} sin(2π·{model.frequency_hz:.12g}·t"
            f"+{model.phase_rad:.12g}) {model.reference_units}; "
            "t sigue el reloj de muestras con retardo FIR"
        )
        result["kappa"] = fit.kappa
        result["kappa_se"] = fit.kappa_standard_error
        if fit.status != "ok":
            return
        fitted_phase = fit.intercept + fit.drift_rad_s * times + fit.kappa * x0
        result["phase_concentration"] = phase_concentration(
            phase, fitted_phase, model_label="in-sample OLS intercept+drift+κx0"
        ).concentration
        if (
            model.noise_sigma_rad is None
            or not model.independent_samples_assumed
            or model.known_drift_rad_s is None
        ):
            return
        result["ln_bayes_factor"] = gaussian_log_bayes_factor(
            x0, phase - model.known_drift_rad_s * times, model.noise_sigma_rad,
            slope_h1=model.slope_h1, slope_h0=model.slope_h0,
            intercept_prior_mean=model.intercept_prior_mean,
            intercept_prior_sd=model.intercept_prior_sd,
        )
        result["noise_sigma_rad"] = model.noise_sigma_rad
        result["independent_samples_assumed"] = True
        result["evidence_valid"] = True
        result["evidence_model_label"] = (
            f"H₁: κ={model.slope_h1:g}; H₀: κ={model.slope_h0:g}; "
            f"prior común b~N({model.intercept_prior_mean:g}, "
            f"{model.intercept_prior_sd:g}²); "
            f"deriva conocida declarada={model.known_drift_rad_s:g} rad/s"
        )


def main(argv: list[str] | None = None) -> int:
    """Explicitly start UDP acquisition and the Dash server, then stop on exit."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8050)
    parser.add_argument("--udp-host", default="127.0.0.1")
    parser.add_argument("--udp-port", type=int, default=5005)
    parser.add_argument("--allow-lan", action="store_true")
    parser.add_argument(
        "--expected-sender", "--expected-source", dest="expected_source",
        default=os.environ.get(
            "QCAL_EXPECTED_SENDER", os.environ.get("QCAL_EXPECTED_SOURCE")
        ),
        help=(
            "Expected sender IP or hostname; required with --allow-lan. "
            "Defaults to QCAL_EXPECTED_SENDER (QCAL_EXPECTED_SOURCE also supported)"
        ),
    )
    parser.add_argument(
        "--source-kind", choices=("unknown", "synthetic", "calibrated"),
        default=os.environ.get("QCAL_SOURCE_KIND", "unknown"),
        help="Operator-declared provenance (or QCAL_SOURCE_KIND), not authentication",
    )
    parser.add_argument(
        "--sample-rate", type=int, choices=(100_000, 1_000_000), default=1_000_000
    )
    parser.add_argument("--carrier-hz", type=float, default=100_000.0)
    parser.add_argument("--cutoff-hz", type=float, default=5_000.0)
    parser.add_argument("--min-amplitude", type=float, default=0.05)
    parser.add_argument("--stale-after", type=float, default=2.0)
    parser.add_argument("--reference-amplitude", type=float)
    parser.add_argument("--reference-frequency-hz", type=float)
    parser.add_argument("--reference-phase-rad", type=float, default=0.0)
    parser.add_argument("--calibration-label")
    parser.add_argument("--reference-units", default="unidades declaradas")
    parser.add_argument("--noise-sigma-rad", type=float)
    parser.add_argument("--assume-independent-samples", action="store_true")
    parser.add_argument("--known-drift-rad-s", type=float)
    parser.add_argument("--slope-h1", type=float, default=13.4034)
    parser.add_argument("--slope-h0", type=float, default=13.3)
    parser.add_argument("--intercept-prior-mean", type=float, default=0.0)
    parser.add_argument("--intercept-prior-sd", type=float, default=1.0)
    args = parser.parse_args(argv)
    if args.source_kind not in ("unknown", "synthetic", "calibrated"):
        parser.error("QCAL_SOURCE_KIND must be unknown, synthetic, or calibrated")

    # Imports and acquisition are intentionally confined to the explicit entrypoint.
    from .dsp import DSPConfig
    from .receiver import UDPReceiver

    try:
        config = DSPConfig(
            fs=args.sample_rate, fc=args.carrier_hz,
            cutoff_hz=args.cutoff_hz, min_amplitude=args.min_amplitude,
        )
        reference = None
        reference_settings = (
            args.reference_amplitude, args.reference_frequency_hz,
            args.calibration_label,
        )
        if any(value is not None for value in reference_settings):
            if not all(value is not None for value in reference_settings):
                raise ValueError(
                    "reference amplitude, frequency and calibration label "
                    "must be provided together"
                )
            reference = _ReferenceModel(
                amplitude=args.reference_amplitude,
                frequency_hz=args.reference_frequency_hz,
                phase_rad=args.reference_phase_rad,
                calibration_label=args.calibration_label,
                reference_units=args.reference_units,
                noise_sigma_rad=args.noise_sigma_rad,
                independent_samples_assumed=args.assume_independent_samples,
                known_drift_rad_s=args.known_drift_rad_s,
                slope_h1=args.slope_h1, slope_h0=args.slope_h0,
                intercept_prior_mean=args.intercept_prior_mean,
                intercept_prior_sd=args.intercept_prior_sd,
            )
        acquisition = _Acquisition(config, reference_model=reference)
        receiver = UDPReceiver(
            on_packet=acquisition.accept, on_gap=acquisition.reset,
            host=args.udp_host, port=args.udp_port,
            expected_sender=args.expected_source, allow_lan=args.allow_lan,
            freshness_seconds=args.stale_after,
        )
    except (ValueError, OSError) as exc:
        parser.error(str(exc))

    def current_snapshot() -> dict[str, Any]:
        """Combine receiver freshness with the actual bounded DSP history."""
        return {
            "receiver": asdict(receiver.snapshot()),
            "dsp": acquisition.snapshot(),
            "source_kind": args.source_kind,
        }

    app = create_app(current_snapshot, stale_after=args.stale_after)
    if not receiver.start():
        parser.exit(1, f"UDP acquisition failed: {receiver.snapshot().last_error}\n")
    try:
        app.run(host=args.host, port=args.port, debug=False, use_reloader=False)
    finally:
        receiver.stop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
