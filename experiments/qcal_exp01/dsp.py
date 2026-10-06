"""Calibrated phase analysis of real sampled IF signals.

The quadrature convention is I = LPF(2 s cos(ωt)), Q = LPF(-2 s sin(ωt)).
Thus a cosine with positive phase modulation has positive demodulated phase.
Unwrapping assumes adjacent valid phase increments are less than π; no
algorithm can recover cycle slips from missing or undersampled observations.
"""

from dataclasses import dataclass
from typing import Optional, Protocol

import numpy as np
from numpy.typing import ArrayLike, NDArray
from scipy import signal

FloatArray = NDArray[np.float64]


class SamplePacket(Protocol):
    """Structural packet interface; transport implementation remains independent."""

    first_sample_index: int
    sample_rate: float
    channel_a: NDArray[np.int16]
    channel_b: NDArray[np.int16]


def _vector(values: ArrayLike, name: str) -> FloatArray:
    """Return a finite real one-dimensional vector, rejecting invalid input."""
    raw = np.asarray(values)
    if raw.ndim != 1 or np.iscomplexobj(raw):
        raise ValueError(f"{name} must be a real one-dimensional vector")
    out = np.asarray(raw, dtype=float)
    if not np.all(np.isfinite(out)):
        raise ValueError(f"{name} must contain only finite values")
    return out


def _unwrap_runs(
    baseband: NDArray[np.complex128], valid: NDArray[np.bool_],
    last_phase: Optional[float], segment: int,
) -> tuple[FloatArray, NDArray[np.int64], Optional[float], int]:
    """Unwrap contiguous valid runs, preserving only identifiable cycle counts."""
    phase = np.full(valid.size, np.nan)
    segments = np.full(valid.size, -1, dtype=np.int64)
    edges = np.diff(np.r_[False, valid, False].astype(int))
    starts, stops = np.flatnonzero(edges == 1), np.flatnonzero(edges == -1)
    for first, stop in zip(starts, stops):
        values = np.unwrap(np.angle(baseband[first:stop]))
        if first == 0 and last_phase is not None:
            values += 2 * np.pi * np.round((last_phase - values[0]) / (2 * np.pi))
        else:
            segment += 1
        phase[first:stop] = values
        segments[first:stop] = segment
    if valid.size:
        last_phase = float(phase[-1]) if valid[-1] else None
    return phase, segments, last_phase, segment


@dataclass(frozen=True)
class DSPConfig:
    """IF acquisition settings; frequencies are Hz and amplitude is input units.

    The odd linear-phase FIR introduces (num_taps - 1)/2 samples of delay.
    The first num_taps - 1 samples after each reset are conservatively masked.
    min_amplitude must be an independently selected detection threshold, not a
    purported quantum fidelity. The low-pass cutoff must fit between the IF
    and both edges of the real-signal Nyquist band.
    """

    fs: float = 1_000_000.0
    fc: float = 100_000.0
    num_taps: int = 101
    cutoff_hz: float = 5_000.0
    min_amplitude: float = 0.05

    def __post_init__(self) -> None:
        """Reject aliased carriers, nonfinite settings, and invalid FIR sizes."""
        if not all(np.isfinite(v) for v in
                   (self.fs, self.fc, self.cutoff_hz, self.min_amplitude)):
            raise ValueError("DSP settings must be finite")
        if self.fs <= 0 or not 0 < self.fc < self.fs / 2:
            raise ValueError("real IF must satisfy 0 < fc < fs/2 (Nyquist)")
        if not 0 < self.cutoff_hz < min(self.fc, self.fs / 2 - self.fc):
            raise ValueError("cutoff must fit inside the available IF band")
        if (isinstance(self.num_taps, bool) or
                not isinstance(self.num_taps, (int, np.integer)) or
                self.num_taps < 3 or self.num_taps % 2 != 1):
            raise ValueError("num_taps must be an odd integer >= 3")
        if self.min_amplitude <= 0:
            raise ValueError("min_amplitude must be positive")


@dataclass(frozen=True)
class DemodulatedBlock:
    """Streaming result with explicit masks and delay-aligned reference.

    time_s refers to the FIR output's physical time (input time minus delay).
    phase_rad is NaN where invalid. phase_segment identifies contiguous valid
    observations: separate segments have unknown relative integer-2π offsets.
    reference is None if no calibrated x0 was supplied; it is a pure delay,
    not a filtered reference. Filter attenuation/distortion must be calibrated
    for the chosen modulation band before interpreting a fitted coefficient.
    """

    sample_index: NDArray[np.int64]
    time_s: FloatArray
    baseband: NDArray[np.complex128]
    amplitude: FloatArray
    phase_rad: FloatArray
    valid: NDArray[np.bool_]
    phase_segment: NDArray[np.int64]
    reference: Optional[FloatArray]
    status: str
    reset_occurred: bool


class StreamingDemodulator:
    """Zero-state FIR demodulator that preserves oscillator and phase continuity."""

    def __init__(self, config: Optional[DSPConfig] = None) -> None:
        """Construct a demodulator; default fs=1 MHz and IF=100 kHz."""
        self.config = config or DSPConfig()
        self.taps = signal.firwin(
            self.config.num_taps, self.config.cutoff_hz, fs=self.config.fs
        )
        self.delay_samples = (self.config.num_taps - 1) // 2
        self.reset()

    def reset(self, start_index: int = 0) -> None:
        """Reset FIR, reference history and unwrap state after a discontinuity."""
        if isinstance(start_index, bool) or not isinstance(start_index, (int, np.integer)):
            raise ValueError("start_index must be an integer")
        if start_index < 0:
            raise ValueError("start_index must be nonnegative")
        self._next_index = int(start_index)
        self._elapsed = 0
        self._zi = np.zeros(self.config.num_taps - 1, dtype=complex)
        self._reference_history = np.full(self.delay_samples, np.nan)
        self._last_phase: Optional[float] = None
        self._segment = -1

    def process_packet(
        self, packet: SamplePacket, *, signal_units_per_count: float = 1.0,
        reference_units_per_count: Optional[float] = None,
    ) -> DemodulatedBlock:
        """Adapt a transport packet without silently assuming reference calibration.

        Channel A is the real sampled IF. Channel B is used as calibrated x0
        only when reference_units_per_count is supplied explicitly; otherwise
        the output reference is unavailable. Signed nonzero conversion factors
        specify the independently measured channel polarity and physical units.
        Packet sample rate must match the configured fs. Connect transport's
        on_gap to reset and on_packet to this method (or a calibrated wrapper).
        This alternate one-IF-plus-x0 adapter is NOT the bundled native
        simulator's two-IF mapping; use DualChannelDemodulator for that source.

        Args:
            packet: Structural packet carrying acquisition indices/rate/channels.
            signal_units_per_count: Channel A amplitude conversion from counts.
            reference_units_per_count: Optional calibrated B-to-x0 conversion.

        Returns:
            Delay-aligned, masked demodulation results for this packet.

        Raises:
            ValueError: A sample-rate mismatch or invalid calibration factor.
        """
        if (not np.isfinite(packet.sample_rate)
                or not np.isclose(packet.sample_rate, self.config.fs, rtol=1e-12, atol=0)):
            self.reset(self._next_index)
            raise ValueError("packet sample_rate must match configured fs")
        gains = [signal_units_per_count]
        if reference_units_per_count is not None:
            gains.append(reference_units_per_count)
        if any(not np.isfinite(gain) or gain == 0 for gain in gains):
            raise ValueError("calibration factors must be finite and nonzero")
        samples = _vector(packet.channel_a, "channel_a") * signal_units_per_count
        reference = (None if reference_units_per_count is None else
                     _vector(packet.channel_b, "channel_b") * reference_units_per_count)
        return self.process(samples, reference, start_index=packet.first_sample_index)

    def process(
        self, samples: ArrayLike, reference: Optional[ArrayLike] = None,
        start_index: Optional[int] = None, healthy: bool = True,
    ) -> DemodulatedBlock:
        """Demodulate a block, retaining absolute sample index across calls.

        Args:
            samples: Finite real IF samples, including an empty block if needed.
            reference: Simultaneous calibrated x0 samples in declared units.
            start_index: Absolute first sample index; a gap/overlap resets state.
            healthy: False masks this block and discards all phase/filter state.

        Returns:
            A typed block. Empty/settling/low-amplitude/failure blocks are marked.

        Raises:
            ValueError: Invalid samples, reference, or acquisition indices.
        """
        try:
            raw = _vector(samples, "samples")
            ref = None if reference is None else _vector(reference, "reference")
            if ref is not None and ref.shape != raw.shape:
                raise ValueError("reference must match samples")
        except (ValueError, TypeError):
            self.reset(self._next_index)
            raise
        index = self._next_index if start_index is None else start_index
        if (isinstance(index, bool) or not isinstance(index, (int, np.integer))
                or index < 0):
            raise ValueError("start_index must be a nonnegative integer")
        restarted = index != self._next_index or not healthy
        if restarted:
            self.reset(int(index))
        n = raw.size
        indices = np.arange(index, index + n, dtype=np.int64)
        times = (indices - self.delay_samples) / self.config.fs
        aligned = None
        if ref is not None:
            combined = np.concatenate((self._reference_history, ref))
            aligned = combined[:n].copy()
            self._reference_history = combined[n:].copy()
        elif n:
            combined = np.concatenate((self._reference_history, np.full(n, np.nan)))
            self._reference_history = combined[n:].copy()
        if n and healthy:
            angle = 2 * np.pi * self.config.fc * indices / self.config.fs
            mixed = 2 * raw * (np.cos(angle) - 1j * np.sin(angle))
            baseband, self._zi = signal.lfilter(self.taps, [1.0], mixed, zi=self._zi)
        else:
            baseband = np.full(n, np.nan + 1j * np.nan, dtype=complex)
        amplitude = np.abs(baseband)
        valid = (np.arange(n) + self._elapsed >= self.config.num_taps - 1)
        valid &= np.isfinite(amplitude) & (amplitude >= self.config.min_amplitude)
        phase, segments, self._last_phase, self._segment = _unwrap_runs(
            baseband, valid, self._last_phase, self._segment
        )
        self._next_index = int(index + n)
        self._elapsed += n
        if not healthy:
            self.reset(self._next_index)
        status = ("failure" if not healthy else "empty" if not n else
                  "ok" if np.any(valid) else
                  "settling" if self._elapsed < self.config.num_taps else
                  "low_amplitude")
        return DemodulatedBlock(indices, times, baseband, amplitude, phase,
                                valid, segments, aligned, status, restarted)


class DualChannelDemodulator:
    """Demodulate two real IF channels and unwrap differential phase B minus A.

    Both channels are sampled synchronously at the same configured IF. Neither
    channel's ADC counts are a displacement reference. To estimate coupling,
    provide a separate, independently calibrated x0 vector in declared units.
    The returned block has the same fields as single-channel demodulation;
    its amplitude is min(|A|, |B|), and its baseband has that magnitude and
    the differential phase. Low amplitude in either channel invalidates phase.
    """

    def __init__(self, config: Optional[DSPConfig] = None) -> None:
        """Construct independent zero-state FIR channels and differential unwrap."""
        self.config = config or DSPConfig()
        self._channel_a = StreamingDemodulator(self.config)
        self._channel_b = StreamingDemodulator(self.config)
        self._last_phase: Optional[float] = None
        self._segment = -1

    def reset(self, start_index: int = 0) -> None:
        """Discard both channel histories and differential phase on packet gaps."""
        self._channel_a.reset(start_index)
        self._channel_b.reset(start_index)
        self._last_phase = None
        self._segment = -1

    def process(
        self, channel_a: ArrayLike, channel_b: ArrayLike,
        reference: Optional[ArrayLike] = None, start_index: Optional[int] = None,
        healthy: bool = True,
    ) -> DemodulatedBlock:
        """Return masked differential phase with an optional external x0 reference.

        Args:
            channel_a: Real baseline/reference-carrier IF samples.
            channel_b: Synchronous real signal-carrier IF samples.
            reference: Independently calibrated displacement x0, not channel A/B.
            start_index: Absolute first acquisition index.
            healthy: False masks and resets both channels.

        Returns:
            Differential phase B-A; calibrated reference is FIR-delay aligned.
        """
        try:
            a, b = _vector(channel_a, "channel_a"), _vector(channel_b, "channel_b")
            ref = None if reference is None else _vector(reference, "reference")
            if a.shape != b.shape or (ref is not None and ref.shape != a.shape):
                raise ValueError("channels and external reference must match")
        except (ValueError, TypeError):
            self.reset(self._channel_a._next_index)
            raise
        block_a = self._channel_a.process(a, ref, start_index, healthy)
        block_b = self._channel_b.process(b, None, start_index, healthy)
        restarted = block_a.reset_occurred or block_b.reset_occurred
        if restarted:
            self._last_phase = None
            self._segment = -1
        maximum = np.maximum(block_a.amplitude, block_b.amplitude)
        differential = np.divide(
            block_b.baseband * np.conjugate(block_a.baseband), maximum,
            out=np.zeros(a.size, dtype=complex), where=maximum > 0,
        )
        valid = block_a.valid & block_b.valid
        phase, segments, self._last_phase, self._segment = _unwrap_runs(
            differential, valid, self._last_phase, self._segment
        )
        amplitude = np.minimum(block_a.amplitude, block_b.amplitude)
        status = ("failure" if not healthy else "empty" if not a.size else
                  "ok" if np.any(valid) else
                  "settling" if "settling" in (block_a.status, block_b.status) else
                  "low_amplitude")
        return DemodulatedBlock(
            block_a.sample_index, block_a.time_s, differential, amplitude,
            phase, valid, segments, block_a.reference, status, restarted,
        )

    def process_packet(
        self, packet: SamplePacket, *, signal_units_per_count: float = 1.0,
        reference: Optional[ArrayLike] = None,
    ) -> DemodulatedBlock:
        """Adapt a two-IF packet with explicit count scaling and external x0.

        Unlike StreamingDemodulator.process_packet, BOTH ADC channels here
        are IF waveforms. reference, if supplied, is already calibrated and
        must correspond to these packet indices. No physical units are
        inferred from the native synthetic generator's --x0 parameter.
        """
        if (not np.isfinite(packet.sample_rate)
                or not np.isclose(packet.sample_rate, self.config.fs, rtol=1e-12, atol=0)):
            self.reset(self._channel_a._next_index)
            raise ValueError("packet sample_rate must match configured fs")
        if not np.isfinite(signal_units_per_count) or signal_units_per_count == 0:
            raise ValueError("signal calibration must be finite and nonzero")
        return self.process(
            _vector(packet.channel_a, "channel_a") * signal_units_per_count,
            _vector(packet.channel_b, "channel_b") * signal_units_per_count,
            reference, packet.first_sample_index,
        )


@dataclass(frozen=True)
class FrequencyEstimate:
    """Spectral phase-modulation peak; resolution_hz is 1/observed duration.

    This is not a sub-bin precision claim or mean instantaneous carrier drift.
    A nonavailable estimate has frequency_hz=None with an explanatory status.
    """

    frequency_hz: Optional[float]
    resolution_hz: Optional[float]
    duration_s: float
    status: str


def estimate_modulation_frequency(
    time_s: ArrayLike, phase_rad: ArrayLike, *,
    frequency_band_hz: tuple[float, float] = (50.0, 500.0),
    min_observation_s: float = 0.1, min_cycles: float = 5.0,
) -> FrequencyEstimate:
    """Estimate the dominant modulation of uniformly sampled unwrapped phase.

    A linear phase trend is removed before a Hann-windowed periodogram.
    At least min_observation_s and min_cycles at the band's lower edge are
    required. No zero-padding or interpolation fabricates frequency precision.
    Supply one contiguous valid unwrap segment; do not bridge masked gaps.
    """
    t, phase = _vector(time_s, "time_s"), _vector(phase_rad, "phase_rad")
    if t.shape != phase.shape:
        raise ValueError("time and phase must match")
    low, high = frequency_band_hz
    if (not all(np.isfinite(v) for v in (low, high, min_observation_s, min_cycles))
            or not 0 < low < high or min_observation_s <= 0 or min_cycles <= 0):
        raise ValueError("invalid frequency band or observation requirement")
    if t.size < 4:
        return FrequencyEstimate(None, None, 0.0, "insufficient_data")
    dt = np.diff(t)
    if np.any(dt <= 0) or not np.allclose(dt, dt[0], rtol=1e-6, atol=1e-12):
        raise ValueError("time must be increasing and uniformly sampled")
    if high >= 0.5 / dt[0]:
        raise ValueError("frequency band must lie below Nyquist")
    duration = float(t[-1] - t[0])
    resolution = 1 / duration
    if duration < max(min_observation_s, min_cycles / low):
        return FrequencyEstimate(None, resolution, duration, "insufficient_duration")
    residual = signal.detrend(phase, type="linear")
    scale = max(1.0, float(np.max(np.abs(phase))))
    if np.std(residual) <= 1e-10 * scale:
        return FrequencyEstimate(None, resolution, duration, "no_modulation")
    freq, power = signal.periodogram(residual, fs=1 / dt[0], window="hann")
    selected = (freq >= low) & (freq <= high)
    if not np.any(selected):
        return FrequencyEstimate(None, resolution, duration, "unresolved_band")
    peak = float(freq[selected][np.argmax(power[selected])])
    return FrequencyEstimate(peak, resolution, duration, "ok")


@dataclass(frozen=True)
class PhaseConcentration:
    """Classical circular concentration of explicitly model-removed phase."""

    concentration: Optional[float]
    model_label: str
    sample_count: int
    label: str = "classical residual phase concentration (not quantum fidelity)"


def phase_concentration(
    phase_rad: ArrayLike, deterministic_phase_rad: ArrayLike, *, model_label: str,
) -> PhaseConcentration:
    """Return |mean exp(i(phase-model))| only for an explicitly supplied model.

    The model and its label must describe the phase removed (for example,
    externally calibrated drift plus modulation). Fitted models create an
    in-sample descriptive statistic, not independent evidence. Raw rotating
    coherence must never gate estimation of a modulation coefficient.
    """
    phase = _vector(phase_rad, "phase_rad")
    model = _vector(deterministic_phase_rad, "deterministic_phase_rad")
    if model.shape != phase.shape or not isinstance(model_label, str) or not model_label.strip():
        raise ValueError("provide a matching deterministic model and a nonempty label")
    value = float(abs(np.mean(np.exp(1j * (phase - model))))) if phase.size else None
    return PhaseConcentration(value, model_label, int(phase.size))


@dataclass(frozen=True)
class PhaseRegression:
    """OLS phase = intercept + drift_rad_s*time + kappa*calibrated_x0.

    Standard errors assume independent Gaussian phase errors and exact x0.
    FIR-correlated or errors-in-variables data require a separate covariance
    model. Residual-estimated uncertainty is descriptive, not Bayes evidence.
    """

    intercept: Optional[float]
    drift_rad_s: Optional[float]
    kappa: Optional[float]
    kappa_standard_error: Optional[float]
    residual_sigma: Optional[float]
    sample_count: int
    rank: int
    status: str


def fit_phase_regression(
    time_s: ArrayLike, phase_rad: ArrayLike, calibrated_x0: ArrayLike, *,
    noise_sigma: Optional[float] = None,
) -> PhaseRegression:
    """Fit intercept, drift, and coupling without any raw-coherence threshold.

    Inputs must be finite matching vectors from one contiguous phase segment.
    x0 must be delay-aligned and calibrated in the units in which kappa is
    reported. Provide independently known noise_sigma for calibrated standard
    errors; otherwise estimate the residual RMS using n-3 degrees of freedom.
    """
    t, phase, x = (_vector(time_s, "time_s"), _vector(phase_rad, "phase_rad"),
                   _vector(calibrated_x0, "calibrated_x0"))
    if not t.shape == phase.shape == x.shape:
        raise ValueError("time, phase and reference must match")
    if noise_sigma is not None and (not np.isfinite(noise_sigma) or noise_sigma <= 0):
        raise ValueError("noise_sigma must be independently known and positive")
    n = t.size
    if n < 4:
        return PhaseRegression(None, None, None, None, None, n, 0, "insufficient_data")
    if np.any(np.diff(t) <= 0):
        raise ValueError("time must be strictly increasing")
    means = np.array([np.mean(t), np.mean(x)])
    centered = np.column_stack((t - means[0], x - means[1]))
    scales = np.std(centered, axis=0)
    if np.any(scales == 0):
        return PhaseRegression(None, None, None, None, None, n, 1, "rank_deficient")
    design = np.column_stack((np.ones(n), centered / scales))
    coeff, _, rank, singular = np.linalg.lstsq(design, phase, rcond=1e-10)
    if rank < 3 or singular[-1] / singular[0] < 1e-10:
        return PhaseRegression(None, None, None, None, None, n, int(rank), "rank_deficient")
    residual = phase - design @ coeff
    residual_sigma = float(np.sqrt(np.dot(residual, residual) / (n - 3)))
    sigma = residual_sigma if noise_sigma is None else noise_sigma
    covariance = sigma**2 * np.linalg.inv(design.T @ design)
    drift, kappa = coeff[1:] / scales
    intercept = coeff[0] - drift * means[0] - kappa * means[1]
    return PhaseRegression(float(intercept), float(drift), float(kappa),
                           float(np.sqrt(covariance[2, 2]) / scales[1]),
                           residual_sigma, n, int(rank), "ok")
