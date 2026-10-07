"""Offline and freshness regressions for the passive EXP01 dashboard."""

import importlib
import sys
import threading
from collections.abc import Callable
from types import SimpleNamespace

import numpy as np
import pytest

from experiments.qcal_exp01.dashboard import (
    _Acquisition, _ReferenceModel, create_app, display_state,
)


def snapshot(*, state: str = "receiving", valid: bool = True) -> dict:
    """Build deterministic, explicitly synthetic acquisition state."""
    return {
        "receiver": {
            "state": state,
            "last_valid_monotonic": 100.0,
            "packets_received": 1,
        },
        "source_kind": "synthetic",
        "dsp": {
            "valid": valid,
        },
    }


def conditional_snapshot() -> dict:
    """Describe a fully declared synthetic conditional model, not hardware."""
    data = snapshot()
    data["dsp"].update(
        duration_s=2.0,
        frequency_hz=[0.0, 0.5, 1.0],
        phase_psd_rad2_hz=[0.0, 0.2, 0.1],
        ln_bayes_factor=-4.25,
        noise_sigma_rad=0.1,
        calibration_label="independent fixture calibration",
        independent_samples_assumed=True,
        evidence_valid=True,
        evidence_model_label="H0: κ=0; H1: κ~N(0, 1)",
    )
    return data


def test_import_and_factory_start_no_receiver_or_threads() -> None:
    """Factory construction must not acquire hardware or start workers."""
    before_threads = set(threading.enumerate())
    before_receiver = sys.modules.get("experiments.qcal_exp01.receiver")
    module = importlib.reload(sys.modules["experiments.qcal_exp01.dashboard"])
    app = module.create_app()
    assert set(threading.enumerate()) == before_threads
    assert sys.modules.get("experiments.qcal_exp01.receiver") is before_receiver
    assert app.server.test_client().get("/health").status_code == 503


def test_offline_measurements_are_unavailable() -> None:
    """Offline state must not replace absent measurements with target values."""
    state = display_state(None, now=100.0)
    assert not state["healthy"]
    assert state["metrics"]
    assert all(value is None for value in state["metrics"].values())
    assert len(state["figure"].data) == 0
    assert "no confirmado" in state["source"]


@pytest.mark.parametrize(
    ("receiver_state", "valid", "now"),
    [
        ("receiving", True, 103.0),
        ("stopped", True, 100.5),
        ("error", True, 100.5),
        ("receiving", False, 100.5),
        ("receiving", True, 99.0),
    ],
)
def test_unusable_data_suppresses_evidence_and_health(
    receiver_state: str, valid: bool, now: float
) -> None:
    """Staleness, disconnection, invalid phase, and future timestamps fail closed."""
    data = conditional_snapshot()
    data["receiver"]["state"] = receiver_state
    data["dsp"]["valid"] = valid
    state = display_state(data, now=now)
    assert not state["healthy"]
    assert "no disponible" in state["evidence_label"]
    assert all(value is None for value in state["metrics"].values())
    assert len(state["figure"].data) == 0
    app = create_app(lambda: data, clock=lambda: now)
    assert app.server.test_client().get("/health").status_code == 503


def test_fresh_validated_synthetic_data_is_healthy_but_not_hardware() -> None:
    """Transport health is not a physical signal confirmation."""
    app = create_app(lambda: snapshot(), clock=lambda: 100.5)
    result = app.server.test_client().get("/health")
    assert result.status_code == 200
    assert result.json["healthy"] is True
    assert "SINTÉTICA" in result.json["source"]
    assert result.json["hardware_confirmed"] is False


def test_provider_failure_returns_unavailable_health() -> None:
    """Snapshot publication errors must not claim fresh data."""
    def broken() -> dict:
        """Simulate a failed acquisition provider."""
        raise RuntimeError("acquisition unavailable")

    app = create_app(broken)
    assert app.server.test_client().get("/health").status_code == 503


def test_negative_log_bayes_factor_remains_visible_and_conditional() -> None:
    """A negative model comparison must not be clamped into favorable evidence."""
    state = display_state(conditional_snapshot(), now=100.5)
    assert state["metrics"]["ln BF₁₀ (modelo condicional)"] == -4.25
    assert "-4.25" in state["evidence_label"]
    assert "favorece H₀" in state["evidence_label"]
    assert "independientes asumidos" in state["evidence_label"]
    assert "No es confirmación física" in state["evidence_label"]
    assert "rad²/Hz" in state["figure"].layout.yaxis.title.text


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("noise_sigma_rad", None),
        ("noise_sigma_rad", 0.0),
        ("calibration_label", ""),
        ("independent_samples_assumed", False),
        ("evidence_valid", False),
        ("evidence_model_label", ""),
        ("ln_bayes_factor", float("nan")),
        ("duration_s", 0.5),
    ],
)
def test_incomplete_model_never_has_an_evidence_verdict(
    field: str, value: object
) -> None:
    """Every evidence assumption must be explicit and usable."""
    data = conditional_snapshot()
    data["dsp"][field] = value
    state = display_state(data, now=100.5)
    assert state["metrics"]["ln BF₁₀ (modelo condicional)"] is None
    assert "no disponible" in state["evidence_label"]


def test_rejected_latest_packet_suppresses_evidence() -> None:
    """A previously valid window cannot mask a current validation error."""
    data = conditional_snapshot()
    data["receiver"]["last_error"] = "invalid sample payload"
    app = create_app(lambda: data, clock=lambda: 100.5)
    assert app.server.test_client().get("/health").status_code == 503
    assert "no disponible" in display_state(data, now=100.5)["evidence_label"]


def test_actual_paired_demodulated_phase_uses_accumulated_hz_psd() -> None:
    """The measured phase spectrum uses long-window spacing, not the IF FFT."""
    from experiments.qcal_exp01.dsp import DSPConfig

    config = DSPConfig(fs=100_000, fc=10_000, cutoff_hz=1_000)
    acquisition = _Acquisition(config)
    acquisition.reset(0)
    samples = np.arange(210_000)
    angle = 2 * np.pi * config.fc * samples / config.fs
    modulation = 0.25 * np.sin(2 * np.pi * 141.7 * samples / config.fs)
    a = np.rint(12_000 * np.cos(angle)).astype(np.int16)
    b = np.rint(12_000 * np.cos(angle + modulation)).astype(np.int16)
    for first in range(0, samples.size, 1024):
        acquisition.accept(SimpleNamespace(
            sample_rate=config.fs, first_sample_index=first,
            channel_a=a[first:first + 1024], channel_b=b[first:first + 1024],
        ))
    data = acquisition.snapshot()
    assert data["valid"]
    assert data["duration_s"] == pytest.approx(2.0)
    assert data["resolution_hz"] == pytest.approx(0.5)
    assert np.diff(data["frequency_hz"]) == pytest.approx(0.5)
    assert data["modulation_hz"] == pytest.approx(141.7, abs=0.5)
    assert np.all(data["phase_psd_rad2_hz"] >= 0)
    assert "ln_bayes_factor" not in data
    acquisition.reset(samples.size + 100)
    assert not acquisition.snapshot()["valid"]


def _cached_fixture(clock: Callable[[], float]) -> _Acquisition:
    """Populate a valid 1.2-second dual-IF window with a controlled clock."""
    from experiments.qcal_exp01.dsp import DSPConfig

    config = DSPConfig(fs=100_000, fc=10_000, cutoff_hz=1_000)
    acquisition = _Acquisition(config, clock=clock)
    indexes = np.arange(120_000)
    carrier = 2 * np.pi * config.fc * indexes / config.fs
    phase = .25 * np.sin(2 * np.pi * 141.7 * indexes / config.fs)
    a = np.rint(12_000 * np.cos(carrier)).astype(np.int16)
    b = np.rint(12_000 * np.cos(carrier + phase)).astype(np.int16)
    for first in range(0, indexes.size, 1024):
        acquisition.accept(SimpleNamespace(
            sample_rate=config.fs, first_sample_index=first,
            channel_a=a[first:first + 1024], channel_b=b[first:first + 1024],
        ))
    return acquisition


def test_expensive_phase_analysis_is_cached_at_one_hertz(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Frequent UI/health polls must not repeat concatenation, detrending, or FFT."""
    from experiments.qcal_exp01 import dashboard

    now = [100.0]
    acquisition = _cached_fixture(lambda: now[0])
    original = dashboard.signal.periodogram
    calls = []

    def counted(*args: object, **kwargs: object) -> tuple:
        """Count periodograms without changing their numeric behavior."""
        calls.append(1)
        return original(*args, **kwargs)

    monkeypatch.setattr(dashboard.signal, "periodogram", counted)
    first = acquisition.snapshot()
    for elapsed in (.1, .2, .5, .9):
        now[0] = 100.0 + elapsed
        cached = acquisition.snapshot()
        assert cached["modulation_hz"] == first["modulation_hz"]
    assert len(calls) == 1
    now[0] = 101.0
    assert acquisition.snapshot()["valid"]
    assert len(calls) == 2


def test_invalid_phase_immediately_invalidates_cached_spectrum() -> None:
    """Low-amplitude input must not reuse a still-young favorable analysis."""
    now = [100.0]
    acquisition = _cached_fixture(lambda: now[0])
    assert "phase_psd_rad2_hz" in acquisition.snapshot()
    now[0] = 100.1
    zeros = np.zeros(2048, dtype=np.int16)
    acquisition.accept(SimpleNamespace(
        sample_rate=100_000, first_sample_index=120_000,
        channel_a=zeros, channel_b=zeros,
    ))
    result = acquisition.snapshot()
    assert not result["valid"]
    assert "phase_psd_rad2_hz" not in result


def test_gap_during_analysis_cannot_publish_old_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A concurrent stream reset invalidates an in-flight analysis generation."""
    acquisition = _cached_fixture(lambda: 100.0)
    original = acquisition._analyze_history

    def interrupted(result: dict, blocks: tuple) -> None:
        """Reset the stream during computation, before result publication."""
        acquisition.reset(121_000)
        original(result, blocks)

    monkeypatch.setattr(acquisition, "_analyze_history", interrupted)
    result = acquisition.snapshot()
    assert not result["valid"]
    assert "phase_psd_rad2_hz" not in result


def test_new_packets_cannot_make_old_cached_analysis_fresh() -> None:
    """Fresh transport traffic must not revive analysis of older samples."""
    data = conditional_snapshot()
    data["dsp"]["data_received_at_monotonic"] = 90.0
    state = display_state(data, now=100.5)
    assert not state["healthy"]
    assert "no disponible" in state["evidence_label"]


@pytest.mark.parametrize("independent", [False, True])
def test_calibrated_model_uses_actual_phase_and_explicit_assumptions(
    independent: bool,
) -> None:
    """Point-model evidence uses known noise/drift, never fitted residual noise."""
    from experiments.qcal_exp01.dsp import DSPConfig

    reference = _ReferenceModel(
        amplitude=1.0, frequency_hz=141.7, phase_rad=0,
        calibration_label="synthetic fixture only", noise_sigma_rad=0.1,
        reference_units="um",
        independent_samples_assumed=independent, known_drift_rad_s=0.0,
        slope_h1=1.0, slope_h0=0.0,
    )
    acquisition = _Acquisition(DSPConfig(), reference_model=reference)
    times = np.arange(2_000) / 1_000
    phase = np.random.default_rng(20).normal(0, 0.1, times.size)
    result = {}
    acquisition._add_calibrated_model(result, times, phase)
    assert result["kappa"] == pytest.approx(0, abs=0.02)
    data = snapshot()
    data["dsp"].update(result, duration_s=2.0)
    label = display_state(data, now=100.5)["source"]
    assert "no ajustada" in label
    assert "141.7" in label and "um" in label
    assert "declaración no verificada" in label
    if independent:
        assert result["ln_bayes_factor"] < 0
        assert result["evidence_valid"] is True
        assert "κ=1" in result["evidence_model_label"]
    else:
        assert "ln_bayes_factor" not in result


@pytest.mark.parametrize("missing", ["noise_sigma_rad", "known_drift_rad_s"])
def test_fitted_nuisance_parameters_do_not_become_bayes_inputs(missing: str) -> None:
    """Fitted drift or residual sigma cannot silently replace known BF inputs."""
    from experiments.qcal_exp01.dsp import DSPConfig

    settings = dict(
        amplitude=1.0, frequency_hz=141.7, phase_rad=0,
        calibration_label="synthetic fixture only", noise_sigma_rad=0.1,
        independent_samples_assumed=True, known_drift_rad_s=0.0,
    )
    settings[missing] = None
    acquisition = _Acquisition(DSPConfig(), reference_model=_ReferenceModel(**settings))
    times = np.arange(2_000) / 1_000
    result = {}
    acquisition._add_calibrated_model(result, times, 0.2 * times)
    assert "ln_bayes_factor" not in result


@pytest.mark.parametrize(
    ("cli", "expected"),
    [
        ([], "127.0.0.2"),
        (["--expected-sender", "127.0.0.3"], "127.0.0.3"),
        (["--expected-source", "127.0.0.4"], "127.0.0.4"),
    ],
)
def test_cli_sender_environment_and_explicit_source_kind(
    monkeypatch: pytest.MonkeyPatch, cli: list[str], expected: str
) -> None:
    """The image's default CLI accepts a sender environment and declared source."""
    from experiments.qcal_exp01 import dashboard, receiver

    calls = {}

    class FakeReceiver:
        """Record explicit lifecycle calls without opening sockets."""

        def __init__(self, **settings: object) -> None:
            """Capture the sender and network configuration."""
            calls["settings"] = settings

        def start(self) -> bool:
            """Simulate a successful explicit bind."""
            calls["started"] = True
            return True

        def stop(self) -> None:
            """Record application shutdown."""
            calls["stopped"] = True

        def snapshot(self) -> receiver.ReceiverSnapshot:
            """Return an unavailable but well-typed health state."""
            return receiver.ReceiverSnapshot(state="waiting")

    def fake_app(provider: object, **settings: object) -> SimpleNamespace:
        """Record the declared provenance and return a nonblocking fake server."""
        calls["source"] = provider()["source_kind"]
        return SimpleNamespace(run=lambda **kwargs: None)

    monkeypatch.setenv("QCAL_EXPECTED_SENDER", "127.0.0.2")
    monkeypatch.setenv("QCAL_EXPECTED_SOURCE", "127.0.0.9")
    monkeypatch.setenv("QCAL_SOURCE_KIND", "synthetic")
    monkeypatch.setattr(receiver, "UDPReceiver", FakeReceiver)
    monkeypatch.setattr(dashboard, "create_app", fake_app)
    assert dashboard.main(["--udp-host", "0.0.0.0", "--allow-lan", *cli]) == 0
    assert calls["settings"]["expected_sender"] == expected
    assert calls["settings"]["allow_lan"] is True
    assert calls["source"] == "synthetic"
    assert calls["started"] and calls["stopped"]


@pytest.mark.parametrize("age", [0, -1, float("nan"), float("inf")])
def test_invalid_freshness_is_rejected(age: float) -> None:
    """Configuration errors cannot silently disable the stale-data check."""
    with pytest.raises(ValueError):
        create_app(stale_after=age)
