"""Offline and freshness regressions for the passive EXP01 dashboard."""

import importlib
import sys
import threading
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


@pytest.mark.parametrize("independent", [False, True])
def test_calibrated_model_uses_actual_phase_and_explicit_assumptions(
    independent: bool,
) -> None:
    """Point-model evidence uses known noise/drift, never fitted residual noise."""
    from experiments.qcal_exp01.dsp import DSPConfig

    reference = _ReferenceModel(
        amplitude=1.0, frequency_hz=141.7, phase_rad=0,
        calibration_label="synthetic fixture only", noise_sigma_rad=0.1,
        independent_samples_assumed=independent, known_drift_rad_s=0.0,
        slope_h1=1.0, slope_h0=0.0,
    )
    acquisition = _Acquisition(DSPConfig(), reference_model=reference)
    times = np.arange(2_000) / 1_000
    phase = np.random.default_rng(20).normal(0, 0.1, times.size)
    result = {}
    acquisition._add_calibrated_model(result, times, phase)
    assert result["kappa"] == pytest.approx(0, abs=0.02)
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


@pytest.mark.parametrize("age", [0, -1, float("nan"), float("inf")])
def test_invalid_freshness_is_rejected(age: float) -> None:
    """Configuration errors cannot silently disable the stale-data check."""
    with pytest.raises(ValueError):
        create_app(stale_after=age)
