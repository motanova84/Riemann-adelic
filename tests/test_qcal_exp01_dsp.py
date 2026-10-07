"""Regression tests for synthetic IF demodulation and calibrated phase analysis."""

import numpy as np
import pytest
from types import SimpleNamespace

from experimental_validation import F0_HZ

from experiments.qcal_exp01.dsp import (
    DSPConfig,
    DualChannelDemodulator,
    StreamingDemodulator,
    estimate_modulation_frequency,
    fit_phase_regression,
    phase_concentration,
)


@pytest.mark.parametrize("kwargs", [
    {"fc": 80_000_000.0}, {"fc": 500_000.0}, {"fc": 0},
    {"fs": -1}, {"num_taps": 100}, {"num_taps": 1},
    {"num_taps": 5.5}, {"cutoff_hz": 100_000},
    {"min_amplitude": 0}, {"fc": np.nan},
])
def test_invalid_acquisition_settings(kwargs: dict) -> None:
    """An IF must actually be sampled below Nyquist, not silently aliased."""
    with pytest.raises(ValueError):
        DSPConfig(**kwargs)


def test_streaming_matches_one_shot_and_delays_reference_across_tiny_blocks() -> None:
    """Oscillator, FIR zero state, reference delay and unwrap are block invariant."""
    config = DSPConfig()
    n = 12_000
    index = np.arange(n)
    time = index / config.fs
    reference = np.sin(2 * np.pi * 141.7 * time)
    phase = 0.2 + 2 * np.pi * 800 * time + 0.15 * reference
    samples = np.cos(2 * np.pi * config.fc * time + phase)
    whole = StreamingDemodulator(config).process(samples, reference)
    stream = StreamingDemodulator(config)
    boundaries = [0, 7, 12, 19, 48, 57, 112, 1000, 5555, n]
    pieces = [stream.process(samples[a:b], reference[a:b])
              for a, b in zip(boundaries[:-1], boundaries[1:])]
    for field in ("baseband", "amplitude", "phase_rad", "time_s", "reference"):
        np.testing.assert_allclose(
            np.concatenate([getattr(piece, field) for piece in pieces]),
            getattr(whole, field), equal_nan=True, atol=1e-11, rtol=1e-11,
        )
    np.testing.assert_array_equal(np.concatenate([p.valid for p in pieces]), whole.valid)
    np.testing.assert_array_equal(np.concatenate([p.sample_index for p in pieces]), index)
    np.testing.assert_array_equal(
        np.concatenate([p.phase_segment for p in pieces]), whole.phase_segment
    )
    assert np.all(np.isnan(whole.reference[:stream.delay_samples]))
    np.testing.assert_array_equal(whole.reference[stream.delay_samples:],
                                  reference[:-stream.delay_samples])
    assert not np.any(whole.valid[:config.num_taps - 1])
    # A positive residual frequency unwraps over many 2π cycles, not π flips.
    assert whole.phase_rad[-1] > 50
    assert np.median(np.diff(whole.phase_rad[whole.valid])) > 0


def test_positive_phase_convention_and_no_invalid_carrier_subtraction() -> None:
    """-sin quadrature recovers positive phase; demodulation already removes IF."""
    config = DSPConfig()
    t = np.arange(20_000) / config.fs
    waveform = np.cos(2 * np.pi * config.fc * t + 0.7)
    block = StreamingDemodulator(config).process(waveform)
    assert np.mean(block.phase_rad[block.valid]) == pytest.approx(0.7, abs=2e-5)
    assert np.mean(block.amplitude[block.valid]) == pytest.approx(1, abs=2e-5)
    assert abs(np.mean(np.diff(block.phase_rad[block.valid]))) < 1e-7


def test_reference_missing_blocks_preserve_only_available_history() -> None:
    """Missing x0 samples leave delay-aligned holes, not fabricated observations."""
    stream = StreamingDemodulator(DSPConfig(num_taps=11, cutoff_hz=10_000))
    stream.process(np.zeros(20), np.arange(20, dtype=float))
    stream.process([])
    stream.process(np.zeros(2))  # x0 missing at absolute indices 20 and 21.
    block = stream.process(np.zeros(6), np.arange(22, 28, dtype=float))
    np.testing.assert_allclose(block.reference, [17, 18, 19, np.nan, np.nan, 22],
                               equal_nan=True)


def test_transport_packet_adapter_requires_explicit_reference_calibration() -> None:
    """Packets preserve absolute acquisition indices and do not infer x0 units."""
    config = DSPConfig(num_taps=11, cutoff_hz=10_000)
    first = 500
    idx = np.arange(first, first + 200)
    channel_a = np.round(10_000 * np.cos(
        2 * np.pi * config.fc * idx / config.fs + 0.3
    )).astype(np.int16)
    channel_b = np.arange(200, dtype=np.int16)
    packet = SimpleNamespace(first_sample_index=first, sample_rate=config.fs,
                             channel_a=channel_a, channel_b=channel_b)
    no_reference = StreamingDemodulator(config).process_packet(
        packet, signal_units_per_count=1e-4
    )
    assert no_reference.reference is None
    calibrated = StreamingDemodulator(config).process_packet(
        packet, signal_units_per_count=1e-4, reference_units_per_count=0.01
    )
    assert calibrated.sample_index[0] == first
    assert calibrated.reset_occurred
    np.testing.assert_allclose(calibrated.reference[5:], channel_b[:-5] * 0.01)
    assert np.mean(calibrated.phase_rad[calibrated.valid]) == pytest.approx(0.3, abs=0.002)
    packet.sample_rate = config.fs / 2
    with pytest.raises(ValueError, match="sample_rate"):
        StreamingDemodulator(config).process_packet(packet)
    packet.sample_rate = config.fs
    with pytest.raises(ValueError, match="calibration"):
        StreamingDemodulator(config).process_packet(packet, reference_units_per_count=0)


def test_dual_if_packets_recover_differential_phase_and_calibrated_coupling() -> None:
    """Two carrier channels recover B−A, not carrier ADC counts as displacement."""
    config = DSPConfig()
    n = 150_000
    indices = np.arange(n)
    time = indices / config.fs
    x0 = 0.01 * np.sin(2 * np.pi * F0_HZ * time)
    common = 2 * np.pi * config.fc * time + 0.3 + 2 * np.pi * 200 * time
    a = np.round(6_000 * np.cos(common)).astype(np.int16)
    b = np.round(6_000 * np.cos(common + 0.4 + 13.4034 * x0)).astype(np.int16)
    stream = DualChannelDemodulator(config)
    pieces = []
    for start in range(0, n, 342):
        stop = min(start + 342, n)
        packet = SimpleNamespace(first_sample_index=start, sample_rate=config.fs,
                                 channel_a=a[start:stop], channel_b=b[start:stop])
        pieces.append(stream.process_packet(
            packet, signal_units_per_count=1 / 32768, reference=x0[start:stop]
        ))
    phase = np.concatenate([p.phase_rad for p in pieces])
    t = np.concatenate([p.time_s for p in pieces])
    reference = np.concatenate([p.reference for p in pieces])
    valid = np.concatenate([p.valid for p in pieces])
    fit = fit_phase_regression(t[valid], phase[valid], reference[valid])
    assert fit.intercept == pytest.approx(0.4, abs=0.001)
    assert fit.drift_rad_s == pytest.approx(0, abs=0.002)
    assert fit.kappa == pytest.approx(13.4034, abs=0.03)
    assert estimate_modulation_frequency(
        t[valid], phase[valid]
    ).frequency_hz == pytest.approx(F0_HZ, abs=1 / (t[valid][-1] - t[valid][0]))
    whole = DualChannelDemodulator(config).process(a / 32768, b / 32768, x0)
    np.testing.assert_allclose(phase, whole.phase_rad, equal_nan=True, atol=1e-10)


def test_dual_channel_masks_missing_reference_carrier_and_handles_reset() -> None:
    """Both carrier envelopes must be valid; discontinuities erase cycle counts."""
    stream = DualChannelDemodulator()
    carrier = np.cos(2 * np.pi * 0.1 * np.arange(200))
    dead_a = stream.process(np.zeros(200), carrier)
    assert dead_a.status == "low_amplitude"
    assert not dead_a.valid.any()
    assert np.isnan(dead_a.phase_rad).all()
    block = stream.process(carrier, carrier, start_index=5000)
    assert block.reset_occurred
    assert not block.valid[:100].any()
    assert block.reference is None
    with pytest.raises(ValueError):
        stream.process(carrier, carrier[:-1])


def test_dropout_failure_and_discontinuity_reset() -> None:
    """Invalid phase is masked and a discontinuity restarts zero-state settling."""
    config = DSPConfig(num_taps=11, cutoff_hz=10_000)
    stream = StreamingDemodulator(config)
    carrier = np.cos(2 * np.pi * config.fc * np.arange(200) / config.fs)
    assert stream.process(carrier).status == "ok"
    dead = stream.process(np.zeros(100))
    assert not np.any(dead.valid[config.num_taps:])
    assert np.all(np.isnan(dead.phase_rad[~dead.valid]))
    failure = stream.process(carrier, healthy=False)
    assert failure.status == "failure"
    assert not failure.valid.any()
    assert np.all(np.isnan(failure.phase_rad))
    resumed = stream.process(carrier)
    assert not resumed.valid[:config.num_taps - 1].any()
    gap = stream.process(carrier, start_index=5000)
    fresh = StreamingDemodulator(config).process(carrier, start_index=5000)
    assert gap.reset_occurred
    np.testing.assert_allclose(gap.baseband, fresh.baseband)
    assert not gap.valid[:config.num_taps - 1].any()


def test_low_amplitude_empty_and_invalid_samples() -> None:
    """Failure states carry masks instead of plausible scalar measurements."""
    stream = StreamingDemodulator()
    empty = stream.process([])
    assert empty.status == "empty"
    assert empty.reference is None
    assert stream.process(np.zeros(10)).status == "settling"
    quiet = stream.process(np.zeros(200))
    assert quiet.status == "low_amplitude"
    assert np.isnan(quiet.phase_rad).all()
    for samples in ([np.nan], [np.inf], [1 + 1j], [[1, 2]]):
        with pytest.raises(ValueError):
            stream.process(samples)
    with pytest.raises(ValueError):
        stream.process([1, 2], reference=[1])
    with pytest.raises(ValueError):
        stream.process([1], start_index=1.5)


def test_modulation_frequency_not_mean_residual_frequency() -> None:
    """A sinusoidal phase modulation is detected despite unrelated linear drift."""
    fs = 4000.0
    t = np.arange(4000) / fs
    phase = 4 + 2 * np.pi * 17 * t + 0.7 * np.sin(2 * np.pi * F0_HZ * t)
    estimate = estimate_modulation_frequency(t, phase)
    assert estimate.status == "ok"
    assert estimate.frequency_hz == pytest.approx(F0_HZ, abs=estimate.resolution_hz)
    assert estimate.resolution_hz >= 1.0
    assert abs(estimate.frequency_hz - 17) > 100
    short = estimate_modulation_frequency(t[:100], phase[:100])
    assert short.frequency_hz is None
    assert short.status == "insufficient_duration"
    constant = estimate_modulation_frequency(t, 4 + 2 * np.pi * 17 * t)
    assert constant.frequency_hz is None
    assert constant.status == "no_modulation"
    few = estimate_modulation_frequency(t[:2], phase[:2])
    assert few.frequency_hz is None
    assert few.resolution_hz is None
    with pytest.raises(ValueError):
        estimate_modulation_frequency(np.array([0, 1, 2, 4]), np.arange(4))


def test_phase_model_concentration_is_classical_and_explicit() -> None:
    """Model-removed concentration is labelled, not a quantum fidelity."""
    t = np.linspace(0, 1, 1000)
    model = 2 * np.pi * 100 * t + 0.7 * np.sin(2 * np.pi * 141.7 * t)
    result = phase_concentration(model, model, model_label="declared drift + modulation")
    assert result.concentration == pytest.approx(1)
    assert "not quantum fidelity" in result.label
    assert phase_concentration([], [], model_label="specified empty model").concentration is None
    with pytest.raises(ValueError):
        phase_concentration(model, np.zeros_like(model), model_label="")


def test_calibrated_regression_with_low_raw_rotating_coherence() -> None:
    """Coupling is estimated even when phase rotation makes raw coherence tiny."""
    rng = np.random.default_rng(12)
    t = np.linspace(0, 1, 5000)
    x = 0.1 * np.sin(2 * np.pi * 141.7 * t)
    phase = 0.6 + 2 * np.pi * 50 * t + 13.4034 * x + rng.normal(0, 0.03, t.size)
    assert abs(np.mean(np.exp(1j * phase))) < 0.01
    fit = fit_phase_regression(t, phase, x, noise_sigma=0.03)
    assert fit.status == "ok"
    assert fit.rank == 3
    assert fit.intercept == pytest.approx(0.6, abs=0.003)
    assert fit.drift_rad_s == pytest.approx(2 * np.pi * 50, abs=0.005)
    assert fit.kappa == pytest.approx(13.4034, abs=4 * fit.kappa_standard_error)
    assert 0 < fit.kappa_standard_error < 0.01


def test_end_to_end_delay_aligned_coupling() -> None:
    """A small modulation recovers calibrated coupling to FIR-band accuracy."""
    config = DSPConfig()
    t = np.arange(150_000) / config.fs
    x = 0.01 * np.sin(2 * np.pi * 141.7 * t)
    phase = 0.2 + 2 * np.pi * 200 * t + 13.4034 * x
    sample = np.cos(2 * np.pi * config.fc * t + phase)
    block = StreamingDemodulator(config).process(sample, x)
    good = block.valid & np.isfinite(block.reference)
    result = fit_phase_regression(
        block.time_s[good], block.phase_rad[good], block.reference[good]
    )
    assert result.kappa == pytest.approx(13.4034, abs=0.03)
    estimate = estimate_modulation_frequency(block.time_s[good], block.phase_rad[good])
    assert estimate.frequency_hz == pytest.approx(141.7, abs=estimate.resolution_hz)


def test_regression_rank_and_insufficient_data() -> None:
    """An unidentified slope is unavailable, not a bogus coefficient or precision."""
    t = np.arange(10, dtype=float)
    assert fit_phase_regression(t, t, t).status == "rank_deficient"
    assert fit_phase_regression(t, t, np.ones(10)).kappa is None
    assert fit_phase_regression(t[:3], t[:3], t[:3]).status == "insufficient_data"
    with pytest.raises(ValueError):
        fit_phase_regression(t, t, t, noise_sigma=0)
    with pytest.raises(ValueError):
        fit_phase_regression(t[::-1], t, np.sin(t))
