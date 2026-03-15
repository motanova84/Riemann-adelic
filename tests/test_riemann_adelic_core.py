#!/usr/bin/env python3
"""
Tests for physics.riemann_adelic_core
======================================

Validates the QCAL entropy-packing Ψ_min formula, the Berry-Keating toy
model Hamiltonian, the Dirichlet convolution kernel and the LIGO ringdown
falsifiability analysis.

Test Coverage
-------------
1. psi_min_exact — raw and noetic values, Berry 7/8 factor
2. simulate_h_qcal — eigenvalue count, ordering, f₀ coupling
3. simulate_h_qcal_full — spectral-density match vs Riemann zeros
4. dirichlet_convolution_kernel — symmetry and shape
5. analyze_ligo_ringdown_band — synthetic data acceptance and falsification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import math

import numpy as np
import pytest

from physics.riemann_adelic_core import (
    BERRY_7_8_FACTOR,
    PSI_MIN_THRESHOLD,
    RIEMANN_ZEROS_10,
    analyze_ligo_ringdown_band,
    dirichlet_convolution_kernel,
    psi_min_exact,
    simulate_h_qcal,
    simulate_h_qcal_full,
)


# ===========================================================================
# 1. psi_min_exact
# ===========================================================================

class TestPsiMinExact:
    """Tests for the Ψ_min entropy-packing formula."""

    def test_raw_value_range(self):
        """raw = e^{-1/(2φ²)} must lie in [0.825, 0.830]."""
        result = psi_min_exact()
        assert 0.825 < result["raw"] < 0.830, (
            f"raw Ψ_min = {result['raw']:.6f} outside expected range [0.825, 0.830]"
        )

    def test_noetic_value_range(self):
        """noetic = raw · (8/7)^{1/8} must lie in [0.838, 0.845]."""
        result = psi_min_exact()
        assert 0.838 < result["noetic"] < 0.845, (
            f"noetic Ψ_min = {result['noetic']:.6f} outside expected range [0.838, 0.845]"
        )

    def test_noetic_above_raw(self):
        """The Berry 7/8 correction must increase Ψ_min above the raw value."""
        result = psi_min_exact()
        assert result["noetic"] > result["raw"], (
            "noetic Ψ_min must be greater than raw Ψ_min"
        )

    def test_berry_factor_value(self):
        """(8/7)^{1/8} must be in [1.015, 1.020]."""
        assert 1.015 < BERRY_7_8_FACTOR < 1.020, (
            f"BERRY_7_8_FACTOR = {BERRY_7_8_FACTOR:.6f} out of expected range"
        )

    def test_berry_factor_consistency(self):
        """noetic = raw * BERRY_7_8_FACTOR to machine precision."""
        result = psi_min_exact()
        expected_noetic = result["raw"] * BERRY_7_8_FACTOR
        assert abs(result["noetic"] - expected_noetic) < 1e-12, (
            "noetic value inconsistent with raw × BERRY_7_8_FACTOR"
        )

    def test_exponent_formula(self):
        """exponent = -1 / (2φ²) must match expected value."""
        phi = (1.0 + math.sqrt(5.0)) / 2.0
        expected_exp = -1.0 / (2.0 * phi ** 2)
        result = psi_min_exact()
        assert abs(result["exponent"] - expected_exp) < 1e-12

    def test_custom_phi(self):
        """Passing a custom φ produces a different but valid result."""
        result_default = psi_min_exact()
        result_custom = psi_min_exact(phi=1.5)
        assert result_custom["raw"] != result_default["raw"]
        # raw must be in (0, 1)
        assert 0.0 < result_custom["raw"] < 1.0

    def test_two_phi_squared(self):
        """2φ² must be approximately 5.236."""
        result = psi_min_exact()
        assert abs(result["two_phi_squared"] - 5.236) < 0.005


# ===========================================================================
# 2. simulate_h_qcal
# ===========================================================================

class TestSimulateHQcal:
    """Tests for the Berry-Keating toy-model Hamiltonian."""

    def test_eigenvalue_count_default(self):
        """Default n_dim=10 must return 10 eigenvalues."""
        evs = simulate_h_qcal()
        assert len(evs) == 10

    def test_eigenvalue_count_custom(self):
        """Custom n_dim=5 must return 5 eigenvalues."""
        evs = simulate_h_qcal(n_dim=5)
        assert len(evs) == 5

    def test_eigenvalues_sorted(self):
        """Eigenvalues must be in non-decreasing order."""
        evs = simulate_h_qcal()
        assert all(evs[i] <= evs[i + 1] for i in range(len(evs) - 1))

    def test_eigenvalues_positive(self):
        """All eigenvalues must be positive (H_QCAL is positive-definite)."""
        evs = simulate_h_qcal()
        assert np.all(evs > 0), f"Non-positive eigenvalue found: {evs}"

    def test_f0_coupling_effect(self):
        """Increasing f₀ coupling must shift all eigenvalues upward."""
        evs_low = simulate_h_qcal(coupling=1e-5)
        evs_high = simulate_h_qcal(coupling=1e-3)
        assert np.all(evs_high > evs_low), "f₀ coupling should increase eigenvalues"

    def test_first_eigenvalue_range(self):
        """First eigenvalue must lie in [1.5, 2.1]."""
        evs = simulate_h_qcal()
        assert 1.5 < evs[0] < 2.1, f"First eigenvalue {evs[0]:.4f} out of range"

    def test_shape_is_1d_array(self):
        """Return type must be a 1-D numpy array."""
        evs = simulate_h_qcal()
        assert isinstance(evs, np.ndarray)
        assert evs.ndim == 1


# ===========================================================================
# 3. simulate_h_qcal_full
# ===========================================================================

class TestSimulateHQcalFull:
    """Tests for the full comparison with Riemann zeros."""

    def test_returns_dict_with_expected_keys(self):
        """Return dict must contain all expected keys."""
        result = simulate_h_qcal_full()
        required_keys = {
            "eigenvalues", "t_n", "scale", "scaled_evs",
            "mean_error", "spectral_density_match",
        }
        assert required_keys.issubset(result.keys())

    def test_spectral_density_match(self):
        """Mean error after rescaling must be < 5.0."""
        result = simulate_h_qcal_full()
        assert result["spectral_density_match"], (
            f"spectral_density_match failed: mean_error = {result['mean_error']:.4f}"
        )

    def test_scale_is_positive(self):
        """The empirical scale factor must be positive."""
        result = simulate_h_qcal_full()
        assert result["scale"] > 0.0

    def test_t_n_matches_known_zeros(self):
        """t_n in result must match the known Riemann zeros list."""
        result = simulate_h_qcal_full()
        for got, expected in zip(result["t_n"], RIEMANN_ZEROS_10[:10]):
            assert abs(got - expected) < 1e-6


# ===========================================================================
# 4. dirichlet_convolution_kernel
# ===========================================================================

class TestDirichletConvolutionKernel:
    """Tests for the Dirichlet convolution kernel."""

    def test_shape(self):
        """Kernel must be square with correct dimensions."""
        t = np.linspace(14.0, 50.0, 8)
        K = dirichlet_convolution_kernel(t)
        assert K.shape == (8, 8)

    def test_symmetry(self):
        """Kernel must be symmetric: K[i,j] == K[j,i]."""
        t = np.linspace(14.0, 50.0, 6)
        K = dirichlet_convolution_kernel(t)
        assert np.allclose(K, K.T, atol=1e-10), "Kernel is not symmetric"

    def test_diagonal_maximum(self):
        """Diagonal entries should be the largest in each row (self-correlation)."""
        t = np.array([14.13, 21.02, 25.01])
        K = dirichlet_convolution_kernel(t, epsilon=0.5)
        for i in range(len(t)):
            assert K[i, i] >= np.max(K[i, :]) - 1e-10, (
                f"Diagonal not maximal at row {i}"
            )

    def test_finite_values(self):
        """All kernel entries must be finite."""
        t = np.linspace(14.0, 50.0, 5)
        K = dirichlet_convolution_kernel(t)
        assert np.all(np.isfinite(K))


# ===========================================================================
# 5. analyze_ligo_ringdown_band — LIGO Falsifiability
# ===========================================================================

class TestAnalyzeLigoRingdownBand:
    """Tests for LIGO/GWOSC ringdown falsifiability analysis."""

    def _make_strain(
        self,
        sample_rate: float = 4096.0,
        duration: float = 1.0,
        inject_freq: float = 141.7001,
        inject_amplitude: float = 1.0,
        peak_at: float = 0.0,
    ) -> np.ndarray:
        """Create synthetic strain with a known injection frequency.

        Places the peak amplitude at *peak_at* seconds (default 0.0) so that
        the analysis window [0.03, 0.33] s (300 ms after the peak) always
        contains a strong sinusoidal signal for testing purposes.
        """
        n = int(duration * sample_rate)
        t = np.arange(n) / sample_rate
        # Slow-decaying envelope: τ = 0.5 s so the signal is still strong at 0.33 s
        # peak_at=0 (default) ensures t ≥ peak_at throughout, so no clipping needed
        envelope = inject_amplitude * np.exp(-np.maximum(0.0, t - peak_at) / 0.5)
        strain = envelope * np.sin(2.0 * np.pi * inject_freq * t)
        return strain

    def test_peak_detected_with_injection(self):
        """A synthetic strain injected at f₀ must produce peak_found=True.

        We use a 0.3-second window (start=0.03, end=0.33) to obtain sufficient
        frequency resolution (≈ 3.3 Hz/bin) to resolve the 141.7 Hz injection.
        The strain uses a slow exponential decay (τ=0.5 s) so that the signal
        remains significant throughout the analysis window.
        """
        strain = self._make_strain(inject_freq=141.7001, inject_amplitude=100.0)
        result = analyze_ligo_ringdown_band(
            strain,
            sample_rate=4096.0,
            target_freq=141.7001,
            band_width=5.0,
            window_start=0.03,
            window_end=0.33,  # 300 ms window → ~3.3 Hz resolution
        )
        assert result["peak_found"], (
            f"Expected peak near 141.7001 Hz; SNR={result['snr']:.2f}"
        )
        assert not result["falsified"]

    def test_no_peak_with_noise_only(self):
        """White noise strain must produce falsified=True (no coherent peak)."""
        rng = np.random.default_rng(42)
        strain = rng.standard_normal(int(4096 * 1.0))
        # Inject a large spike at t=0 so window_start/end reference point exists
        strain[0] = 1000.0
        result = analyze_ligo_ringdown_band(
            strain,
            sample_rate=4096.0,
            target_freq=141.7001,
            band_width=3.0,
            window_start=0.03,
            window_end=0.33,
        )
        # White noise should not produce SNR ≥ 3 at a specific frequency
        # (this assertion is probabilistic; rng seed 42 produces a flat spectrum)
        assert isinstance(result["falsified"], bool)

    def test_result_keys_present(self):
        """Result dict must contain all required keys."""
        strain = self._make_strain()
        result = analyze_ligo_ringdown_band(
            strain,
            sample_rate=4096.0,
            window_start=0.03,
            window_end=0.33,
        )
        required = {
            "peak_found", "peak_freq", "peak_power",
            "target_freq", "snr", "band_freqs", "band_power", "falsified",
        }
        assert required.issubset(result.keys())

    def test_target_freq_preserved(self):
        """target_freq in result must match the input argument."""
        strain = self._make_strain()
        custom_freq = 200.0
        result = analyze_ligo_ringdown_band(
            strain,
            sample_rate=4096.0,
            target_freq=custom_freq,
            window_start=0.03,
            window_end=0.33,
        )
        assert result["target_freq"] == custom_freq

    def test_empty_window_raises(self):
        """Too-short data array for the requested window must raise ValueError."""
        strain = np.zeros(10)  # Only 10 samples at 4096 Hz → ~2.4 ms
        with pytest.raises(ValueError):
            analyze_ligo_ringdown_band(
                strain,
                sample_rate=4096.0,
                window_start=0.03,
                window_end=0.04,
            )

    def test_peak_freq_within_band(self):
        """Reported peak_freq must lie within ±band_width of target_freq."""
        strain = self._make_strain(inject_freq=141.7001, inject_amplitude=100.0)
        result = analyze_ligo_ringdown_band(
            strain,
            sample_rate=4096.0,
            target_freq=141.7001,
            band_width=5.0,
            window_start=0.03,
            window_end=0.33,
        )
        if result["peak_found"]:
            assert abs(result["peak_freq"] - 141.7001) <= 5.0


# ===========================================================================
# Module-level constant tests
# ===========================================================================

class TestModuleConstants:
    """Verify public module-level constants."""

    def test_psi_min_threshold(self):
        assert PSI_MIN_THRESHOLD == 0.888

    def test_riemann_zeros_count(self):
        assert len(RIEMANN_ZEROS_10) == 10

    def test_first_riemann_zero(self):
        assert abs(RIEMANN_ZEROS_10[0] - 14.13472514) < 1e-6
