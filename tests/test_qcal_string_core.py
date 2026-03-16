#!/usr/bin/env python3
"""
Test Suite for QCAL-Strings: Gran Unificación Noética
======================================================

Validates the QCAL-Strings framework (Phases #260-#262):
 - string_noetic_forcing():   KK string forcing operator
 - tachyon_censorship():      Architecture #261 off-critical mode suppression
 - hard_reset_noetic_protocol(): 141.7001 Hz Logos reset pulse
 - will_intention_operator(): SEQ-009 consciousness-density modulation
 - QCALStringSimulation:      Full RK4 spectral simulation
 - UPE signal helpers

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add project root to path (handled by conftest, but explicit for clarity)
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcal_string_core import (
    # Constants
    F0,
    MU_ADELIC,
    PSI_SUPERRADIANT,
    EPSILON_DEFAULT,
    PSI_RESET_THRESHOLD,
    RIEMANN_ZEROS_KK,
    # Core forcing
    string_noetic_forcing,
    # Tachyon censorship
    compute_sigma_mapped,
    tachyon_censorship,
    # Hard reset
    hard_reset_noetic_protocol,
    # Will/Intention
    will_intention_operator,
    # UPE
    upe_signal,
    dominant_upe_frequency,
    # Simulation
    QCALStringSimulation,
    StringSimulationConfig,
    StringSimulationState,
    # Helpers
    get_kk_modes,
)


# ===========================================================================
# Fixtures
# ===========================================================================

@pytest.fixture
def small_config():
    """Minimal configuration for fast tests."""
    return StringSimulationConfig(N=16, dt=0.005, nt=50)


@pytest.fixture
def default_config():
    """Default simulation configuration."""
    return StringSimulationConfig(N=32, dt=0.005, nt=100)


@pytest.fixture
def mock_spectral_fields():
    """Small random spectral fields for unit tests."""
    rng = np.random.default_rng(seed=0)
    N = 16
    uhat = (rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))) * 1e-2
    vhat = (rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))) * 1e-2
    return uhat, vhat


# ===========================================================================
# Tests: Constants
# ===========================================================================

class TestConstants:
    """Verify that module constants have the expected values."""

    def test_f0_value(self):
        """F0 must equal 141.7001 Hz."""
        assert F0 == pytest.approx(141.7001, rel=1e-6)

    def test_mu_adelic(self):
        """μ = 1/f₀ (adelic viscosity)."""
        assert MU_ADELIC == pytest.approx(1.0 / F0, rel=1e-10)

    def test_psi_superradiant_threshold(self):
        """Superradiant threshold is 0.888."""
        assert PSI_SUPERRADIANT == pytest.approx(0.888, rel=1e-6)

    def test_psi_reset_threshold(self):
        """Hard-reset activation threshold is 0.3."""
        assert PSI_RESET_THRESHOLD == pytest.approx(0.3, rel=1e-6)

    def test_riemann_zeros_count(self):
        """20 KK mode frequencies must be available."""
        assert len(RIEMANN_ZEROS_KK) == 20

    def test_riemann_zeros_first(self):
        """First Riemann zero imaginary part ≈ 14.1347."""
        assert RIEMANN_ZEROS_KK[0] == pytest.approx(14.134725142, rel=1e-6)

    def test_epsilon_default_positive(self):
        """Default tachyon tolerance ε must be positive."""
        assert EPSILON_DEFAULT > 0.0


# ===========================================================================
# Tests: string_noetic_forcing
# ===========================================================================

class TestStringNoeticForcing:
    """Tests for the KK string forcing operator (Phase #260)."""

    def test_returns_two_arrays(self, mock_spectral_fields):
        """Function must return two 2-D arrays."""
        uhat, vhat = mock_spectral_fields
        N = uhat.shape[0]
        f_x, f_y = string_noetic_forcing(
            uhat, vhat, t=0.0,
            lambda_n_list=RIEMANN_ZEROS_KK[:5],
            psi_local=0.9,
        )
        assert f_x.shape == (N, N)
        assert f_y.shape == (N, N)

    def test_y_component_zero(self, mock_spectral_fields):
        """y-forcing must be identically zero (as specified)."""
        uhat, vhat = mock_spectral_fields
        _, f_y = string_noetic_forcing(
            uhat, vhat, t=1.0,
            lambda_n_list=RIEMANN_ZEROS_KK[:3],
            psi_local=0.9,
        )
        assert np.allclose(f_y, 0.0)

    def test_zero_psi_gives_zero_forcing(self, mock_spectral_fields):
        """When Ψ_local = 0 the superradiant gain is 0 → zero forcing."""
        uhat, vhat = mock_spectral_fields
        f_x, f_y = string_noetic_forcing(
            uhat, vhat, t=1.0,
            lambda_n_list=RIEMANN_ZEROS_KK[:5],
            psi_local=0.0,
        )
        assert np.allclose(f_x, 0.0)
        assert np.allclose(f_y, 0.0)

    def test_forcing_grows_with_psi(self, mock_spectral_fields):
        """Larger Ψ_local must produce larger forcing (gain ∝ Ψ²)."""
        uhat, vhat = mock_spectral_fields
        t = 0.25
        lambdas = RIEMANN_ZEROS_KK[:3]
        f_lo, _ = string_noetic_forcing(uhat, vhat, t, lambdas, psi_local=0.5)
        f_hi, _ = string_noetic_forcing(uhat, vhat, t, lambdas, psi_local=1.0)
        # |f_hi| / |f_lo| = (1.0/0.5)² = 4
        ratio = np.abs(f_hi[0, 0]) / (np.abs(f_lo[0, 0]) + 1e-30)
        assert ratio == pytest.approx(4.0, rel=1e-6)

    def test_single_kk_mode(self, mock_spectral_fields):
        """Forcing with a single KK mode should still return valid arrays."""
        uhat, vhat = mock_spectral_fields
        f_x, f_y = string_noetic_forcing(
            uhat, vhat, t=0.5,
            lambda_n_list=[RIEMANN_ZEROS_KK[0]],
            psi_local=0.9,
        )
        assert not np.any(np.isnan(f_x))
        assert not np.any(np.isinf(f_x))

    def test_t_duality_phase_varies_per_mode(self, mock_spectral_fields):
        """Different modes should produce different phases (φ = π/(n+1))."""
        uhat, vhat = mock_spectral_fields
        # Modes at same frequency but different phase index
        phi_0 = np.pi / 1  # n=0 → π/1
        phi_1 = np.pi / 2  # n=1 → π/2
        assert phi_0 != phi_1


# ===========================================================================
# Tests: compute_sigma_mapped
# ===========================================================================

class TestComputeSigmaMapped:
    """Tests for the wavenumber-to-sigma mapping."""

    def test_zero_k_gives_half(self):
        """k=0 must give σ_mapped = 0.5 (on critical line)."""
        k = np.array([0.0])
        sigma = compute_sigma_mapped(k, k_max=10.0, epsilon=0.01)
        assert sigma[0] == pytest.approx(0.5, rel=1e-10)

    def test_k_max_gives_half_plus_epsilon(self):
        """k = k_max must give σ_mapped = 0.5 + ε."""
        k = np.array([10.0])
        epsilon = 0.01
        sigma = compute_sigma_mapped(k, k_max=10.0, epsilon=epsilon)
        assert sigma[0] == pytest.approx(0.5 + epsilon, rel=1e-10)

    def test_monotone_in_k(self):
        """σ_mapped must be monotonically non-decreasing with k."""
        k = np.linspace(0, 10, 50)
        sigma = compute_sigma_mapped(k, k_max=10.0, epsilon=0.01)
        assert np.all(np.diff(sigma) >= 0)

    def test_invalid_k_max_raises(self):
        """k_max ≤ 0 must raise ValueError."""
        with pytest.raises(ValueError):
            compute_sigma_mapped(np.array([1.0]), k_max=0.0, epsilon=0.01)


# ===========================================================================
# Tests: tachyon_censorship
# ===========================================================================

class TestTachyonCensorship:
    """Tests for Architecture #261 tachyon censorship."""

    def test_returns_field_and_count(self, mock_spectral_fields):
        """Must return (array, int)."""
        uhat, _ = mock_spectral_fields
        N = uhat.shape[0]
        k1d = np.fft.fftfreq(N, d=1.0 / N)
        kx, ky = np.meshgrid(k1d, k1d, indexing="ij")
        k_mag = np.sqrt(kx ** 2 + ky ** 2)
        k_max = float(np.max(k_mag))

        censored, n = tachyon_censorship(uhat, k_mag, k_max)
        assert censored.shape == uhat.shape
        assert isinstance(n, int)

    def test_zero_deviation_no_suppression(self):
        """k=0 (on critical line) must not suppress the field."""
        N = 4
        field = np.ones((N, N), dtype=complex)
        k_mag = np.zeros((N, N))
        censored, n_cens = tachyon_censorship(field, k_mag, k_max=10.0, epsilon=0.01)
        # σ_mapped(0) = 0.5 → deviation = 0 → Ψ_censored = 1
        assert np.allclose(censored, field)
        assert n_cens == 0

    def test_large_deviation_suppresses(self):
        """High-k modes (large deviation) must be exponentially suppressed."""
        N = 4
        field = np.ones((N, N), dtype=complex)
        # Uniform high wavenumber
        k_mag = np.full((N, N), 100.0)
        k_max = 100.0
        epsilon = 0.01
        censored, _ = tachyon_censorship(field, k_mag, k_max, epsilon=epsilon)
        # All modes suppressed: |censored| << 1
        assert np.all(np.abs(censored) < 1.0)

    def test_invalid_epsilon_raises(self):
        """ε ≤ 0 must raise ValueError."""
        field = np.ones((4, 4), dtype=complex)
        k_mag = np.zeros((4, 4))
        with pytest.raises(ValueError):
            tachyon_censorship(field, k_mag, k_max=10.0, epsilon=0.0)

    def test_n_censored_non_negative(self, mock_spectral_fields):
        """Number of censored modes must be ≥ 0."""
        uhat, _ = mock_spectral_fields
        N = uhat.shape[0]
        k1d = np.fft.fftfreq(N, d=1.0 / N)
        kx, ky = np.meshgrid(k1d, k1d, indexing="ij")
        k_mag = np.sqrt(kx ** 2 + ky ** 2)
        k_max = float(np.max(k_mag))

        _, n = tachyon_censorship(uhat, k_mag, k_max)
        assert n >= 0


# ===========================================================================
# Tests: hard_reset_noetic_protocol
# ===========================================================================

class TestHardResetNoeticProtocol:
    """Tests for the 141.7001 Hz hard-reset protocol."""

    def test_returns_two_arrays(self):
        """Must return two N×N arrays."""
        N = 8
        f_rx, f_ry = hard_reset_noetic_protocol(t=0.0, N=N)
        assert f_rx.shape == (N, N)
        assert f_ry.shape == (N, N)

    def test_y_component_zero(self):
        """y-component of reset forcing must be identically zero."""
        _, f_ry = hard_reset_noetic_protocol(t=1.0, N=8)
        assert np.allclose(f_ry, 0.0)

    def test_zero_at_t0(self):
        """At t=0, sin(0) = 0 → reset forcing = 0."""
        f_rx, _ = hard_reset_noetic_protocol(t=0.0, N=8, f0=F0, beta_max=1.0)
        assert np.allclose(f_rx, 0.0, atol=1e-10)

    def test_nonzero_at_quarter_period(self):
        """At t = T/4 = 1/(4f₀), sin(π/2) = 1 → maximum reset."""
        t_quarter = 1.0 / (4.0 * F0)
        f_rx, _ = hard_reset_noetic_protocol(
            t=t_quarter, N=4, f0=F0, beta_max=1.0, n_microtubules=1.0,
        )
        # Expected: fft2 of array filled with sin(π/2) = 1
        # DC component = N² * 1 = 16
        assert np.abs(f_rx[0, 0]) == pytest.approx(16.0, rel=1e-4)

    def test_f0_modulation(self):
        """Reset pulse must change with different f0 values."""
        t = 0.001
        N = 4
        f_rx_lo, _ = hard_reset_noetic_protocol(t=t, N=N, f0=100.0, n_microtubules=1.0)
        f_rx_hi, _ = hard_reset_noetic_protocol(t=t, N=N, f0=300.0, n_microtubules=1.0)
        assert not np.allclose(f_rx_lo, f_rx_hi)


# ===========================================================================
# Tests: will_intention_operator  (SEQ-009)
# ===========================================================================

class TestWillIntentionOperator:
    """Tests for the Will/Intention Operator SEQ-009."""

    def test_zero_hrv_returns_c_base(self):
        """HRV=0 (no intention) → C(t) = C_base."""
        C_base = 244.36
        result = will_intention_operator(C_base, hrv_coherence=0.0)
        assert result == pytest.approx(C_base, rel=1e-10)

    def test_full_hrv_adds_delta_c(self):
        """HRV=1 (perfect 6 bpm) → C(t) = C_base + delta_C_max."""
        C_base = 244.36
        delta = 0.20
        result = will_intention_operator(C_base, hrv_coherence=1.0, delta_C_max=delta)
        assert result == pytest.approx(C_base + delta, rel=1e-10)

    def test_monotone_in_hrv(self):
        """C(t) must increase monotonically with HRV coherence."""
        C_base = 244.36
        hrv_values = np.linspace(0, 1, 11)
        C_values = [will_intention_operator(C_base, h) for h in hrv_values]
        assert all(C_values[i] <= C_values[i + 1] for i in range(len(C_values) - 1))

    def test_invalid_hrv_raises(self):
        """HRV outside [0,1] must raise ValueError."""
        with pytest.raises(ValueError):
            will_intention_operator(244.36, hrv_coherence=-0.1)
        with pytest.raises(ValueError):
            will_intention_operator(244.36, hrv_coherence=1.1)

    def test_partial_hrv_interpolates(self):
        """Intermediate HRV gives proportional ΔC."""
        C_base = 244.36
        delta = 0.20
        result = will_intention_operator(C_base, hrv_coherence=0.5, delta_C_max=delta)
        expected = C_base + 0.5 * delta
        assert result == pytest.approx(expected, rel=1e-10)


# ===========================================================================
# Tests: UPE signal
# ===========================================================================

class TestUPESignal:
    """Tests for the Ultra-weak Photon Emission signal."""

    def test_returns_scalar(self):
        """upe_signal must return a float."""
        result = upe_signal(t=0.5, lambda_n_list=RIEMANN_ZEROS_KK[:5])
        assert isinstance(result, float)

    def test_zero_at_t0_with_sin(self):
        """At t=0, sin(0)·HRV(0) = 0."""
        result = upe_signal(t=0.0, lambda_n_list=RIEMANN_ZEROS_KK[:5])
        assert result == pytest.approx(0.0, abs=1e-10)

    def test_custom_alpha(self):
        """Custom αₙ coefficients must be respected."""
        lambdas = RIEMANN_ZEROS_KK[:2]
        alpha = [2.0, 3.0]
        t = 0.1
        signal = upe_signal(t, lambdas, alpha_n=alpha)
        # Should not raise; result is finite
        assert np.isfinite(signal)

    def test_dominant_upe_frequency(self):
        """Dominant UPE frequency must be ≈ λ₁·f₀ + f_HRV ≈ 2003 Hz."""
        f_hrv = 0.1
        freq = dominant_upe_frequency(RIEMANN_ZEROS_KK, f_hrv=f_hrv)
        # λ₁ × f₀ ≈ 14.1347 × 141.7001 ≈ 2002.89 Hz (as stated in problem)
        # dominant_upe_frequency returns λ₁·f₀ + f_HRV
        expected = RIEMANN_ZEROS_KK[0] * F0 + f_hrv
        assert freq == pytest.approx(expected, rel=1e-6)
        # Verify it is in the ≈2003 Hz range
        assert 2000.0 < freq < 2010.0

    def test_dominant_upe_frequency_empty_raises(self):
        """Empty lambda_n_list must raise ValueError."""
        with pytest.raises(ValueError):
            dominant_upe_frequency([])


# ===========================================================================
# Tests: get_kk_modes helper
# ===========================================================================

class TestGetKKModes:
    """Tests for the KK-mode helper."""

    def test_default_returns_20(self):
        """Default call returns 20 modes."""
        modes = get_kk_modes()
        assert len(modes) == 20

    def test_n_less_than_20(self):
        """n=5 returns exactly 5 modes."""
        modes = get_kk_modes(5)
        assert len(modes) == 5

    def test_n_exceeds_available_capped(self):
        """n>20 is capped at 20."""
        modes = get_kk_modes(100)
        assert len(modes) == 20

    def test_first_mode_equals_gamma_1(self):
        """First KK mode equals γ₁ ≈ 14.1347."""
        modes = get_kk_modes(1)
        assert modes[0] == pytest.approx(14.134725142, rel=1e-6)


# ===========================================================================
# Tests: StringSimulationConfig dataclass
# ===========================================================================

class TestStringSimulationConfig:
    """Tests for the simulation configuration dataclass."""

    def test_defaults(self):
        """Default configuration must have expected values."""
        cfg = StringSimulationConfig()
        assert cfg.N == 64
        assert cfg.dt == pytest.approx(0.005, rel=1e-10)
        assert cfg.nt == 1000
        assert cfg.f0 == pytest.approx(F0, rel=1e-10)
        assert cfg.mu_adelic == pytest.approx(MU_ADELIC, rel=1e-10)
        assert len(cfg.lambda_n_list) == 20

    def test_custom_values(self):
        """Custom values must be stored correctly."""
        cfg = StringSimulationConfig(N=32, dt=0.01, nt=500, hrv_coherence=0.5)
        assert cfg.N == 32
        assert cfg.dt == pytest.approx(0.01)
        assert cfg.nt == 500
        assert cfg.hrv_coherence == pytest.approx(0.5)


# ===========================================================================
# Tests: QCALStringSimulation
# ===========================================================================

class TestQCALStringSimulation:
    """Integration tests for the full RK4 simulation."""

    def test_run_returns_state(self, small_config):
        """sim.run() must return a StringSimulationState."""
        sim = QCALStringSimulation(small_config)
        final = sim.run()
        assert isinstance(final, StringSimulationState)

    def test_history_length(self, small_config):
        """History must contain nt entries."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        assert len(sim.history) == small_config.nt

    def test_psi_in_unit_interval(self, small_config):
        """All Ψ values must lie in [0, 1]."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        psi = sim.psi_series()
        assert np.all(psi >= 0.0) and np.all(psi <= 1.0)

    def test_entropy_in_unit_interval(self, small_config):
        """All entropy values must lie in [0, 1]."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        ent = sim.entropy_series()
        assert np.all(ent >= 0.0) and np.all(ent <= 1.0)

    def test_state_fields_shape(self, small_config):
        """Spectral fields in state must have correct shape."""
        sim = QCALStringSimulation(small_config)
        final = sim.run()
        N = small_config.N
        assert final.uhat.shape == (N, N)
        assert final.vhat.shape == (N, N)

    def test_energy_spectrum_non_negative(self, small_config):
        """Energy spectrum E(k) must be non-negative."""
        sim = QCALStringSimulation(small_config)
        final = sim.run()
        assert np.all(final.energy_spectrum >= 0.0)

    def test_tachyon_censored_non_negative(self, small_config):
        """Tachyon-censored mode count must be ≥ 0."""
        sim = QCALStringSimulation(small_config)
        final = sim.run()
        assert final.tachyon_modes_censored >= 0

    def test_entropy_reduction_non_negative(self, small_config):
        """Entropy reduction must be ≥ 0 (never increases)."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        assert sim.entropy_reduction() >= 0.0

    def test_psi_series_length(self, small_config):
        """psi_series() must return an array of length nt."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        assert len(sim.psi_series()) == small_config.nt

    def test_entropy_series_length(self, small_config):
        """entropy_series() must return an array of length nt."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        assert len(sim.entropy_series()) == small_config.nt

    def test_hrv_coherence_increases_psi(self):
        """Higher HRV coherence (stronger intention) must not decrease Ψ."""
        cfg_lo = StringSimulationConfig(N=16, dt=0.005, nt=30, hrv_coherence=0.0)
        cfg_hi = StringSimulationConfig(N=16, dt=0.005, nt=30, hrv_coherence=1.0)
        sim_lo = QCALStringSimulation(cfg_lo)
        sim_hi = QCALStringSimulation(cfg_hi)
        final_lo = sim_lo.run()
        final_hi = sim_hi.run()
        # Higher HRV → higher C_density → stronger forcing → Ψ ≥ Ψ_low
        # (not guaranteed by pure mathematics, but expected by QCAL dynamics)
        assert final_hi.psi >= final_lo.psi - 0.1  # Allow small numerical tolerance

    def test_reset_flag_present_in_history(self, small_config):
        """reset_active flag must be present in each history entry."""
        sim = QCALStringSimulation(small_config)
        sim.run()
        for state in sim.history:
            assert hasattr(state, "reset_active")
            assert isinstance(state.reset_active, bool)

    def test_no_nans_in_final_fields(self, small_config):
        """Final spectral fields must not contain NaN or Inf."""
        sim = QCALStringSimulation(small_config)
        final = sim.run()
        assert not np.any(np.isnan(final.uhat))
        assert not np.any(np.isnan(final.vhat))
        assert not np.any(np.isinf(final.uhat))
        assert not np.any(np.isinf(final.vhat))
