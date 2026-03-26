#!/usr/bin/env python3
"""
Tests for the Unified Adelic Wave Equation.

Validates the core mathematical properties of the unified wave equation
    □_Σ Ψ + ω₀² Ψ = ζ'(1/2) · ∇²_Σ Ψ + Tr_distr(e^{itH})
on the compact adelic solenoid Σ = A_Q / Q.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import pytest
import numpy as np

from operators.unified_wave_equation import (
    AdelicSpectralLaplacian,
    SpectralMode,
    UnifiedWaveEquation,
    WaveEvolutionResult,
    solve_unified_wave_equation,
    _GAMMA_TABLE,
    _zeta_prime_half,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def equation():
    """Create a small UnifiedWaveEquation for fast tests."""
    return UnifiedWaveEquation(f0=141.7001, n_modes=10, precision=15)


@pytest.fixture(scope="module")
def evolution(equation):
    """Run a short evolution to obtain a WaveEvolutionResult."""
    return equation.evolve(t_min=0.5, t_max=5.0, n_t=100, n_primes=8, k_max=2, sigma=0.3)


# ---------------------------------------------------------------------------
# AdelicSpectralLaplacian
# ---------------------------------------------------------------------------

class TestAdelicSpectralLaplacian:
    """Test the discrete adelic spectral Laplacian."""

    def test_default_gammas(self):
        lap = AdelicSpectralLaplacian()
        assert len(lap.gammas) == len(_GAMMA_TABLE)

    def test_gammas_positive_and_sorted(self):
        lap = AdelicSpectralLaplacian()
        gammas = lap.gammas
        assert all(g > 0 for g in gammas), "All γ_n must be positive"
        assert gammas == sorted(gammas), "γ_n must be sorted ascending"

    def test_eigenvalue_formula(self):
        lap = AdelicSpectralLaplacian()
        # λ_0 = γ_0² + 1/4
        gamma_0 = lap.gammas[0]
        expected = gamma_0 ** 2 + 0.25
        assert abs(lap.eigenvalue(0) - expected) < 1e-10

    def test_first_eigenvalue(self):
        lap = AdelicSpectralLaplacian()
        # γ_1 ≈ 14.1347
        expected = 14.134725141734693 ** 2 + 0.25
        assert abs(lap.eigenvalue(0) - expected) < 1e-6

    def test_all_eigenvalues_shape(self):
        lap = AdelicSpectralLaplacian()
        lambdas = lap.all_eigenvalues()
        assert lambdas.shape == (len(_GAMMA_TABLE),)
        assert all(lam > 0 for lam in lambdas)

    def test_apply_scaling(self):
        lap = AdelicSpectralLaplacian()
        n_modes = 5
        Psi = np.ones(n_modes)
        result = lap.apply(Psi)
        expected = lap.all_eigenvalues()[:n_modes]
        np.testing.assert_allclose(result, expected, rtol=1e-10)

    def test_custom_gammas(self):
        custom = [14.0, 21.0, 25.0]
        lap = AdelicSpectralLaplacian(gammas=custom)
        assert lap.gammas == sorted(custom)


# ---------------------------------------------------------------------------
# _zeta_prime_half
# ---------------------------------------------------------------------------

class TestZetaPrimeHalf:
    """Test ζ'(1/2) computation."""

    def test_sign_negative(self):
        zp = _zeta_prime_half(precision=15)
        assert zp < 0, "ζ'(1/2) must be negative"

    def test_known_value(self):
        zp = _zeta_prime_half(precision=15)
        assert abs(zp - (-3.9226461392)) < 0.01

    def test_precision_consistency(self):
        zp_low = _zeta_prime_half(precision=15)
        zp_high = _zeta_prime_half(precision=25)
        assert abs(zp_low - zp_high) < 1e-4


# ---------------------------------------------------------------------------
# UnifiedWaveEquation construction
# ---------------------------------------------------------------------------

class TestUnifiedWaveEquationConstruction:
    """Test that the equation is built correctly."""

    def test_initialization(self, equation):
        assert equation.f0 == pytest.approx(141.7001, rel=1e-6)
        assert equation.n_modes == 10
        assert len(equation.modes) == 10

    def test_omega_0_value(self, equation):
        expected = 2 * np.pi * 141.7001
        assert equation.omega_0 == pytest.approx(expected, rel=1e-6)

    def test_modes_type(self, equation):
        for mode in equation.modes:
            assert isinstance(mode, SpectralMode)

    def test_modes_indices_sequential(self, equation):
        for i, mode in enumerate(equation.modes):
            assert mode.n == i

    def test_modes_gammas_from_table(self, equation):
        sorted_gammas = sorted(_GAMMA_TABLE)[:10]
        for mode, expected_gamma in zip(equation.modes, sorted_gammas):
            assert abs(mode.gamma - expected_gamma) < 1e-10

    def test_eigenvalue_formula_for_each_mode(self, equation):
        for mode in equation.modes:
            expected_lam = mode.gamma ** 2 + 0.25
            assert abs(mode.eigenvalue - expected_lam) < 1e-10

    def test_effective_frequencies_array(self, equation):
        freqs = equation.effective_frequencies()
        assert freqs.shape == (10,)
        assert all(f >= 0 for f in freqs)

    def test_spectral_eigenvalues_positive(self, equation):
        lambdas = equation.spectral_eigenvalues()
        assert all(lam > 0 for lam in lambdas)


# ---------------------------------------------------------------------------
# SpectralMode propagation flag
# ---------------------------------------------------------------------------

class TestSpectralModePropagation:
    """Test the propagation flag and effective frequency."""

    def test_propagating_modes_have_positive_omega_sq(self, equation):
        for mode in equation.modes:
            omega_sq = equation.omega_0 ** 2 + mode.eigenvalue * equation.zeta_prime_half
            if omega_sq > 0:
                assert mode.is_propagating
            else:
                assert not mode.is_propagating

    def test_omega_eff_matches_formula(self, equation):
        for mode in equation.modes:
            omega_sq = equation.omega_0 ** 2 + mode.eigenvalue * equation.zeta_prime_half
            expected = float(np.sqrt(abs(omega_sq)))
            assert abs(mode.omega_eff - expected) < 1e-8


# ---------------------------------------------------------------------------
# RH consistency check
# ---------------------------------------------------------------------------

class TestRHConsistency:
    """Test verify_rh_consistency output."""

    def test_keys_present(self, equation):
        result = equation.verify_rh_consistency()
        assert "all_propagating" in result
        assert "n_propagating" in result
        assert "n_evanescent" in result
        assert "min_omega_eff_sq" in result

    def test_counts_sum_to_n_modes(self, equation):
        result = equation.verify_rh_consistency()
        assert result["n_propagating"] + result["n_evanescent"] == equation.n_modes

    def test_min_omega_sq_is_float(self, equation):
        result = equation.verify_rh_consistency()
        assert isinstance(result["min_omega_eff_sq"], float)


# ---------------------------------------------------------------------------
# Source term
# ---------------------------------------------------------------------------

class TestPrimeOrbitSource:
    """Test the distributional trace source S(t)."""

    def test_source_shape(self, evolution):
        assert evolution.source.shape == evolution.t.shape

    def test_source_finite(self, evolution):
        assert np.all(np.isfinite(evolution.source))

    def test_source_peaks_near_log_primes(self, equation):
        """Source should peak near t = log(p) for small primes."""
        t = np.linspace(0.5, 5.0, 1000)
        source = equation._prime_orbit_source(t, n_primes=5, k_max=1, sigma=0.1)
        # log(2) ≈ 0.693, log(3) ≈ 1.099, log(5) ≈ 1.609
        for log_p in [np.log(2), np.log(3), np.log(5)]:
            if t.min() <= log_p <= t.max():
                idx = np.argmin(np.abs(t - log_p))
                local_max = np.max(source[max(0, idx - 20):idx + 20])
                assert local_max > 0, f"Source should be positive near log p = {log_p:.3f}"

    def test_source_non_negative(self, equation):
        """Smoothed source should be non-negative (Gaussians with positive weights)."""
        t = np.linspace(0.5, 5.0, 500)
        source = equation._prime_orbit_source(t, n_primes=5, k_max=1, sigma=0.3)
        assert np.all(source >= -1e-12)


# ---------------------------------------------------------------------------
# Wave evolution
# ---------------------------------------------------------------------------

class TestWaveEvolution:
    """Test the WaveEvolutionResult from equation.evolve."""

    def test_result_type(self, evolution):
        assert isinstance(evolution, WaveEvolutionResult)

    def test_status_ok(self, evolution):
        assert evolution.status == "OK"

    def test_Psi_shape(self, evolution, equation):
        assert evolution.Psi.shape == (equation.n_modes, len(evolution.t))

    def test_t_grid_monotone(self, evolution):
        assert np.all(np.diff(evolution.t) > 0)

    def test_Psi_finite(self, evolution):
        assert np.all(np.isfinite(evolution.Psi))

    def test_energy_finite(self, evolution):
        assert np.all(np.isfinite(evolution.total_energy))

    def test_energy_non_negative(self, evolution):
        assert np.all(evolution.total_energy >= 0)

    def test_parameters_stored(self, evolution):
        params = evolution.parameters
        assert "f0" in params
        assert "omega_0" in params
        assert "zeta_prime_half" in params
        assert "n_modes" in params

    def test_modes_count_in_result(self, evolution, equation):
        assert len(evolution.modes) == equation.n_modes

    def test_Psi_initial_amplitude(self, equation):
        """First sample of each mode should be close to A0 = 1."""
        res = equation.evolve(t_min=0.0, t_max=5.0, n_t=100, sigma=0.5)
        # At t=0 (shifted), homogeneous part = A0 * cos(0) = A0
        np.testing.assert_allclose(res.Psi[:, 0], 1.0, atol=0.5)


# ---------------------------------------------------------------------------
# Wave equation residual
# ---------------------------------------------------------------------------

class TestWaveEquationResidual:
    """Test the residual checker."""

    def test_residual_homogeneous(self, equation):
        """For cos(Ω t) the residual Ψ''+Ω²Ψ ≈ 0; verify relative to Ω²."""
        mode = equation.modes[0]
        n_pts = 1000
        t = np.linspace(0.0, 2.0 * np.pi / mode.omega_eff, n_pts)
        Psi = np.cos(mode.omega_eff * t)
        residual = equation.wave_equation_residual(t, Psi, mode_index=0)
        # Relative error: |residual| / Ω² should be small in the interior
        interior = residual[10:-10]
        rel_err = np.max(np.abs(interior)) / (mode.omega_eff ** 2)
        assert rel_err < 0.01, (
            f"Relative residual too large: {rel_err:.4e} (max interior |res|={np.max(np.abs(interior)):.4f})"
        )

    def test_residual_shape(self, equation, evolution):
        Psi_0 = evolution.Psi[0]
        residual = equation.wave_equation_residual(evolution.t, Psi_0, mode_index=0)
        assert residual.shape == evolution.t.shape


# ---------------------------------------------------------------------------
# Convenience wrapper
# ---------------------------------------------------------------------------

class TestSolveUnifiedWaveEquation:
    """Test the top-level convenience function."""

    def test_returns_result(self):
        result = solve_unified_wave_equation(
            t_min=0.5, t_max=3.0, n_t=50, n_modes=5, n_primes=5, k_max=1
        )
        assert isinstance(result, WaveEvolutionResult)
        assert result.status == "OK"

    def test_custom_f0(self):
        result = solve_unified_wave_equation(f0=141.7001, n_modes=5, n_t=50)
        assert result.parameters["f0"] == pytest.approx(141.7001, rel=1e-6)

    def test_output_shapes_consistent(self):
        result = solve_unified_wave_equation(
            t_min=0.5, t_max=4.0, n_t=80, n_modes=8
        )
        assert result.Psi.shape == (8, 80)
        assert result.t.shape == (80,)
        assert result.source.shape == (80,)
        assert result.total_energy.shape == (80,)
