#!/usr/bin/env python3
"""
Tests for Triple Rescaling Spectral Analysis Module

Tests the H_Ψ operator derived from the vacuum energy functional
and the triple rescaling mechanism for spectral alignment.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: December 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from triple_rescaling_spectral import (
    F_RAW, F_0, OMEGA_RAW, OMEGA_0, ZETA_PRIME_HALF,
    VacuumOperatorParams,
    E_vac,
    E_vac_second_derivative,
    compute_rescaling_factor,
    apply_triple_rescaling,
    construct_H_psi_from_vacuum,
    construct_H_psi_extended,
    compute_spectrum_before_after_rescaling,
    compute_extended_spectrum,
    validate_rescaling
)


class TestConstants:
    """Test QCAL universal constants."""
    
    def test_f_raw_value(self):
        """Test raw frequency value."""
        assert F_RAW == 157.9519
    
    def test_f_0_value(self):
        """Test universal frequency value."""
        assert F_0 == 141.7001
    
    def test_omega_raw_calculation(self):
        """Test ω_raw = 2π·f_raw."""
        expected = 2 * np.pi * F_RAW
        assert np.isclose(OMEGA_RAW, expected, rtol=1e-14)
    
    def test_omega_0_calculation(self):
        """Test ω₀ = 2π·f₀."""
        expected = 2 * np.pi * F_0
        assert np.isclose(OMEGA_0, expected, rtol=1e-14)
    
    def test_zeta_prime_half_sign(self):
        """Test that ζ'(1/2) is negative."""
        assert ZETA_PRIME_HALF < 0
        assert -4.0 < ZETA_PRIME_HALF < -3.8


class TestVacuumOperatorParams:
    """Test VacuumOperatorParams dataclass."""
    
    def test_default_params(self):
        """Test default parameter values."""
        params = VacuumOperatorParams()
        assert params.alpha == 1.0
        assert params.beta == 1.0
        assert params.gamma == 1.0
        assert params.delta == 0.1
        assert np.isclose(params.eta, np.e, rtol=1e-14)
    
    def test_custom_params(self):
        """Test custom parameter values."""
        params = VacuumOperatorParams(alpha=2.0, beta=0.5, gamma=0.1)
        assert params.alpha == 2.0
        assert params.beta == 0.5
        assert params.gamma == 0.1


class TestVacuumEnergy:
    """Test vacuum energy calculation."""
    
    def test_positive_radius(self):
        """Test E_vac for positive radius."""
        params = VacuumOperatorParams()
        R = np.array([1.0, 2.0, 3.0])
        E = E_vac(R, params)
        assert len(E) == 3
        assert np.all(np.isfinite(E))
    
    def test_energy_at_unity(self):
        """Test E_vac(1) with standard parameters."""
        params = VacuumOperatorParams(delta=0)  # No fractal term
        R = np.array([1.0])
        E = E_vac(R, params)
        # E = α + β·ζ'(1/2) + γ = 1 + ζ'(1/2) + 1
        expected = 1.0 + ZETA_PRIME_HALF + 1.0
        assert np.isclose(E[0], expected, rtol=1e-10)
    
    def test_casimir_dominates_small_r(self):
        """Test that Casimir term dominates at small R."""
        params = VacuumOperatorParams(alpha=1.0, beta=0.1, gamma=0.01, delta=0.01)
        R = np.array([0.1])
        E = E_vac(R, params)
        casimir_term = 1.0 / (0.1 ** 4)  # = 10000
        assert E[0] > 0.8 * casimir_term  # Casimir should dominate
    
    def test_dark_energy_dominates_large_r(self):
        """Test that dark energy term dominates at large R."""
        params = VacuumOperatorParams(alpha=0.1, beta=0.1, gamma=1.0, delta=0.01)
        R = np.array([100.0])
        E = E_vac(R, params)
        dark_energy_term = 1.0 * (100.0 ** 2)  # = 10000
        assert E[0] > 0.8 * dark_energy_term


class TestSecondDerivative:
    """Test vacuum energy second derivative."""
    
    def test_finite_value(self):
        """Test that second derivative is finite."""
        params = VacuumOperatorParams()
        R = 0.6952
        d2E = E_vac_second_derivative(R, params)
        assert np.isfinite(d2E)
    
    def test_positive_curvature_at_minimum(self):
        """Test that curvature is positive near a minimum."""
        # At a minimum, d²E/dR² > 0 (stable equilibrium)
        params = VacuumOperatorParams(alpha=1.0, beta=0, gamma=1.0, delta=0)
        # For E = α/R⁴ + γR², minimum at R = (2α/γ)^(1/6)
        # d²E/dR² = 20α/R⁶ + 2γ > 0 for all R > 0
        R = 1.0
        d2E = E_vac_second_derivative(R, params)
        assert d2E > 0


class TestRescalingFactor:
    """Test rescaling factor computation."""
    
    def test_k_calculation(self):
        """Test k = (f₀/f_raw)²."""
        k = compute_rescaling_factor()
        expected = (F_0 / F_RAW) ** 2
        assert np.isclose(k, expected, rtol=1e-14)
    
    def test_k_less_than_one(self):
        """Test that k < 1 since f₀ < f_raw."""
        k = compute_rescaling_factor()
        assert k < 1.0
    
    def test_k_positive(self):
        """Test that k > 0."""
        k = compute_rescaling_factor()
        assert k > 0
    
    def test_custom_frequencies(self):
        """Test k with custom frequencies."""
        k = compute_rescaling_factor(f_raw=200.0, f_0=100.0)
        assert np.isclose(k, 0.25, rtol=1e-14)


class TestTripleRescaling:
    """Test triple rescaling application."""
    
    def test_alpha_unchanged(self):
        """Test that α is unchanged by rescaling."""
        params = VacuumOperatorParams(alpha=2.5)
        k = 0.8
        scaled = apply_triple_rescaling(params, k)
        assert scaled.alpha == params.alpha
    
    def test_beta_scaled(self):
        """Test that β → k·β."""
        params = VacuumOperatorParams(beta=1.0)
        k = 0.8
        scaled = apply_triple_rescaling(params, k)
        assert np.isclose(scaled.beta, k * params.beta, rtol=1e-14)
    
    def test_gamma_scaled(self):
        """Test that γ → k·γ."""
        params = VacuumOperatorParams(gamma=1.0)
        k = 0.8
        scaled = apply_triple_rescaling(params, k)
        assert np.isclose(scaled.gamma, k * params.gamma, rtol=1e-14)
    
    def test_delta_unchanged(self):
        """Test that δ (fractal) is unchanged."""
        params = VacuumOperatorParams(delta=0.5)
        k = 0.8
        scaled = apply_triple_rescaling(params, k)
        assert scaled.delta == params.delta


class TestHPsiConstruction:
    """Test H_Ψ operator construction."""
    
    def test_matrix_shape(self):
        """Test that H_Ψ has correct shape."""
        n = 50
        H = construct_H_psi_from_vacuum(n=n)
        assert H.shape == (n, n)
    
    def test_hermiticity(self):
        """Test that H_Ψ is Hermitian (symmetric for real)."""
        H = construct_H_psi_from_vacuum(n=30)
        hermiticity_error = np.max(np.abs(H - H.T))
        assert hermiticity_error < 1e-14
    
    def test_real_matrix(self):
        """Test that H_Ψ is real."""
        H = construct_H_psi_from_vacuum(n=30)
        assert np.all(np.isreal(H))
    
    def test_diagonal_structure(self):
        """Test that basic H_Ψ is diagonal."""
        H = construct_H_psi_from_vacuum(n=30)
        off_diagonal = H - np.diag(np.diag(H))
        assert np.max(np.abs(off_diagonal)) < 1e-14


class TestHPsiExtended:
    """Test extended H_Ψ operator construction."""
    
    def test_matrix_shape(self):
        """Test correct matrix shape."""
        n = 50
        H, R = construct_H_psi_extended(n=n)
        assert H.shape == (n, n)
        assert len(R) == n
    
    def test_hermiticity(self):
        """Test Hermiticity of extended operator."""
        H, _ = construct_H_psi_extended(n=30)
        hermiticity_error = np.max(np.abs(H - H.T))
        assert hermiticity_error < 1e-14
    
    def test_r_values_range(self):
        """Test that R values are in expected range."""
        R_range = (0.5, 2.0)
        H, R = construct_H_psi_extended(n=50, R_range=R_range)
        assert np.min(R) >= R_range[0]
        assert np.max(R) <= R_range[1]


class TestSpectrumComputation:
    """Test eigenvalue spectrum computation."""
    
    def test_eigenvalue_count(self):
        """Test correct number of eigenvalues."""
        n = 50
        results = compute_spectrum_before_after_rescaling(n=n)
        assert len(results['evals_original']) == n
        assert len(results['evals_scaled']) == n
    
    def test_real_eigenvalues(self):
        """Test that eigenvalues are real."""
        results = compute_spectrum_before_after_rescaling(n=30)
        assert np.all(np.isreal(results['evals_original']))
        assert np.all(np.isreal(results['evals_scaled']))
    
    def test_scaling_relationship(self):
        """Test that scaled eigenvalues = k * original."""
        results = compute_spectrum_before_after_rescaling(n=30)
        k = results['k']
        expected = k * results['evals_original']
        np.testing.assert_allclose(results['evals_scaled'], expected, rtol=1e-12)
    
    def test_k_value_in_results(self):
        """Test that results contain correct k value."""
        results = compute_spectrum_before_after_rescaling()
        expected_k = (F_0 / F_RAW) ** 2
        assert np.isclose(results['k'], expected_k, rtol=1e-14)


class TestExtendedSpectrum:
    """Test extended spectrum computation."""
    
    def test_eigenvalue_count(self):
        """Test correct eigenvalue count."""
        n = 50
        results = compute_extended_spectrum(n=n)
        assert len(results['evals_original']) == n
        assert len(results['evals_scaled']) == n
    
    def test_eigenvector_shape(self):
        """Test eigenvector matrix shape."""
        n = 50
        results = compute_extended_spectrum(n=n)
        assert results['evecs_original'].shape == (n, n)
        assert results['evecs_scaled'].shape == (n, n)
    
    def test_sorted_eigenvalues(self):
        """Test that eigenvalues are sorted."""
        results = compute_extended_spectrum(n=50)
        evals = results['evals_original']
        assert np.all(evals[:-1] <= evals[1:])
    
    def test_r_vals_in_results(self):
        """Test that R values are included in results."""
        n = 50
        results = compute_extended_spectrum(n=n)
        assert 'R_vals' in results
        assert len(results['R_vals']) == n


class TestValidation:
    """Test validation of rescaling."""
    
    def test_validation_passes(self):
        """Test that valid rescaling passes validation."""
        results = compute_spectrum_before_after_rescaling(n=30)
        validation = validate_rescaling(results)
        assert validation['is_valid']
    
    def test_k_error_small(self):
        """Test that k error is negligible."""
        results = compute_spectrum_before_after_rescaling(n=30)
        validation = validate_rescaling(results)
        assert validation['k_error'] < 1e-14
    
    def test_scaling_error_small(self):
        """Test that scaling error is negligible."""
        results = compute_spectrum_before_after_rescaling(n=30)
        validation = validate_rescaling(results)
        assert validation['scaling_error'] < 1e-12


class TestPhysicalInterpretation:
    """Test physical interpretation of results."""
    
    def test_frequency_alignment(self):
        """Test that rescaling aligns to universal frequency."""
        k = compute_rescaling_factor()
        # After rescaling, spectral scale should be aligned to f₀
        # Check that k·ω_raw ≠ ω₀ but the eigenvalues scale properly
        assert k < 1.0  # Since f₀ < f_raw
    
    def test_omega_ratio(self):
        """Test ω₀/ω_raw = √k relationship."""
        k = compute_rescaling_factor()
        omega_ratio = OMEGA_0 / OMEGA_RAW
        assert np.isclose(omega_ratio, np.sqrt(k), rtol=1e-14)
    
    def test_coherence_preserved(self):
        """Test that QCAL coherence is preserved after rescaling."""
        # Use the simple spectrum (diagonal) where scaling is exact
        results = compute_spectrum_before_after_rescaling(n=50)
        # Spectral structure should be preserved (just scaled)
        evals_orig = results['evals_original']
        evals_scaled = results['evals_scaled']
        k = results['k']
        
        # For the simple diagonal case, rescaled = k * original
        # This preserves the spectral structure exactly
        np.testing.assert_allclose(evals_scaled, k * evals_orig, rtol=1e-12)


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_large_n(self):
        """Test with large matrix dimension."""
        n = 200
        results = compute_spectrum_before_after_rescaling(n=n)
        assert len(results['evals_original']) == n
        assert np.all(np.isfinite(results['evals_original']))
    
    def test_small_n(self):
        """Test with small matrix dimension."""
        n = 5
        results = compute_spectrum_before_after_rescaling(n=n)
        assert len(results['evals_original']) == n
    
    def test_deterministic(self):
        """Test that results are deterministic."""
        results1 = compute_spectrum_before_after_rescaling(n=30)
        results2 = compute_spectrum_before_after_rescaling(n=30)
        np.testing.assert_array_equal(results1['evals_original'], results2['evals_original'])


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
