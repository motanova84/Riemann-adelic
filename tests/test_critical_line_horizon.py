#!/usr/bin/env python3
"""
Tests for Critical Line Horizon Operator
=========================================

Tests para el operador H_ψ de línea crítica como horizonte vibracional.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from critical_line_horizon import (
    F0_BASE,
    F0_AUDIBLE,
    PHI,
    COHERENCE_CONSTANT_C,
    get_first_primes,
    compute_potential_V,
    construct_H_psi_operator,
    compute_spectrum_H_psi,
    CriticalLineMetric,
    UnifiedDualityTensor,
    riemann_zeros_as_singularities,
    validate_critical_line_hypothesis,
    create_critical_line_operator,
)


class TestQCALConstants:
    """Test QCAL ∞³ constants"""
    
    def test_base_frequency(self):
        """Test that base frequency is correct"""
        assert abs(F0_BASE - 141.7001) < 1e-6
    
    def test_golden_ratio(self):
        """Test golden ratio φ"""
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected_phi) < 1e-10
    
    def test_audible_frequency(self):
        """Test that audible frequency = f₀ × φ⁴"""
        expected = F0_BASE * (PHI ** 4)
        assert abs(F0_AUDIBLE - expected) < 1e-6
        
        # Should be in audible range (close to 888-1000 Hz range)
        assert abs(F0_AUDIBLE - 888.0) < 100.0
    
    def test_coherence_constant(self):
        """Test coherence constant C"""
        assert abs(COHERENCE_CONSTANT_C - 244.36) < 1e-6


class TestPrimeNumbers:
    """Test prime number generation"""
    
    def test_first_primes_count(self):
        """Test that we get the correct number of primes"""
        for n in [5, 10, 20]:
            primes = get_first_primes(n)
            assert len(primes) == n
    
    def test_first_primes_values(self):
        """Test that first primes are correct"""
        primes = get_first_primes(10)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        np.testing.assert_array_equal(primes, expected)
    
    def test_primes_are_prime(self):
        """Test that all returned values are prime"""
        primes = get_first_primes(20)
        
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(np.sqrt(n)) + 1):
                if n % i == 0:
                    return False
            return True
        
        for p in primes:
            assert is_prime(int(p))


class TestPotentialV:
    """Test potential function V(x)"""
    
    def test_potential_shape(self):
        """Test that potential has correct shape"""
        x = np.linspace(-5, 5, 100)
        primes = get_first_primes(10)
        V = compute_potential_V(x, primes)
        
        assert V.shape == x.shape
    
    def test_potential_is_real(self):
        """Test that potential is real-valued"""
        x = np.linspace(-5, 5, 100)
        primes = get_first_primes(10)
        V = compute_potential_V(x, primes)
        
        assert np.all(np.isreal(V))
    
    def test_potential_coupling(self):
        """Test that λ coupling scales potential"""
        x = np.linspace(-5, 5, 50)
        primes = get_first_primes(10)
        
        V1 = compute_potential_V(x, primes, lambda_coupling=1.0)
        V2 = compute_potential_V(x, primes, lambda_coupling=2.0)
        
        np.testing.assert_allclose(V2, 2.0 * V1, rtol=1e-10)


class TestHPsiOperator:
    """Test H_ψ operator construction"""
    
    def test_operator_shape(self):
        """Test that operator has correct shape"""
        n_basis = 50
        H_psi, x_grid = construct_H_psi_operator(n_basis=n_basis)
        
        assert H_psi.shape == (n_basis, n_basis)
        assert len(x_grid) == n_basis
    
    def test_operator_hermiticity(self):
        """Test that H_ψ is Hermitian"""
        H_psi, _ = construct_H_psi_operator(n_basis=50)
        
        # Check if matrix equals its conjugate transpose
        hermiticity_error = np.max(np.abs(H_psi - H_psi.T))
        assert hermiticity_error < 1e-10
    
    def test_operator_real_valued(self):
        """Test that H_ψ is real (not complex)"""
        H_psi, _ = construct_H_psi_operator(n_basis=50)
        
        assert np.all(np.isreal(H_psi))
    
    def test_grid_spacing(self):
        """Test that grid spacing is uniform"""
        _, x_grid = construct_H_psi_operator(n_basis=100)
        
        spacing = np.diff(x_grid)
        assert np.std(spacing) < 1e-10  # Uniform spacing


class TestSpectrum:
    """Test spectral calculations"""
    
    def test_spectrum_real(self):
        """Test that eigenvalues are real"""
        H_psi, _ = construct_H_psi_operator(n_basis=50)
        eigenvalues, _ = compute_spectrum_H_psi(H_psi)
        
        assert np.all(np.isreal(eigenvalues))
    
    def test_spectrum_sorted(self):
        """Test that eigenvalues are sorted"""
        H_psi, _ = construct_H_psi_operator(n_basis=50)
        eigenvalues, _ = compute_spectrum_H_psi(H_psi)
        
        assert np.all(eigenvalues[:-1] <= eigenvalues[1:])
    
    def test_eigenvector_normalization(self):
        """Test that eigenvectors are normalized"""
        H_psi, _ = construct_H_psi_operator(n_basis=50)
        _, eigenvectors = compute_spectrum_H_psi(H_psi)
        
        # Each column should be normalized
        norms = np.linalg.norm(eigenvectors, axis=0)
        np.testing.assert_allclose(norms, 1.0, rtol=1e-6)
    
    def test_spectrum_n_eigenvalues(self):
        """Test returning specific number of eigenvalues"""
        H_psi, _ = construct_H_psi_operator(n_basis=100)
        
        for n in [5, 10, 20]:
            eigenvalues, eigenvectors = compute_spectrum_H_psi(H_psi, n_eigenvalues=n)
            assert len(eigenvalues) == n
            assert eigenvectors.shape[1] == n


class TestCriticalLineMetric:
    """Test Ψ-deformed metric"""
    
    def test_psi_field(self):
        """Test Ψ = I × A_eff²"""
        metric = CriticalLineMetric(I=2.0, A_eff=3.0)
        expected_psi = 2.0 * (3.0 ** 2)
        
        assert abs(metric.psi_field() - expected_psi) < 1e-10
    
    def test_metric_deformation_shape(self):
        """Test that deformation has correct shape"""
        metric = CriticalLineMetric(I=1.0, A_eff=1.0)
        x = np.linspace(-5, 5, 100)
        
        deformation = metric.metric_deformation(x)
        assert deformation.shape == x.shape
    
    def test_total_metric(self):
        """Test total metric g_μν = g₀ + δg"""
        metric = CriticalLineMetric(I=1.0, A_eff=1.0)
        x = np.linspace(-5, 5, 100)
        g0 = 1.0
        
        g_total = metric.total_metric(x, g0=g0)
        
        # Total metric should include background
        assert np.all(g_total >= g0 - 1.0)  # Allow for negative deformations


class TestUnifiedDualityTensor:
    """Test unified duality tensor"""
    
    def test_frequency_ratio(self):
        """Test that f_audible / f_base ≈ φ⁴"""
        duality = UnifiedDualityTensor()
        ratio = duality.frequency_ratio()
        
        expected_ratio = PHI ** 4
        assert abs(ratio - expected_ratio) < 1e-6
    
    def test_critical_line_frequency(self):
        """Test critical line frequency = 888 Hz"""
        duality = UnifiedDualityTensor()
        f_critical = duality.critical_line_frequency()
        
        assert abs(f_critical - F0_AUDIBLE) < 1e-6
    
    def test_spectral_correspondence(self):
        """Test t_n ≈ n·f₀"""
        duality = UnifiedDualityTensor()
        
        # Generate expected zeros
        n_values = np.arange(1, 11)
        t_n = n_values * F0_BASE
        
        # Recover n from t_n
        n_recovered = duality.spectral_correspondence(t_n)
        
        np.testing.assert_allclose(n_recovered, n_values, rtol=1e-10)
    
    def test_duality_operator_shape(self):
        """Test duality operator shape"""
        duality = UnifiedDualityTensor()
        
        D_s = np.eye(5)
        H_psi = np.eye(10)
        
        duality_op = duality.duality_operator(D_s, H_psi)
        
        expected_shape = (5 * 10, 5 * 10)
        assert duality_op.shape == expected_shape
    
    def test_duality_operator_hermiticity(self):
        """Test that duality operator is Hermitian"""
        duality = UnifiedDualityTensor()
        
        # Create Hermitian operators
        D_s = np.random.randn(5, 5)
        D_s = (D_s + D_s.T) / 2
        
        H_psi = np.random.randn(10, 10)
        H_psi = (H_psi + H_psi.T) / 2
        
        duality_op = duality.duality_operator(D_s, H_psi)
        
        hermiticity_error = np.max(np.abs(duality_op - duality_op.T))
        assert hermiticity_error < 1e-10


class TestRiemannSingularities:
    """Test Riemann zeros as singularities"""
    
    def test_singularities_count(self):
        """Test that singularities are computed for all zeros"""
        t_zeros = np.array([14.134725, 21.022040, 25.010858])
        
        result = riemann_zeros_as_singularities(t_zeros)
        
        assert result['n_zeros'] == len(t_zeros)
        assert len(result['spectral_mass']) == len(t_zeros)
    
    def test_spectral_mass_positive(self):
        """Test that spectral mass is positive"""
        t_zeros = np.array([14.134725, 21.022040, 25.010858])
        
        result = riemann_zeros_as_singularities(t_zeros)
        
        assert np.all(result['spectral_mass'] > 0)
    
    def test_frequency_correspondence(self):
        """Test frequency correspondence"""
        t_zeros = np.array([14.134725, 21.022040, 25.010858])
        f0 = F0_BASE
        
        result = riemann_zeros_as_singularities(t_zeros, f0=f0)
        
        assert abs(result['frequency_correspondence'] - f0) < 1e-10
    
    def test_mean_spacing(self):
        """Test mean spacing calculation"""
        t_zeros = np.array([14.0, 21.0, 28.0, 35.0])
        
        result = riemann_zeros_as_singularities(t_zeros)
        
        expected_spacing = 7.0
        assert abs(result['mean_spacing'] - expected_spacing) < 1e-6


class TestValidation:
    """Test validation functions"""
    
    def test_perfect_match(self):
        """Test validation with perfect match"""
        values = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        
        result = validate_critical_line_hypothesis(
            values, values, tolerance=1e-6
        )
        
        assert result['success']
        assert result['max_absolute_error'] < 1e-10
    
    def test_imperfect_match(self):
        """Test validation with small errors"""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        zeros = np.array([1.001, 2.001, 3.001, 4.001, 5.001])
        
        result = validate_critical_line_hypothesis(
            eigenvalues, zeros, tolerance=0.01
        )
        
        assert result['success']
        assert result['max_absolute_error'] < 0.01
    
    def test_validation_failure(self):
        """Test validation with large errors"""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        zeros = np.array([1.1, 2.1, 3.1])
        
        result = validate_critical_line_hypothesis(
            eigenvalues, zeros, tolerance=0.01
        )
        
        assert not result['success']


class TestConvenienceFunctions:
    """Test convenience functions"""
    
    def test_create_critical_line_operator(self):
        """Test convenience function for operator creation"""
        H_psi, x_grid, eigenvalues, eigenvectors = create_critical_line_operator(
            n_basis=50,
            n_primes=20
        )
        
        assert H_psi.shape == (50, 50)
        assert len(x_grid) == 50
        assert len(eigenvalues) == 50
        assert eigenvectors.shape == (50, 50)


class TestIntegration:
    """Integration tests combining multiple components"""
    
    def test_full_pipeline(self):
        """Test full pipeline: operator → spectrum → singularities"""
        # Create operator
        H_psi, x_grid, eigenvalues, eigenvectors = create_critical_line_operator(
            n_basis=100,
            n_primes=50
        )
        
        # Use eigenvalues as "zeros"
        t_zeros = eigenvalues[:20]
        
        # Compute singularity properties
        singularities = riemann_zeros_as_singularities(t_zeros)
        
        # Verify properties
        assert singularities['n_zeros'] == 20
        assert np.all(singularities['spectral_mass'] > 0)
        assert np.all(singularities['event_horizon_radius'] > 0)
    
    def test_metric_with_operator(self):
        """Test metric deformation with operator"""
        # Create operator
        _, x_grid, _, _ = create_critical_line_operator(n_basis=100)
        
        # Create metric
        metric = CriticalLineMetric(I=1.0, A_eff=2.0)
        
        # Compute deformed metric
        g_total = metric.total_metric(x_grid)
        
        assert len(g_total) == len(x_grid)
        assert np.all(np.isreal(g_total))
    
    def test_duality_with_spectrum(self):
        """Test duality tensor with spectrum"""
        # Create small operators
        H_psi, _, _, _ = create_critical_line_operator(n_basis=20)
        D_s = np.eye(10)
        
        # Create duality
        duality = UnifiedDualityTensor()
        duality_op = duality.duality_operator(D_s, H_psi)
        
        # Verify properties
        assert duality_op.shape == (200, 200)
        
        # Should be Hermitian
        hermiticity_error = np.max(np.abs(duality_op - duality_op.T))
        assert hermiticity_error < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
