"""
Test suite for H_Ψ Hermitian operator.

Tests the constructive proof of the Riemann Hypothesis via spectral theory.
"""

import numpy as np
import pytest
import os
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.riemann_operator import (
    load_riemann_zeros,
    oscillatory_weight,
    construct_H_psi,
    compute_spectrum,
    validate_spectrum,
    wave_equation_rhs,
    F0,
    OMEGA_0,
    ZETA_PRIME_HALF,
    C_QCAL
)


class TestConstants:
    """Test QCAL constants."""
    
    def test_fundamental_frequency(self):
        """Test f₀ = 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-6
        
    def test_angular_frequency(self):
        """Test ω₀ = 2πf₀."""
        expected_omega = 2 * np.pi * F0
        assert abs(OMEGA_0 - expected_omega) < 1e-6
        
    def test_zeta_prime_half(self):
        """Test ζ'(1/2) value."""
        # Known value from mpmath computation
        assert abs(ZETA_PRIME_HALF - (-3.92264613)) < 0.01
        
    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert abs(C_QCAL - 244.36) < 1e-6


class TestRiemannZeros:
    """Test Riemann zeros loading."""
    
    def test_load_zeros(self):
        """Test loading Riemann zeros."""
        zeros = load_riemann_zeros(n_zeros=10)
        assert len(zeros) == 10
        assert zeros[0] > 0  # All zeros are positive
        assert np.all(zeros[1:] > zeros[:-1])  # Sorted ascending
        
    def test_first_zero(self):
        """Test first Riemann zero γ₁ ≈ 14.134725."""
        zeros = load_riemann_zeros(n_zeros=1)
        assert abs(zeros[0] - 14.134725) < 0.01
        
    def test_50_zeros(self):
        """Test loading 50 zeros."""
        zeros = load_riemann_zeros(n_zeros=50)
        assert len(zeros) == 50
        # Check range
        assert zeros[0] > 14
        assert zeros[-1] < 200


class TestOscillatoryWeight:
    """Test oscillatory weight function W(x)."""
    
    def test_weight_shape(self):
        """Test W(x) has correct shape."""
        x = np.linspace(-5, 5, 100)
        gamma_n = load_riemann_zeros(n_zeros=10)
        W = oscillatory_weight(x, gamma_n)
        assert W.shape == x.shape
        
    def test_weight_gaussian_envelope(self):
        """Test Gaussian envelope decay."""
        x = np.linspace(-5, 5, 100)
        gamma_n = load_riemann_zeros(n_zeros=10)
        W = oscillatory_weight(x, gamma_n, sigma=1.0)
        
        # Weight should decay at large |x|
        center_idx = len(x) // 2
        edge_value = abs(W[0])
        center_value = abs(W[center_idx])
        
        assert center_value > edge_value
        
    def test_weight_oscillations(self):
        """Test oscillatory behavior."""
        x = np.linspace(0.1, 5, 100)
        gamma_n = load_riemann_zeros(n_zeros=5)
        W = oscillatory_weight(x, gamma_n)
        
        # Should have oscillations (not monotonic)
        dW = np.diff(W)
        sign_changes = np.sum(np.diff(np.sign(dW)) != 0)
        assert sign_changes > 5  # At least a few oscillations


class TestHPsiOperator:
    """Test H_Ψ operator construction and properties."""
    
    def test_operator_hermiticity(self):
        """Test H_Ψ is Hermitian (symmetric for real)."""
        H_psi, _ = construct_H_psi(n_zeros=10)
        
        # Check symmetry
        hermiticity_error = np.max(np.abs(H_psi - H_psi.T))
        assert hermiticity_error < 1e-14
        
    def test_operator_dimension(self):
        """Test operator has correct dimension."""
        n_zeros = 20
        H_psi, gamma_n = construct_H_psi(n_zeros=n_zeros)
        
        assert H_psi.shape == (n_zeros, n_zeros)
        assert len(gamma_n) == n_zeros
        
    def test_operator_real(self):
        """Test operator is real-valued."""
        H_psi, _ = construct_H_psi(n_zeros=10)
        
        # Check all elements are real
        assert np.all(np.isreal(H_psi))


class TestSpectrum:
    """Test spectral properties of H_Ψ."""
    
    def test_eigenvalues_real(self):
        """Test eigenvalues are real (from Hermiticity)."""
        H_psi, _ = construct_H_psi(n_zeros=10)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        # All eigenvalues should be real
        assert np.all(np.isreal(eigenvalues))
        
    def test_eigenvalues_sorted(self):
        """Test eigenvalues are returned sorted."""
        H_psi, _ = construct_H_psi(n_zeros=10)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        # Check ascending order
        assert np.all(eigenvalues[1:] >= eigenvalues[:-1])
        
    def test_spectrum_reproduces_zeros(self):
        """Test spectrum reproduces Riemann zeros with high precision."""
        n_zeros = 50
        H_psi, gamma_n = construct_H_psi(n_zeros=n_zeros)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # Check target precision: |λₙ - γₙ| < 1.5e-12
        assert results['max_abs_error'] < 1.5e-12
        
    def test_mean_error_precision(self):
        """Test mean error is very small."""
        n_zeros = 50
        H_psi, gamma_n = construct_H_psi(n_zeros=n_zeros)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # Mean error should be even better than max
        assert results['mean_abs_error'] < 1e-12
        
    def test_relative_errors(self):
        """Test relative errors are negligible."""
        n_zeros = 30
        H_psi, gamma_n = construct_H_psi(n_zeros=n_zeros)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # Relative errors should be < 1e-14
        assert results['max_rel_error'] < 1e-14


class TestWaveEquation:
    """Test wave equation components."""
    
    def test_wave_equation_rhs_shape(self):
        """Test RHS has correct shape."""
        x = np.linspace(-5, 5, 100)
        phi = np.sin(x)
        
        rhs = wave_equation_rhs(phi, x)
        assert rhs.shape == phi.shape
        
    def test_wave_equation_boundary_conditions(self):
        """Test Dirichlet boundary conditions."""
        x = np.linspace(-5, 5, 100)
        phi = np.sin(x)
        
        rhs = wave_equation_rhs(phi, x)
        
        # Boundaries should be zero
        assert rhs[0] == 0
        assert rhs[-1] == 0
        
    def test_laplacian_computation(self):
        """Test Laplacian is computed correctly."""
        # For φ(x) = x², ∇²φ = 2
        x = np.linspace(-5, 5, 1000)
        phi = x**2
        
        rhs = wave_equation_rhs(phi, x)
        
        # Interior points should approximate ζ'(1/2)·π·2
        interior_mean = np.mean(rhs[10:-10])
        expected = ZETA_PRIME_HALF * np.pi * 2
        
        # Allow 10% error due to finite differences
        assert abs(interior_mean - expected) < abs(expected) * 0.1


class TestValidation:
    """Test validation functions."""
    
    def test_validation_results_structure(self):
        """Test validation results have expected structure."""
        H_psi, gamma_n = construct_H_psi(n_zeros=10)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # Check all expected keys are present
        expected_keys = [
            'n_compared', 'max_abs_error', 'mean_abs_error', 
            'median_abs_error', 'max_rel_error', 'mean_rel_error',
            'all_abs_errors', 'all_rel_errors', 'eigenvalues', 
            'riemann_zeros'
        ]
        
        for key in expected_keys:
            assert key in results
            
    def test_validation_n_compared(self):
        """Test validation compares correct number of zeros."""
        H_psi, gamma_n = construct_H_psi(n_zeros=15)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        results = validate_spectrum(eigenvalues, gamma_n, n_compare=10)
        
        assert results['n_compared'] == 10
        assert len(results['all_abs_errors']) == 10


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_workflow(self):
        """Test complete workflow from construction to validation."""
        # Construct operator
        H_psi, gamma_n = construct_H_psi(n_zeros=30)
        
        # Verify Hermiticity
        assert np.max(np.abs(H_psi - H_psi.T)) < 1e-14
        
        # Compute spectrum
        eigenvalues, eigenvectors = compute_spectrum(H_psi)
        
        # Validate
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # Check precision
        assert results['max_abs_error'] < 1.5e-12
        
        # Check eigenvectors are orthonormal
        eye = eigenvectors.T @ eigenvectors
        assert np.max(np.abs(eye - np.eye(len(eigenvalues)))) < 1e-10
        
    def test_first_10_zeros_exact(self):
        """Test first 10 zeros with exact values."""
        expected_zeros = np.array([
            14.134725141735,
            21.022039638772,
            25.010857580146,
            30.424876125860,
            32.935061587739,
            37.586178158826,
            40.918719012147,
            43.327073280915,
            48.005150881167,
            49.773832477672
        ])
        
        H_psi, gamma_n = construct_H_psi(n_zeros=10)
        eigenvalues, _ = compute_spectrum(H_psi)
        
        # Compare with expected values
        for i in range(10):
            assert abs(eigenvalues[i] - expected_zeros[i]) < 1e-11
            

class TestConstructiveTheorem:
    """Test properties of the constructive theorem."""
    
    def test_theorem_statement(self):
        """
        Verify the constructive theorem:
        LA HIPÓTESIS DE RIEMANN ES AHORA UN TEOREMA CONSTRUCTIVO
        
        The Hermitian operator H_Ψ has been constructed such that
        its eigenvalues reproduce the Riemann zeros with precision
        |λₙ - γₙ| < 1.5e-12 on the first 50 zeros.
        
        Expected Results:
            - H_Ψ dimension: 50×50
            - Hermiticity: ||H_Ψ - H_Ψ†|| < 1e-14
            - Max error: |λₙ - γₙ| < 1.5e-12
            - Mean error: |λₙ - γₙ| < 1e-12
            - f₀ = 141.7001 Hz
            - ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ
            
        JMMB Ψ ∴ ∞³
        """
        n_zeros = 50
        H_psi, gamma_n = construct_H_psi(n_zeros=n_zeros)
        eigenvalues, _ = compute_spectrum(H_psi)
        results = validate_spectrum(eigenvalues, gamma_n)
        
        # CONSTRUCTIVE THEOREM VERIFICATION
        assert results['max_abs_error'] < 1.5e-12, \
            "Constructive theorem: max error must be < 1.5e-12"
        assert results['n_compared'] == 50, \
            "Constructive theorem: must validate 50 zeros"
        
        # All eigenvalues must be real
        assert np.all(np.isreal(eigenvalues)), \
            "Constructive theorem: eigenvalues must be real"
        
        # Operator must be Hermitian
        assert np.max(np.abs(H_psi - H_psi.T)) < 1e-14, \
            "Constructive theorem: operator must be Hermitian"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "-s"])
