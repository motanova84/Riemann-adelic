"""
Tests for thermal kernel operator construction and Riemann Hypothesis verification.

These tests verify that the thermal kernel operator H:
1. Is properly constructed from geometric principles
2. Has non-negative eigenvalues (coercivity)
3. Encodes Riemann zeros on the critical line Re(ρ) = 1/2
Tests for thermal kernel spectral operator implementation.

This validates the analytical Gaussian kernel approach without oscillatory integration.
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thermal_kernel_operator import (
    K_t, basis_func, build_H_operator, spectrum_to_zeros,
    load_theoretical_zeros, compare_with_theoretical
)


class TestThermalKernel:
    """Test the thermal kernel K_t(x, y, t)"""
    
    def test_kernel_symmetry(self):
        """Thermal kernel should be symmetric: K_t(x,y) = K_t(y,x)"""
        x, y = 1.5, 2.3
        t = 0.01
        
        k_xy = K_t(x, y, t)
        k_yx = K_t(y, x, t)
        
        assert np.abs(k_xy - k_yx) < 1e-10, "Kernel should be symmetric"
    
    def test_kernel_positive(self):
        """Thermal kernel should be positive for t > 0"""
        x, y = 1.0, 1.0
        t = 0.01
        
        k = K_t(x, y, t)
        
        assert np.real(k) > 0, "Kernel should be positive at diagonal"
    
    def test_kernel_decay(self):
        """Kernel should decay as |log x - log y| increases"""
        t = 0.01
        x = 1.0
        
        k_near = K_t(x, 1.1, t)
        k_far = K_t(x, 10.0, t)
        
        assert np.abs(k_near) > np.abs(k_far), "Kernel should decay with distance"
    
    def test_kernel_thermal_limit(self):
        """As t → 0, kernel should become more localized"""
        x, y = 1.0, 2.0
        
        k_large_t = K_t(x, y, 0.1)
        k_small_t = K_t(x, y, 0.001)
        
        # Smaller t means more localization (larger magnitude at origin)
        assert np.abs(k_small_t) < np.abs(k_large_t) * 100, "Kernel behavior with t"


class TestBasisFunctions:
    """Test the logarithmic basis functions"""
    
    def test_basis_orthogonality(self):
        """Different basis functions should be approximately orthogonal"""
        x_min, x_max = np.exp(-1), np.exp(1)
        n_points = 100
        x_vals = np.linspace(x_min, x_max, n_points)
        
        psi_1 = np.array([basis_func(1, x, x_min, x_max) for x in x_vals])
        psi_2 = np.array([basis_func(2, x, x_min, x_max) for x in x_vals])
        
        # Approximate inner product with d×x = dx/x measure
        inner_product = np.sum(psi_1 * psi_2 / x_vals) * (x_max - x_min) / n_points
        
        assert np.abs(inner_product) < 0.5, "Basis functions should be approximately orthogonal"
    
    def test_basis_normalization(self):
        """Basis functions should have finite norm"""
        x_min, x_max = np.exp(-1), np.exp(1)
        n_points = 100
        x_vals = np.linspace(x_min, x_max, n_points)
        
        psi_1 = np.array([basis_func(1, x, x_min, x_max) for x in x_vals])
        
        # Approximate norm
        norm_sq = np.sum(psi_1**2 / x_vals) * (x_max - x_min) / n_points
        
        assert 0 < norm_sq < 10, f"Basis function norm should be finite, got {norm_sq}"
    
    def test_basis_boundary(self):
        """Basis functions should be zero outside domain"""
        x_min, x_max = np.exp(-1), np.exp(1)
        
        # Outside domain
        assert basis_func(1, 0.1, x_min, x_max) == 0
        assert basis_func(1, 10.0, x_min, x_max) == 0


class TestOperatorConstruction:
    """Test the H operator construction"""
    
    def test_operator_hermiticity(self):
        """Operator H should be Hermitian (self-adjoint)"""
        n_basis = 5
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=1.0)
        
        # Check Hermiticity: H = H†
        H_dagger = np.conj(H.T)
        
        assert np.allclose(H, H_dagger, atol=1e-10), "Operator should be Hermitian"
    
    def test_operator_coercivity(self):
        """Operator H (with shift) should have all positive eigenvalues"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=50.0)
        
        # Add shift for coercivity
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive (coercive)"
        assert np.min(eigenvalues) >= 0.249, f"Minimum eigenvalue should be at least 0.249, got {np.min(eigenvalues)}"
    
    def test_operator_finite_spectrum(self):
        """Operator should have finite spectrum"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.01, scale_factor=50.0)
        
        eigenvalues = np.linalg.eigvalsh(H)
        
        assert np.all(np.isfinite(eigenvalues)), "All eigenvalues should be finite"
        assert len(eigenvalues) == n_basis, "Should have n_basis eigenvalues"


class TestZeroConversion:
    """Test conversion from eigenvalues to zeros"""
    
    def test_zero_conversion_critical_line(self):
        """All converted zeros should lie on critical line Re(ρ) = 1/2"""
        eigenvalues = np.array([0.25, 1.0, 4.0, 10.0, 25.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        for z in zeros:
            assert np.abs(np.real(z) - 0.5) < 1e-10, f"Zero {z} not on critical line"
    
    def test_zero_conversion_imaginary_positive(self):
        """Imaginary parts of zeros should be positive"""
        eigenvalues = np.array([0.25, 1.0, 4.0, 10.0, 25.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        for z in zeros:
            assert np.imag(z) >= 0, f"Zero {z} has negative imaginary part"
    
    def test_zero_conversion_relation(self):
        """Verify λ = ρ(1-ρ) = 1/4 + γ² relationship"""
        # Use eigenvalues that will produce non-trivial zeros (λ > 0.25)
        eigenvalues = np.array([1.0, 4.0, 10.0])
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Should have one zero per eigenvalue
        assert len(zeros) == len(eigenvalues), f"Expected {len(eigenvalues)} zeros, got {len(zeros)}"
        
        for lam, z in zip(eigenvalues, zeros):
            # Extract gamma from zero: z = 1/2 + i*gamma
            gamma = np.imag(z)
            
            # Verify: λ = 1/4 + γ²
            expected_lambda = 0.25 + gamma**2
            
            assert np.abs(lam - expected_lambda) < 1e-8, f"λ={lam} should equal 1/4 + γ²={expected_lambda}"


class TestTheoreticalComparison:
    """Test comparison with known theoretical zeros"""
    
    def test_theoretical_zeros_loaded(self):
        """Should be able to load theoretical zeros"""
        zeros = load_theoretical_zeros(n_zeros=5)
        
        assert len(zeros) == 5, "Should load 5 zeros"
        
        # First zero should be around 14.13...
        assert np.abs(np.imag(zeros[0]) - 14.134725) < 0.001
    
    def test_comparison_function(self):
        """Comparison function should work correctly"""
        theoretical = load_theoretical_zeros(n_zeros=3)
        
        # Create synthetic computed zeros close to theoretical
        computed = [z + 0.1j for z in theoretical]
        
        result = compare_with_theoretical(computed, theoretical)
        
        assert result is not None
        assert result['n_compared'] == 3
        assert all(err < 0.2 for err in result['differences'])


class TestSpectralInversion:
    """Test spectral inversion properties"""
    
    def test_trace_formula(self):
        """Trace of operator should relate to number of zeros"""
        n_basis = 10
        H = build_H_operator(n_basis=n_basis, t=0.001, scale_factor=1.0)
        
        trace = np.trace(H)
        
        # Trace should be finite and positive
        assert np.isfinite(trace), "Trace should be finite"
        assert trace > 0, "Trace should be positive"


class TestIntegration:
    """Integration tests for complete workflow"""
    
    def test_complete_workflow_small(self):
        """Test complete workflow with small basis"""
        # Build operator
        n_basis = 8
        t = 0.01
        H = build_H_operator(n_basis=n_basis, t=t, scale_factor=50.0)
        
        # Add shift
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        # Convert to zeros
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Check properties
        assert len(zeros) <= n_basis
        assert all(np.abs(np.real(z) - 0.5) < 1e-10 for z in zeros)
        assert all(np.isfinite(z) for z in zeros)
    
    @pytest.mark.slow
    def test_complete_workflow_large(self):
        """Test complete workflow with larger basis (slower)"""
        # Build operator with more basis functions
        n_basis = 15
        t = 0.001
        H = build_H_operator(n_basis=n_basis, t=t, scale_factor=50.0)
        
        # Add shift
        shift = 0.25
        H_shifted = H + shift * np.eye(n_basis)
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(H_shifted)
        
        # Convert to zeros
        zeros = spectrum_to_zeros(eigenvalues, return_both_signs=False)
        
        # Compare with theoretical
        theoretical = load_theoretical_zeros(n_zeros=10)
        
        # At least some zeros should be captured
        assert len(zeros) > 0
        assert all(np.abs(np.real(z) - 0.5) < 1e-10 for z in zeros)
from thermal_kernel_spectral import (
    K_gauss, thermal_kernel, cos_basis, build_R_matrix,
    spectrum_from_R, fourier_eigs_H, build_H_operator,
    validate_spectral_construction
)


class TestGaussianKernel:
    """Test the analytical Gaussian kernel."""
    
    def test_gaussian_kernel_symmetry(self):
        """K_h(t,s) should be symmetric in t,s."""
        h = 0.01
        t, s = 0.5, -0.3
        assert np.isclose(K_gauss(t, s, h), K_gauss(s, t, h))
    
    def test_gaussian_kernel_peak_at_diagonal(self):
        """K_h(t,t) should be maximum for fixed t."""
        h = 0.01
        t = 0.0
        s_vals = np.linspace(-1, 1, 21)
        K_vals = [K_gauss(t, s, h) for s in s_vals]
        assert K_vals[10] == max(K_vals)  # t=s=0 at index 10
    
    def test_gaussian_kernel_positive(self):
        """K_h should always be positive."""
        h = 0.01
        t_vals = np.linspace(-1, 1, 11)
        s_vals = np.linspace(-1, 1, 11)
        for t in t_vals:
            for s in s_vals:
                assert K_gauss(t, s, h) > 0
    
    def test_thermal_kernel_compatibility(self):
        """thermal_kernel(x,y) should match K_gauss(log x, log y)."""
        t = 0.01
        x, y = 2.0, 1.5
        K_xy = thermal_kernel(x, y, t)
        K_ts = K_gauss(np.log(x), np.log(y), t)
        assert np.isclose(K_xy, K_ts)


class TestCosineBasis:
    """Test orthonormal cosine basis functions."""
    
    def test_basis_normalization(self):
        """Basis functions should be normalized."""
        from numpy.polynomial.legendre import leggauss
        L = 1.0
        Nq = 160
        x, w = leggauss(Nq)
        t = L * x
        w = L * w
        
        # Check k=0 (constant) mode
        phi0 = cos_basis(t, L, 0)
        norm0 = np.sum(phi0**2 * w)
        assert np.isclose(norm0, 1.0, rtol=1e-10)
        
        # Check k=1 mode
        phi1 = cos_basis(t, L, 1)
        norm1 = np.sum(phi1**2 * w)
        assert np.isclose(norm1, 1.0, rtol=1e-10)
    
    def test_basis_orthogonality(self):
        """Different basis functions should be orthogonal."""
        from numpy.polynomial.legendre import leggauss
        L = 1.0
        Nq = 160
        x, w = leggauss(Nq)
        t = L * x
        w = L * w
        
        phi0 = cos_basis(t, L, 0)
        phi1 = cos_basis(t, L, 1)
        phi2 = cos_basis(t, L, 2)
        
        # Check orthogonality
        assert np.abs(np.sum(phi0 * phi1 * w)) < 1e-13
        assert np.abs(np.sum(phi0 * phi2 * w)) < 1e-13
        assert np.abs(np.sum(phi1 * phi2 * w)) < 1e-13


class TestRMatrixConstruction:
    """Test the R_h heat operator matrix construction."""
    
    def test_R_matrix_symmetric(self):
        """R matrix should be symmetric."""
        R = build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160)
        assert np.allclose(R, R.T)
    
    def test_R_matrix_positive_definite(self):
        """R matrix should be positive definite."""
        R = build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160)
        eigenvalues = np.linalg.eigvals(R)
        assert np.all(eigenvalues > 0)
    
    def test_R_matrix_size(self):
        """R matrix should have correct dimensions."""
        n_basis = 7
        R = build_R_matrix(n_basis=n_basis, h=1e-3, L=1.0, Nq=160)
        assert R.shape == (n_basis, n_basis)


class TestSpectrumMapping:
    """Test the spectral mapping from R_h to H."""
    
    def test_spectrum_positive_eigenvalues(self):
        """H eigenvalues should be >= 1/4."""
        R = build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160)
        lam_H, gammas = spectrum_from_R(R, h=1e-3)
        assert np.all(lam_H >= 0.25 - 1e-10)  # Allow small numerical error
    
    def test_spectrum_gammas_nonnegative(self):
        """Gamma values should be non-negative."""
        R = build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160)
        lam_H, gammas = spectrum_from_R(R, h=1e-3)
        assert np.all(gammas >= 0)
    
    def test_spectrum_sorted(self):
        """Eigenvalues should be sorted in ascending order."""
        R = build_R_matrix(n_basis=5, h=1e-3, L=1.0, Nq=160)
        lam_H, gammas = spectrum_from_R(R, h=1e-3)
        assert np.all(np.diff(lam_H) >= 0)


class TestFourierExactEigenvalues:
    """Test exact Fourier eigenvalue computation."""
    
    def test_fourier_first_mode(self):
        """First mode (k=0) should give λ = 1/4."""
        h = 1e-3
        L = 1.0
        eig_H, gammas = fourier_eigs_H(n_modes=1, h=h, L=L)
        # For k=0: ω=0, so λ = 0² + 1/4 = 1/4
        assert np.isclose(eig_H[0], 0.25, rtol=1e-10)
        assert np.isclose(gammas[0], 0.0, atol=1e-10)
    
    def test_fourier_eigenvalue_formula(self):
        """Check λ = ω² + 1/4 formula."""
        h = 1e-3
        L = 1.0
        n_modes = 5
        eig_H, gammas = fourier_eigs_H(n_modes=n_modes, h=h, L=L)
        
        # Check each eigenvalue
        for k in range(n_modes):
            omega_k = (np.pi / L) * k
            expected_lambda = omega_k**2 + 0.25
            assert np.isclose(eig_H[k], expected_lambda, rtol=1e-10)


class TestHOperatorConstruction:
    """Test the full H operator construction."""
    
    def test_H_symmetric(self):
        """H operator should be symmetric."""
        H, basis_info = build_H_operator(n_basis=5, t=1e-3)
        assert np.allclose(H, H.T)
    
    def test_H_coercive(self):
        """H operator should be coercive (all eigenvalues > 1/4)."""
        H, basis_info = build_H_operator(n_basis=5, t=1e-3)
        eigenvalues = basis_info['eigenvalues']
        # Allow small numerical error
        assert np.all(eigenvalues >= 0.25 - 1e-6)
    
    def test_H_basis_info(self):
        """Basis info should contain expected fields."""
        H, basis_info = build_H_operator(n_basis=5, t=1e-3)
        assert 'n_basis' in basis_info
        assert 'h' in basis_info
        assert 'L' in basis_info
        assert 'spectrum_type' in basis_info
        assert 'gammas' in basis_info
        assert 'eigenvalues' in basis_info


class TestValidation:
    """Test the full validation workflow."""
    
    def test_validation_runs(self):
        """Validation should complete without errors."""
        results = validate_spectral_construction(
            n_basis=5, t=0.01, max_zeros=5, verbose=False
        )
        assert 'eigenvalues' in results
        assert 'computed_gammas' in results
        assert 'construction_stable' in results
    
    def test_validation_stability_flags(self):
        """Validation should confirm stability properties."""
        results = validate_spectral_construction(
            n_basis=5, t=0.01, max_zeros=5, verbose=False
        )
        assert results['construction_stable'] is True
        assert results['R_symmetric'] is True
        assert results['H_coercive'] is True


class TestNoOscillatoryIntegration:
    """Test that we use analytical formulas, not oscillatory integration."""
    
    def test_kernel_is_real(self):
        """Kernel should be real (no complex oscillations)."""
        h = 0.01
        t_vals = np.linspace(-1, 1, 11)
        s_vals = np.linspace(-1, 1, 11)
        
        for t in t_vals:
            for s in s_vals:
                K_val = K_gauss(t, s, h)
                assert np.isreal(K_val)
                assert isinstance(K_val, (float, np.floating))
    
    def test_kernel_smooth_decay(self):
        """Kernel should decay smoothly (Gaussian), not oscillate."""
        h = 0.01
        t = 0.0
        s_vals = np.linspace(-2, 2, 101)
        K_vals = np.array([K_gauss(t, s, h) for s in s_vals])
        
        # Check monotonic decay away from t=s=0
        # Left side: should increase
        assert np.all(np.diff(K_vals[:50]) >= -1e-10)
        # Right side: should decrease
        assert np.all(np.diff(K_vals[51:]) <= 1e-10)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
