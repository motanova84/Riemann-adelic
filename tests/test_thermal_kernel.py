"""
Tests for thermal kernel spectral operator implementation.

This validates the analytical Gaussian kernel approach without oscillatory integration.
"""

import pytest
import numpy as np
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
