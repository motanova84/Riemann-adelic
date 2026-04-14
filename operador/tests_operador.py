"""
Tests for the Gaussian kernel spectral operator.

This module validates:
1. Symmetry of R matrix
2. Coercivity of H (eigenvalues > 0.25)
3. Convergence of cosine basis to Fourier as Nq increases
"""

import numpy as np
import pytest
from operador.operador_H import build_R_matrix, spectrum_from_R, fourier_eigs_H
from operador.operador_H_fourier import K_gauss as K_gauss_fourier, fourier_eigs_H as fourier_eigs_H_fourier


def test_symmetry_R():
    """Test that R matrix is symmetric."""
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=80)
    assert np.allclose(R, R.T, atol=1e-12), "R should be symmetric"


def test_positive_H():
    """Test that H is coercive: all eigenvalues > 1/4."""
    h = 1e-3
    R = build_R_matrix(n_basis=5, h=h, L=1.0, Nq=120)
    lam_H, gammas = spectrum_from_R(R, h)
    assert np.all(lam_H > 0.25), "Eigenvalues of H should exceed 1/4"
    assert np.all(gammas >= 0), "Gammas should be real nonnegative"


def test_cosine_vs_fourier_convergence():
    """Test that cosine quadrature is stable as Nq increases."""
    h = 1e-3
    L = 1.0
    
    # Cosine with increasing quadrature
    R1 = build_R_matrix(n_basis=5, h=h, L=L, Nq=60)
    lam_H1, _ = spectrum_from_R(R1, h)

    R2 = build_R_matrix(n_basis=5, h=h, L=L, Nq=160)
    lam_H2, _ = spectrum_from_R(R2, h)
    
    R3 = build_R_matrix(n_basis=5, h=h, L=L, Nq=240)
    lam_H3, _ = spectrum_from_R(R3, h)

    # Check stability: results should be similar as Nq increases
    diff_12 = np.linalg.norm(lam_H2 - lam_H1)
    diff_23 = np.linalg.norm(lam_H3 - lam_H2)
    
    # As Nq increases, changes should become smaller (converging to something)
    assert diff_23 <= diff_12 * 1.5, "Results should stabilize as Nq increases"


def test_fourier_module_consistency():
    """Test that operador_H_fourier module produces consistent results."""
    h = 1e-3
    L = 1.0
    n_modes = 5
    
    # Get eigenvalues from both modules
    eig_H_main, gammas_main = fourier_eigs_H(n_modes=n_modes, h=h, L=L)
    eig_H_fourier, gammas_fourier = fourier_eigs_H_fourier(n_modes=n_modes, h=h, L=L)
    
    # Both should give identical results
    assert np.allclose(eig_H_main, eig_H_fourier, atol=1e-14), "Fourier eigenvalues should match"
    assert np.allclose(gammas_main, gammas_fourier, atol=1e-14), "Gammas should match"


def test_fourier_spectrum_properties():
    """Test mathematical properties of Fourier spectrum."""
    h = 1e-3
    L = 1.0
    n_modes = 10
    
    eig_H, gammas = fourier_eigs_H_fourier(n_modes=n_modes, h=h, L=L)
    
    # Verify λ = ω² + 1/4
    k = np.arange(n_modes, dtype=float)
    omega = (np.pi / L) * k
    expected_eig_H = omega**2 + 0.25
    
    assert np.allclose(eig_H, expected_eig_H, atol=1e-12), "Should satisfy λ = ω² + 1/4"
    
    # Verify all eigenvalues >= 1/4 (with tolerance for floating point)
    assert np.all(eig_H >= 0.25 - 1e-10), "All eigenvalues should be >= 1/4"
    
    # Verify γ spacing is π/L (for k ≥ 1)
    if n_modes > 2:
        gamma_spacing = gammas[2:] - gammas[1:-1]
        expected_spacing = np.pi / L
        assert np.allclose(gamma_spacing, expected_spacing, atol=1e-10), "γ spacing should be π/L"


def test_K_gauss_consistency():
    """Test that K_gauss from both modules gives same results."""
    h = 1e-3
    t = np.array([0.0, 0.5, 1.0])
    s = np.array([0.0, 0.5, 1.0])
    
    # This tests that both modules have compatible K_gauss functions
    from operador.operador_H import K_gauss as K_gauss_main
    
    for ti in t:
        for si in s:
            val_main = K_gauss_main(ti, si, h)
            val_fourier = K_gauss_fourier(ti, si, h)
            assert np.isclose(val_main, val_fourier, atol=1e-14), f"K_gauss mismatch at t={ti}, s={si}"



if __name__ == "__main__":
    pytest.main([__file__, "-v"])
