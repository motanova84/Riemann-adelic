"""
Test module for spectral eigenfunction expansion (QCAL ∞³).

Tests the complete spectral eigenfunction expansion framework:
- Potential reconstruction from Riemann zeros
- Eigenfunction computation and orthonormality
- Basis completeness verification
- Function expansion and reconstruction

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import os
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from spectral_eigenfunction_expansion import (  # noqa: E402
    load_riemann_zeros,
    reconstruct_potential_marchenko,
    construct_orthonormal_eigenfunctions,
    verify_orthonormality,
    zeta_probe_function,
    project_onto_basis,
    reconstruct_from_basis,
    compute_reconstruction_error,
    gram_schmidt_orthonormalize,
    full_spectral_expansion,
    demo_exact_reconstruction,
    F0, C_QCAL
)


class TestRiemannZerosLoading:
    """Test loading of Riemann zeros."""

    def test_load_zeros_returns_array(self):
        """Test that load_riemann_zeros returns a numpy array."""
        zeros = load_riemann_zeros(n_zeros=10)
        assert isinstance(zeros, np.ndarray)
        assert len(zeros) == 10

    def test_zeros_are_sorted(self):
        """Test that zeros are sorted in ascending order."""
        zeros = load_riemann_zeros(n_zeros=20)
        assert np.all(np.diff(zeros) > 0)

    def test_first_zero_is_correct(self):
        """Test that first zero is approximately 14.13472514."""
        zeros = load_riemann_zeros(n_zeros=1)
        assert np.isclose(zeros[0], 14.134725, rtol=1e-5)

    def test_zeros_are_positive(self):
        """Test that all zeros are positive."""
        zeros = load_riemann_zeros(n_zeros=50)
        assert np.all(zeros > 0)


class TestPotentialReconstruction:
    """Test Marchenko-type potential reconstruction."""

    def test_potential_returns_array(self):
        """Test that reconstruct_potential_marchenko returns an array."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 100)
        V = reconstruct_potential_marchenko(gamma_n, x_grid)
        assert isinstance(V, np.ndarray)
        assert len(V) == len(x_grid)

    def test_potential_is_finite(self):
        """Test that potential values are finite."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 100)
        V = reconstruct_potential_marchenko(gamma_n, x_grid)
        assert np.all(np.isfinite(V))

    def test_potential_is_smooth(self):
        """Test that potential is smooth (no NaN or Inf)."""
        gamma_n = load_riemann_zeros(n_zeros=20)
        x_grid = np.linspace(-5, 5, 200)
        V = reconstruct_potential_marchenko(gamma_n, x_grid)
        assert not np.any(np.isnan(V))
        assert not np.any(np.isinf(V))


class TestOrthonormalEigenfunctions:
    """Test construction of orthonormal eigenfunctions."""

    def test_eigenfunctions_shape(self):
        """Test that eigenfunctions have correct shape."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=5)
        assert psi.shape == (200, 5)
        assert len(eigenvalues) == 5

    def test_orthonormality_precision(self):
        """Test that eigenfunctions are orthonormal to machine precision."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 500)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=10)

        ortho_error, overlap = verify_orthonormality(psi, x_grid)

        # Orthonormality error should be at machine precision (< 1e-14)
        assert ortho_error < 1e-14, f"Orthonormality error {ortho_error} exceeds 1e-14"

    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=5)
        assert np.all(np.isreal(eigenvalues))

    def test_eigenvalues_are_sorted(self):
        """Test that eigenvalues are sorted."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=10)
        assert np.all(np.diff(eigenvalues) > 0)


class TestGramSchmidt:
    """Test Gram-Schmidt orthonormalization."""

    def test_gram_schmidt_produces_orthonormal(self):
        """Test that Gram-Schmidt produces orthonormal functions."""
        x_grid = np.linspace(-10, 10, 500)

        # Create some non-orthogonal functions
        psi = np.zeros((500, 5))
        for n in range(5):
            psi[:, n] = np.exp(-(x_grid - n)**2) + 0.1 * np.exp(-(x_grid + n)**2)

        psi_ortho = gram_schmidt_orthonormalize(psi, x_grid)

        ortho_error, overlap = verify_orthonormality(psi_ortho, x_grid)
        assert ortho_error < 1e-14


class TestProbeFunction:
    """Test probe function construction."""

    def test_probe_is_gaussian(self):
        """Test that probe function is a Gaussian."""
        x = np.array([0.0])
        zeta = zeta_probe_function(x, sigma=2.5)
        assert np.isclose(zeta[0], 1.0)

    def test_probe_decays(self):
        """Test that probe function decays away from origin."""
        x = np.linspace(-10, 10, 100)
        zeta = zeta_probe_function(x, sigma=2.5)
        assert zeta[0] < zeta[len(x) // 2]  # Edge smaller than center
        assert zeta[-1] < zeta[len(x) // 2]


class TestProjection:
    """Test projection onto eigenfunction basis."""

    def test_projection_returns_coefficients(self):
        """Test that projection returns correct number of coefficients."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=5)

        f = zeta_probe_function(x_grid, sigma=2.5)
        coeffs = project_onto_basis(f, psi, x_grid)

        assert len(coeffs) == 5

    def test_projection_coefficients_finite(self):
        """Test that projection coefficients are finite."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=10)

        f = zeta_probe_function(x_grid, sigma=2.5)
        coeffs = project_onto_basis(f, psi, x_grid)

        assert np.all(np.isfinite(coeffs))


class TestReconstruction:
    """Test reconstruction from eigenfunction expansion."""

    def test_reconstruction_shape(self):
        """Test that reconstruction has correct shape."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-10, 10, 200)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=5)

        coeffs = np.array([1.0, 0.5, 0.25, 0.125, 0.0625])
        f_recon = reconstruct_from_basis(coeffs, psi)

        assert len(f_recon) == len(x_grid)

    def test_exact_reconstruction_machine_precision(self):
        """Test that reconstruction of eigenfunction combinations is exact."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        x_grid = np.linspace(-15, 15, 1000)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=10)

        # Create function as linear combination
        true_coeffs = np.array([0.8421, 0.0013, -0.0008, 0.0005, -0.0003,
                                0.0002, -0.0001, 0.0001, 0.0001, 0.0001])
        f_original = reconstruct_from_basis(true_coeffs, psi)

        # Project and reconstruct
        recovered_coeffs = project_onto_basis(f_original, psi, x_grid)
        f_recon = reconstruct_from_basis(recovered_coeffs, psi)

        # Error should be at machine precision
        errors = compute_reconstruction_error(f_original, f_recon)
        assert errors['rms_error'] < 1e-13, f"RMS error {errors['rms_error']} exceeds 1e-13"


class TestErrorMetrics:
    """Test error computation."""

    def test_error_zero_for_identical(self):
        """Test that error is zero for identical functions."""
        f = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        errors = compute_reconstruction_error(f, f)
        assert errors['rms_error'] == 0.0
        assert errors['max_error'] == 0.0

    def test_error_positive_for_different(self):
        """Test that error is positive for different functions."""
        f1 = np.array([1.0, 2.0, 3.0])
        f2 = np.array([1.1, 2.1, 3.1])
        errors = compute_reconstruction_error(f1, f2)
        assert errors['rms_error'] > 0
        assert errors['max_error'] > 0


class TestFullSpectralExpansion:
    """Test the complete spectral expansion framework."""

    def test_full_expansion_returns_dict(self):
        """Test that full_spectral_expansion returns a dictionary."""
        results = full_spectral_expansion(
            n_zeros=10,
            n_states=5,
            n_points=200,
            verbose=False
        )
        assert isinstance(results, dict)
        assert 'gamma_n' in results
        assert 'eigenvalues' in results
        assert 'psi' in results
        assert 'errors' in results

    def test_orthonormality_is_verified(self):
        """Test that orthonormality is verified in full expansion."""
        results = full_spectral_expansion(
            n_zeros=10,
            n_states=10,
            n_points=500,
            verbose=False,
            use_orthonormal_basis=True
        )
        assert results['ortho_error'] < 1e-14

    def test_reconstruction_converges(self):
        """Test that reconstruction error decreases with more modes."""
        results_5 = full_spectral_expansion(
            n_zeros=10,
            n_states=5,
            n_points=500,
            verbose=False,
            use_orthonormal_basis=True
        )
        results_20 = full_spectral_expansion(
            n_zeros=10,
            n_states=20,
            n_points=500,
            verbose=False,
            use_orthonormal_basis=True
        )

        # More modes should give smaller error
        assert results_20['errors']['rms_error'] < results_5['errors']['rms_error']


class TestExactReconstruction:
    """Test exact reconstruction demonstration."""

    def test_exact_reconstruction_machine_precision(self):
        """Test that exact reconstruction achieves machine precision."""
        results = demo_exact_reconstruction(
            n_zeros=10,
            n_basis_modes=10,
            n_points=1000,
            verbose=False
        )

        # RMS error should be at machine precision (< 1e-14)
        assert results['rms_error'] < 1e-14, f"RMS error {results['rms_error']} exceeds 1e-14"

    def test_coefficient_recovery(self):
        """Test that coefficients are recovered exactly."""
        results = demo_exact_reconstruction(
            n_zeros=10,
            n_basis_modes=10,
            n_points=1000,
            verbose=False
        )

        # Coefficient error should be at machine precision
        assert results['coeff_error'] < 1e-14


class TestQCALConstants:
    """Test QCAL framework constants."""

    def test_fundamental_frequency(self):
        """Test QCAL fundamental frequency constant."""
        assert np.isclose(F0, 141.7001, rtol=1e-6)

    def test_coherence_constant(self):
        """Test QCAL coherence constant."""
        assert np.isclose(C_QCAL, 244.36, rtol=1e-4)


class TestSpectralConvergence:
    """Test spectral convergence properties."""

    def test_ultrafast_convergence(self):
        """Test that convergence is ultrafast (exponential)."""
        gamma_n = load_riemann_zeros(n_zeros=100)
        x_grid = np.linspace(-15, 15, 1000)
        eigenvalues, psi = construct_orthonormal_eigenfunctions(gamma_n, x_grid, n_states=50)

        zeta_vec = zeta_probe_function(x_grid, sigma=2.5)
        all_coeffs = project_onto_basis(zeta_vec, psi, x_grid)

        errors = []
        for n_modes in [5, 10, 20, 40]:
            zeta_recon = np.sum(all_coeffs[:n_modes, np.newaxis] * psi[:, :n_modes].T, axis=0)
            err = compute_reconstruction_error(zeta_vec, zeta_recon)
            errors.append(err['rms_error'])

        # Each doubling of modes should significantly reduce error
        for i in range(len(errors) - 1):
            assert errors[i + 1] < errors[i], "Error should decrease with more modes"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
