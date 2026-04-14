"""
Test module for infinity_cubed_expansion.py

Tests the ∞³ eigenfunction expansion implementation, validating:
1. Orthonormal basis construction
2. Function expansion and reconstruction
3. Ultrafast convergence
4. Machine precision error (10⁻¹⁴)

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest

from infinity_cubed_expansion import (
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
    get_known_riemann_zeros,
    build_harmonic_potential,
    build_potential_from_zeros,
    build_hamiltonian_matrix,
    compute_eigenfunctions,
    normalize_eigenfunctions,
    verify_orthonormality,
    zeta_probe,
    project_onto_basis,
    run_infinity_cubed_expansion,
)


class TestQCALConstants:
    """Test QCAL integration constants."""

    def test_base_frequency(self):
        """Test QCAL base frequency is correct."""
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_coherence_constant(self):
        """Test QCAL coherence constant is correct."""
        assert QCAL_COHERENCE == 244.36


class TestRiemannZeros:
    """Test Riemann zeros retrieval."""

    def test_first_zero(self):
        """Test first Riemann zero is approximately 14.13."""
        zeros = get_known_riemann_zeros(1)
        assert abs(zeros[0] - 14.134725141734693) < 1e-10

    def test_zeros_increasing(self):
        """Test that zeros are strictly increasing."""
        zeros = get_known_riemann_zeros(10)
        for i in range(len(zeros) - 1):
            assert zeros[i] < zeros[i + 1]

    def test_zeros_count(self):
        """Test we can get requested number of zeros."""
        for n in [5, 10, 20, 30]:
            zeros = get_known_riemann_zeros(n)
            assert len(zeros) == n


class TestPotentialConstruction:
    """Test potential construction functions."""

    def test_harmonic_potential_shape(self):
        """Test harmonic potential has correct shape."""
        x = np.linspace(-5, 5, 100)
        V = build_harmonic_potential(x, omega=1.0)
        assert V.shape == x.shape

    def test_harmonic_potential_values(self):
        """Test harmonic potential V(x) = ω²x²/2."""
        x = np.linspace(-5, 5, 100)
        omega = 2.0
        V = build_harmonic_potential(x, omega=omega)
        expected = 0.5 * omega ** 2 * x ** 2
        np.testing.assert_allclose(V, expected)

    def test_harmonic_potential_symmetric(self):
        """Test harmonic potential is symmetric."""
        x = np.linspace(-5, 5, 101)  # Odd number for x=0 at center
        V = build_harmonic_potential(x)
        np.testing.assert_allclose(V, V[::-1])

    def test_zeros_potential_shape(self):
        """Test zeros-based potential has correct shape."""
        x = np.linspace(-50, 50, 1000)
        V = build_potential_from_zeros(x, num_zeros=5)
        assert V.shape == x.shape

    def test_zeros_potential_confining(self):
        """Test zeros-based potential is confining."""
        x = np.linspace(-50, 50, 1000)
        V = build_potential_from_zeros(x, num_zeros=5)
        # Edges should be higher than center region
        assert V[0] > V[len(x) // 2]
        assert V[-1] > V[len(x) // 2]


class TestHamiltonianConstruction:
    """Test Hamiltonian matrix construction."""

    def test_hamiltonian_shape(self):
        """Test Hamiltonian has correct shape."""
        N = 100
        H, x, V = build_hamiltonian_matrix(N=N, L=10.0)
        assert H.shape == (N, N)
        assert len(x) == N
        assert len(V) == N

    def test_hamiltonian_symmetric(self):
        """Test Hamiltonian is symmetric (self-adjoint)."""
        H, _, _ = build_hamiltonian_matrix(N=100, L=10.0, use_harmonic=True)
        np.testing.assert_allclose(H, H.T)

    def test_grid_spacing(self):
        """Test grid spacing is uniform."""
        _, x, _ = build_hamiltonian_matrix(N=100, L=10.0)
        dx = np.diff(x)
        np.testing.assert_allclose(dx, dx[0] * np.ones_like(dx))


class TestEigenfunctions:
    """Test eigenfunction computation."""

    def test_eigenvalues_real(self):
        """Test eigenvalues are real."""
        H, _, _ = build_hamiltonian_matrix(N=500, L=8.0, use_harmonic=True)
        eigenvalues, _ = compute_eigenfunctions(H, num_states=10)
        assert np.all(np.isreal(eigenvalues))

    def test_eigenvalues_ascending(self):
        """Test eigenvalues are in ascending order."""
        H, _, _ = build_hamiltonian_matrix(N=500, L=8.0, use_harmonic=True)
        eigenvalues, _ = compute_eigenfunctions(H, num_states=10)
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] <= eigenvalues[i + 1]

    def test_harmonic_eigenvalues(self):
        """Test harmonic oscillator eigenvalues scale linearly with spacing (n+1/2)ω."""
        H, _, _ = build_hamiltonian_matrix(N=1000, L=8.0, use_harmonic=True, omega=1.0)
        eigenvalues, _ = compute_eigenfunctions(H, num_states=5)

        # For discretized harmonic oscillator, eigenvalues are approximately:
        # E_n ≈ ω_eff * (n + 1/2) where ω_eff is effective frequency
        # Key property: eigenvalues should be evenly spaced
        spacings = np.diff(eigenvalues)

        # All spacings should be approximately equal (linear spectrum)
        np.testing.assert_allclose(spacings, spacings[0] * np.ones_like(spacings), rtol=1e-3)


class TestOrthonormality:
    """Test orthonormality of eigenfunctions."""

    def test_normalization(self):
        """Test eigenfunctions are normalized."""
        H, x, _ = build_hamiltonian_matrix(N=500, L=8.0, use_harmonic=True)
        dx = x[1] - x[0]
        _, eigenvectors = compute_eigenfunctions(H, num_states=10)
        psi = normalize_eigenfunctions(eigenvectors, dx)

        for i in range(psi.shape[1]):
            norm = np.sum(psi[:, i] ** 2) * dx
            assert abs(norm - 1.0) < 1e-10

    def test_orthogonality(self):
        """Test eigenfunctions are orthogonal."""
        H, x, _ = build_hamiltonian_matrix(N=500, L=8.0, use_harmonic=True)
        dx = x[1] - x[0]
        _, eigenvectors = compute_eigenfunctions(H, num_states=10)
        psi = normalize_eigenfunctions(eigenvectors, dx)

        ortho = verify_orthonormality(psi, dx)
        assert ortho['is_orthonormal']
        assert ortho['max_off_diagonal'] < 1e-10


class TestZetaProbe:
    """Test zeta probe function."""

    def test_probe_shape(self):
        """Test probe function has correct shape."""
        x = np.linspace(-10, 10, 100)
        zeta = zeta_probe(x)
        assert zeta.shape == x.shape

    def test_probe_gaussian(self):
        """Test probe function is a Gaussian."""
        x = np.linspace(-10, 10, 100)
        sigma = 1.0
        zeta = zeta_probe(x, sigma=sigma)
        expected = np.exp(-x ** 2 / (2 * sigma ** 2))
        np.testing.assert_allclose(zeta, expected)

    def test_probe_maximum_at_origin(self):
        """Test probe function maximum at x=0."""
        x = np.linspace(-10, 10, 101)
        zeta = zeta_probe(x)
        center_idx = len(x) // 2
        assert zeta[center_idx] == np.max(zeta)


class TestProjection:
    """Test projection and reconstruction."""

    def test_projection_preserves_norm(self):
        """Test projection coefficients satisfy Parseval's identity."""
        H, x, _ = build_hamiltonian_matrix(N=1000, L=8.0, use_harmonic=True)
        dx = x[1] - x[0]
        _, eigenvectors = compute_eigenfunctions(H, num_states=100)
        psi = normalize_eigenfunctions(eigenvectors, dx)

        zeta = zeta_probe(x)
        coeffs = project_onto_basis(zeta, psi, dx)

        # Parseval: ||f||² ≈ Σ|cₙ|²
        norm_zeta = np.sum(zeta ** 2) * dx
        norm_coeffs = np.sum(coeffs ** 2)

        # Should be close (equality only for complete basis)
        assert norm_coeffs <= norm_zeta * 1.01  # Allow small numerical error

    def test_reconstruction_identity_for_eigenfunction(self):
        """Test that projecting an eigenfunction gives back itself."""
        H, x, _ = build_hamiltonian_matrix(N=500, L=8.0, use_harmonic=True)
        dx = x[1] - x[0]
        _, eigenvectors = compute_eigenfunctions(H, num_states=10)
        psi = normalize_eigenfunctions(eigenvectors, dx)

        # Use first eigenfunction as test function
        psi_0 = psi[:, 0]
        coeffs = project_onto_basis(psi_0, psi, dx)

        # Coefficient 0 should be 1, others should be 0
        assert abs(coeffs[0] - 1.0) < 1e-10
        assert np.all(np.abs(coeffs[1:]) < 1e-10)


class TestInfinityCubedExpansion:
    """Test complete ∞³ expansion."""

    def test_expansion_success(self):
        """Test expansion validates successfully."""
        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=10,
            use_harmonic_demo=True, verbose=False
        )
        assert result.success

    def test_expansion_orthonormality(self):
        """Test expansion has orthonormal basis."""
        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=10,
            use_harmonic_demo=True, verbose=False
        )
        assert result.orthonormality['is_orthonormal']

    def test_expansion_ultrafast_convergence(self):
        """Test expansion shows ultrafast convergence."""
        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=10,
            use_harmonic_demo=True, verbose=False
        )
        # Coefficients should decrease rapidly
        assert abs(result.coefficients[0]) > 10 * abs(result.coefficients[-2])

    def test_expansion_low_error(self):
        """Test expansion has low reconstruction error."""
        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=10,
            use_harmonic_demo=True, verbose=False
        )
        assert result.rms_error < 1e-4


class TestHighPrecision:
    """Test high-precision expansion achieving 10⁻¹⁴ error."""

    @pytest.mark.slow
    def test_machine_precision_error(self):
        """Test that 100 modes achieve machine precision."""
        result = run_infinity_cubed_expansion(
            N=2000, L=8.0, num_states=100,
            use_harmonic_demo=True, verbose=False
        )
        assert result.rms_error < 1e-13

    def test_orthonormality_preserved(self):
        """Test orthonormality is preserved with many modes."""
        result = run_infinity_cubed_expansion(
            N=1000, L=8.0, num_states=50,
            use_harmonic_demo=True, verbose=False
        )
        assert result.orthonormality['total_error'] < 1e-12


class TestCustomFunction:
    """Test expansion with custom probe functions."""

    def test_custom_gaussian(self):
        """Test expansion with custom Gaussian."""
        def custom_gaussian(x):
            return np.exp(-x ** 2 / 4)  # σ = √2

        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=20,
            zeta_func=custom_gaussian,
            use_harmonic_demo=True, verbose=False
        )
        assert result.success

    def test_custom_even_function(self):
        """Test expansion of even function (only even modes)."""
        def even_func(x):
            return np.cos(x) * np.exp(-x ** 2 / 2)

        result = run_infinity_cubed_expansion(
            N=500, L=8.0, num_states=10,
            zeta_func=even_func,
            use_harmonic_demo=True, verbose=False
        )
        # Odd coefficients should be near zero
        odd_coeffs = result.coefficients[1::2]
        assert np.all(np.abs(odd_coeffs) < 1e-10)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
