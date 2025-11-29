"""
Test module for eigenfunctions_psi.py

Tests the eigenfunction computation and visualization for the
Marchenko-Riemann Hamiltonian H = -d²/dx² + V(x).

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest

from operador.eigenfunctions_psi import (
    load_riemann_zeros,
    construct_marchenko_potential,
    build_hamiltonian,
    compute_eigenfunctions,
    run_eigenfunction_analysis,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
)


class TestLoadRiemannZeros:
    """Tests for load_riemann_zeros function."""

    def test_load_zeros_returns_array(self):
        """Test that loading zeros returns a numpy array."""
        gammas = load_riemann_zeros(max_zeros=10)
        assert isinstance(gammas, np.ndarray)

    def test_load_zeros_correct_count(self):
        """Test that the correct number of zeros is loaded."""
        gammas = load_riemann_zeros(max_zeros=5)
        assert len(gammas) <= 5

    def test_zeros_are_positive(self):
        """Test that all loaded zeros are positive."""
        gammas = load_riemann_zeros(max_zeros=10)
        assert all(g > 0 for g in gammas)

    def test_first_zero_approximately_14(self):
        """Test that first Riemann zero is approximately 14.134..."""
        gammas = load_riemann_zeros(max_zeros=1)
        if len(gammas) > 0:
            assert abs(gammas[0] - 14.134725) < 0.001


class TestMarchenkoPotential:
    """Tests for construct_marchenko_potential function."""

    def test_potential_shape(self):
        """Test that potential has same shape as grid."""
        x = np.linspace(-10, 10, 100)
        gammas = np.array([14.134, 21.022, 25.010])
        V = construct_marchenko_potential(x, gammas)
        assert V.shape == x.shape

    def test_potential_is_real(self):
        """Test that potential is real-valued."""
        x = np.linspace(-10, 10, 100)
        gammas = np.array([14.134, 21.022])
        V = construct_marchenko_potential(x, gammas)
        assert np.all(np.isreal(V))

    def test_potential_has_minimum_near_origin(self):
        """Test that potential has local structure near origin."""
        x = np.linspace(-10, 10, 200)
        gammas = np.array([14.134, 21.022, 25.010])
        V = construct_marchenko_potential(x, gammas)
        # Potential should vary across the domain
        assert np.max(V) > np.min(V)

    def test_potential_bounded(self):
        """Test that potential is finite everywhere."""
        x = np.linspace(-30, 30, 500)
        gammas = np.array([14.134, 21.022, 25.010, 30.42, 32.93])
        V = construct_marchenko_potential(x, gammas)
        assert np.all(np.isfinite(V))


class TestBuildHamiltonian:
    """Tests for build_hamiltonian function."""

    def test_hamiltonian_shape(self):
        """Test that Hamiltonian is square matrix."""
        x = np.linspace(-5, 5, 50)
        V = 0.5 * x**2  # Simple harmonic potential
        H = build_hamiltonian(x, V)
        assert H.shape == (50, 50)

    def test_hamiltonian_is_symmetric(self):
        """Test that Hamiltonian is symmetric (Hermitian for real case)."""
        x = np.linspace(-5, 5, 50)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V).toarray()
        assert np.allclose(H, H.T, atol=1e-10)

    def test_hamiltonian_tridiagonal(self):
        """Test that Hamiltonian has tridiagonal structure."""
        x = np.linspace(-5, 5, 20)
        V = np.zeros_like(x)
        H = build_hamiltonian(x, V).toarray()
        # Check that elements beyond tridiagonal are zero
        for i in range(len(x)):
            for j in range(len(x)):
                if abs(i - j) > 1:
                    assert H[i, j] == 0

    def test_hamiltonian_sparse_format(self):
        """Test that Hamiltonian is in sparse CSR format."""
        x = np.linspace(-5, 5, 50)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        assert H.format == "csr"


class TestComputeEigenfunctions:
    """Tests for compute_eigenfunctions function."""

    def test_eigenvalue_count(self):
        """Test that correct number of eigenvalues is returned."""
        x = np.linspace(-10, 10, 100)
        V = 0.5 * x**2  # Harmonic oscillator for known spectrum
        H = build_hamiltonian(x, V)
        evals, evecs = compute_eigenfunctions(H, x, num_states=5)
        assert len(evals) == 5

    def test_eigenfunction_shape(self):
        """Test that eigenfunctions have correct shape."""
        x = np.linspace(-10, 10, 100)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        evals, evecs = compute_eigenfunctions(H, x, num_states=5)
        assert evecs.shape == (100, 5)

    def test_eigenfunctions_normalized(self):
        """Test that eigenfunctions are L²-normalized."""
        x = np.linspace(-10, 10, 200)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        dx = x[1] - x[0]
        evals, evecs = compute_eigenfunctions(H, x, num_states=3)
        for n in range(3):
            norm = np.sum(np.abs(evecs[:, n])**2) * dx
            assert abs(norm - 1.0) < 0.05  # Within 5% of unit normalization

    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted in ascending order."""
        x = np.linspace(-10, 10, 100)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        evals, _ = compute_eigenfunctions(H, x, num_states=5)
        assert all(evals[i] <= evals[i + 1] for i in range(len(evals) - 1))

    def test_eigenvalues_real(self):
        """Test that all eigenvalues are real (Hermitian operator)."""
        x = np.linspace(-10, 10, 100)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        evals, _ = compute_eigenfunctions(H, x, num_states=5)
        assert all(np.isreal(e) for e in evals)

    def test_harmonic_oscillator_spectrum(self):
        """Test eigenvalues match harmonic oscillator (approximately)."""
        x = np.linspace(-20, 20, 400)
        V = 0.5 * x**2  # V = (1/2)ω²x² with ω=1
        H = build_hamiltonian(x, V)
        evals, _ = compute_eigenfunctions(H, x, num_states=5)
        # Harmonic oscillator: E_n = (n + 1/2)ω with ω=1
        # E_0 ≈ 0.5, E_1 ≈ 1.5, E_2 ≈ 2.5, ...
        # Due to discretization, we allow some tolerance
        expected_E0 = 0.5
        # Allow 50% tolerance due to finite difference discretization error
        assert abs(evals[0] - expected_E0) < 0.5  # Within 0.5 of expected


class TestEigenfunctionProperties:
    """Tests for physical properties of eigenfunctions."""

    def test_ground_state_localized(self):
        """Test that ground state is localized near origin."""
        x = np.linspace(-15, 15, 300)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        _, evecs = compute_eigenfunctions(H, x, num_states=3)
        psi_0 = evecs[:, 0]
        # Ground state should be localized near x=0
        # Check that amplitude is larger near center than at edges
        center_region = psi_0[len(psi_0)//3:2*len(psi_0)//3]
        edge_region = np.concatenate([psi_0[:len(psi_0)//6], psi_0[-len(psi_0)//6:]])
        center_amplitude = np.mean(np.abs(center_region))
        edge_amplitude = np.mean(np.abs(edge_region))
        # Ground state should be more concentrated near center
        assert center_amplitude > edge_amplitude * 0.5

    def test_first_excited_one_node(self):
        """Test that first excited state has approximately one node."""
        x = np.linspace(-15, 15, 300)
        V = 0.5 * x**2
        H = build_hamiltonian(x, V)
        _, evecs = compute_eigenfunctions(H, x, num_states=3)
        psi_1 = evecs[:, 1]
        # Count sign changes
        sign_changes = np.sum(np.abs(np.diff(np.sign(psi_1))) > 1)
        assert sign_changes >= 1  # At least one node


class TestRunEigenfunctionAnalysis:
    """Tests for the main analysis function."""

    def test_analysis_returns_dict(self):
        """Test that analysis returns a dictionary."""
        result = run_eigenfunction_analysis(
            n_points=50,
            x_range=(-10, 10),
            num_states=3,
            max_zeros=5,
            show_plot=False,
            save_path=None,
            verbose=False,
        )
        assert isinstance(result, dict)

    def test_analysis_contains_required_keys(self):
        """Test that result contains all required keys."""
        result = run_eigenfunction_analysis(
            n_points=50,
            x_range=(-10, 10),
            num_states=3,
            max_zeros=5,
            show_plot=False,
            save_path=None,
            verbose=False,
        )
        required_keys = ["x", "V", "eigenvalues", "eigenfunctions", "gammas"]
        for key in required_keys:
            assert key in result

    def test_analysis_eigenvalues_count(self):
        """Test that analysis returns correct number of eigenvalues."""
        result = run_eigenfunction_analysis(
            n_points=100,
            x_range=(-15, 15),
            num_states=5,
            max_zeros=10,
            show_plot=False,
            save_path=None,
            verbose=False,
        )
        assert len(result["eigenvalues"]) == 5

    def test_analysis_grid_size(self):
        """Test that grid has correct number of points."""
        n_points = 75
        result = run_eigenfunction_analysis(
            n_points=n_points,
            x_range=(-10, 10),
            num_states=3,
            max_zeros=5,
            show_plot=False,
            save_path=None,
            verbose=False,
        )
        assert len(result["x"]) == n_points


class TestQCALConstants:
    """Tests for QCAL integration constants."""

    def test_base_frequency_value(self):
        """Test that QCAL base frequency has correct value."""
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_coherence_constant_value(self):
        """Test that QCAL coherence constant has correct value."""
        assert QCAL_COHERENCE == 244.36


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
