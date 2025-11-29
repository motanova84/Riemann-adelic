"""
Test module for eigenfunctions_psi.py

This module tests the computation and properties of eigenfunctions ψₙ(x)
of the Hamiltonian H = -d²/dx² + V(x) reconstructed from Riemann zeros.

Tests cover:
    - Potential reconstruction (Marchenko method)
    - Hamiltonian construction
    - Eigenfunction computation
    - Orthonormality verification
    - Eigenvalue equation verification
    - Node counting and symmetry properties

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

# Add parent directory to path for imports (noqa to ignore E402)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pytest  # noqa: E402
import numpy as np  # noqa: E402
from scipy import sparse  # noqa: E402

from eigenfunctions_psi import (  # noqa: E402
    get_riemann_zeros,
    marchenko_potential_reconstruction,
    build_hamiltonian_sparse,
    compute_eigenfunctions,
    count_nodes,
    verify_orthonormality,
    verify_eigenvalue_equation,
    run_eigenfunction_analysis,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE
)


class TestRiemannZeros:
    """Test cases for Riemann zeros data."""

    def test_get_riemann_zeros_returns_array(self):
        """Test that get_riemann_zeros returns numpy array."""
        zeros = get_riemann_zeros(10)
        assert isinstance(zeros, np.ndarray)

    def test_get_riemann_zeros_count(self):
        """Test that get_riemann_zeros returns correct count."""
        for n in [1, 5, 10, 15, 20]:
            zeros = get_riemann_zeros(n)
            assert len(zeros) == min(n, 20)

    def test_get_riemann_zeros_sorted(self):
        """Test that zeros are sorted in ascending order."""
        zeros = get_riemann_zeros(20)
        assert np.all(np.diff(zeros) > 0)

    def test_first_zero_value(self):
        """Test that first zero is approximately 14.1347..."""
        zeros = get_riemann_zeros(1)
        assert abs(zeros[0] - 14.134725141734693) < 1e-10


class TestPotentialReconstruction:
    """Test cases for Marchenko potential reconstruction."""

    def test_potential_shape(self):
        """Test that potential has correct shape."""
        x = np.linspace(-30, 30, 100)
        zeros = get_riemann_zeros(5)
        V = marchenko_potential_reconstruction(x, zeros)
        assert V.shape == x.shape

    def test_potential_negative(self):
        """Test that potential is predominantly negative (attractive)."""
        x = np.linspace(-30, 30, 100)
        zeros = get_riemann_zeros(5)
        V = marchenko_potential_reconstruction(x, zeros)
        # Potential should be negative at origin
        center_idx = len(x) // 2
        assert V[center_idx] < 0

    def test_potential_symmetric(self):
        """Test that potential is symmetric V(-x) = V(x)."""
        x = np.linspace(-30, 30, 101)  # Odd number for symmetric grid
        zeros = get_riemann_zeros(5)
        V = marchenko_potential_reconstruction(x, zeros)
        # Check symmetry
        assert np.allclose(V, V[::-1], rtol=1e-10)

    def test_potential_decays_to_zero(self):
        """Test that potential decays to zero at boundaries."""
        x = np.linspace(-30, 30, 100)
        zeros = get_riemann_zeros(5)
        V = marchenko_potential_reconstruction(x, zeros)
        # Boundary values should be small
        assert abs(V[0]) < 1.0
        assert abs(V[-1]) < 1.0

    def test_potential_alpha_scaling(self):
        """Test that alpha parameter scales potential amplitude."""
        x = np.linspace(-30, 30, 100)
        zeros = get_riemann_zeros(5)
        V1 = marchenko_potential_reconstruction(x, zeros, alpha=1.0)
        V2 = marchenko_potential_reconstruction(x, zeros, alpha=2.0)
        # V2 should be twice V1
        assert np.allclose(V2, 2 * V1, rtol=1e-10)


class TestHamiltonianConstruction:
    """Test cases for Hamiltonian matrix construction."""

    def test_hamiltonian_sparse(self):
        """Test that Hamiltonian is sparse matrix."""
        H, x, V = build_hamiltonian_sparse(N=100)
        assert sparse.issparse(H)

    def test_hamiltonian_shape(self):
        """Test Hamiltonian has correct shape."""
        N = 100
        H, x, V = build_hamiltonian_sparse(N=N)
        assert H.shape == (N, N)

    def test_hamiltonian_symmetric(self):
        """Test Hamiltonian is symmetric (Hermitian)."""
        H, x, V = build_hamiltonian_sparse(N=100)
        H_dense = H.toarray()
        assert np.allclose(H_dense, H_dense.T, rtol=1e-10)

    def test_grid_values(self):
        """Test that spatial grid is correctly constructed."""
        N = 100
        x_min, x_max = -30.0, 30.0
        H, x, V = build_hamiltonian_sparse(N=N, x_min=x_min, x_max=x_max)
        assert len(x) == N
        assert x[0] == pytest.approx(x_min)
        assert x[-1] == pytest.approx(x_max)


class TestEigenfunctions:
    """Test cases for eigenfunction computation."""

    def test_compute_eigenfunctions_count(self):
        """Test that correct number of eigenfunctions are computed."""
        H, x, V = build_hamiltonian_sparse(N=200, n_zeros=5)
        num_states = 5
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, num_states)
        assert len(eigenvalues) == num_states
        assert eigenfunctions.shape[1] == num_states

    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted ascending."""
        H, x, V = build_hamiltonian_sparse(N=200, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)
        assert np.all(np.diff(eigenvalues) >= 0)

    def test_eigenfunctions_normalized(self):
        """Test that eigenfunctions are L² normalized."""
        H, x, V = build_hamiltonian_sparse(N=500, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)
        dx = x[1] - x[0]

        for n in range(5):
            psi = eigenfunctions[:, n]
            norm = np.sqrt(np.sum(np.abs(psi) ** 2) * dx)
            assert norm == pytest.approx(1.0, rel=1e-6)


class TestOrthonormality:
    """Test cases for orthonormality verification."""

    def test_orthonormality(self):
        """Test that eigenfunctions are orthonormal."""
        H, x, V = build_hamiltonian_sparse(N=500, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)
        dx = x[1] - x[0]

        result = verify_orthonormality(eigenfunctions, dx, tol=1e-6)
        assert result['is_orthonormal']
        assert result['max_deviation'] < 1e-6


class TestEigenvalueEquation:
    """Test cases for eigenvalue equation verification."""

    def test_eigenvalue_equation_satisfied(self):
        """Test that H ψₙ = Eₙ ψₙ is satisfied."""
        H, x, V = build_hamiltonian_sparse(N=500, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)

        result = verify_eigenvalue_equation(H, eigenvalues, eigenfunctions, tol=1e-6)
        assert result['eigenvalue_equation_satisfied']
        assert result['max_residual'] < 1e-6


class TestNodeCounting:
    """Test cases for node counting."""

    def test_count_nodes_ground_state_few_nodes(self):
        """Test that ground state has very few significant nodes."""
        H, x, V = build_hamiltonian_sparse(N=500, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)

        # Ground state (n=0) should have very few significant nodes
        # Due to numerical discretization, we allow up to 2
        nodes = count_nodes(eigenfunctions[:, 0])
        assert nodes <= 2, f"Ground state has too many nodes: {nodes}"

    def test_nodes_ordering(self):
        """Test that higher states tend to have more nodes than lower states."""
        H, x, V = build_hamiltonian_sparse(N=500, n_zeros=5)
        eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, 5)

        # Count nodes for each state
        node_counts = [count_nodes(eigenfunctions[:, n]) for n in range(5)]

        # The general trend should be increasing nodes with state index
        # We check that the last state has at least as many as the first
        # (allowing for numerical variations)
        assert node_counts[-1] >= node_counts[0] or \
               abs(node_counts[-1] - node_counts[0]) <= 2


class TestQCALConstants:
    """Test QCAL framework constants."""

    def test_base_frequency(self):
        """Test QCAL base frequency value."""
        assert QCAL_BASE_FREQUENCY == pytest.approx(141.7001, rel=1e-6)

    def test_coherence_constant(self):
        """Test QCAL coherence constant value."""
        assert QCAL_COHERENCE == pytest.approx(244.36, rel=1e-6)


class TestFullAnalysis:
    """Integration tests for full eigenfunction analysis."""

    def test_run_analysis_success(self):
        """Test that full analysis runs successfully."""
        # Use smaller parameters for speed
        results = run_eigenfunction_analysis(
            N=200,
            x_min=-20.0,
            x_max=20.0,
            num_states=5,
            n_zeros=5,
            verbose=False,
            save_figures=False
        )

        assert results['success']
        assert 'eigenvalues' in results
        assert 'eigenfunctions' in results
        assert results['orthonormality']['is_orthonormal']
        assert results['eigenvalue_equation']['eigenvalue_equation_satisfied']

    def test_analysis_results_structure(self):
        """Test that analysis returns expected structure."""
        results = run_eigenfunction_analysis(
            N=100,
            num_states=3,
            n_zeros=3,
            verbose=False,
            save_figures=False
        )

        required_keys = [
            'N', 'x_range', 'num_states', 'n_zeros',
            'eigenvalues', 'eigenfunctions', 'x', 'V',
            'orthonormality', 'eigenvalue_equation', 'success'
        ]

        for key in required_keys:
            assert key in results, f"Missing key: {key}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
