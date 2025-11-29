"""
Tests for validation/spectral_analysis_G4.py module.

This test suite validates the spectral analysis of the 4×4 expander G₄
used in the Lean formalization.

Author: José Manuel Mota Burruezo
"""
import sys
import os
import numpy as np
import pytest

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# G₄ adjacency matrix - shared across all tests
# This is the 4×4 expander graph used in Lean formalization
G4_ADJACENCY_MATRIX = np.array([
    [0, 1, 1, 0],
    [1, 0, 1, 1],
    [1, 1, 0, 1],
    [0, 1, 1, 0]
], dtype=float)

# Expected spectral gap bounds (derived from numerical computation)
# λ₁ ≈ 2.5616, λ₂ ≈ 0, so spectral gap ≈ 2.5616
SPECTRAL_GAP_LOWER_BOUND = 2.5  # Slightly below expected value
SPECTRAL_GAP_UPPER_BOUND = 2.7  # Slightly above expected value


class TestG4AdjacencyMatrix:
    """Tests for the G₄ adjacency matrix structure."""

    def test_matrix_shape(self):
        """Test that G₄ is a 4×4 matrix."""
        assert G4_ADJACENCY_MATRIX.shape == (4, 4)

    def test_matrix_symmetric(self):
        """Test that G₄ adjacency matrix is symmetric."""
        assert np.allclose(G4_ADJACENCY_MATRIX, G4_ADJACENCY_MATRIX.T)

    def test_matrix_no_self_loops(self):
        """Test that G₄ has no self-loops (diagonal is zero)."""
        assert np.allclose(np.diag(G4_ADJACENCY_MATRIX), np.zeros(4))

    def test_matrix_binary_entries(self):
        """Test that G₄ has only binary entries (0 or 1)."""
        assert np.all((G4_ADJACENCY_MATRIX == 0) | (G4_ADJACENCY_MATRIX == 1))


class TestG4Eigenvalues:
    """Tests for the eigenvalue computation of G₄."""

    @pytest.fixture
    def eigenvalues(self):
        """Compute eigenvalues of G₄."""
        return np.sort(np.linalg.eigvalsh(G4_ADJACENCY_MATRIX))[::-1]

    def test_eigenvalue_count(self, eigenvalues):
        """Test that G₄ has exactly 4 eigenvalues."""
        assert len(eigenvalues) == 4

    def test_eigenvalues_real(self, eigenvalues):
        """Test that all eigenvalues are real (symmetric matrix)."""
        assert np.all(np.isreal(eigenvalues))

    def test_largest_eigenvalue_positive(self, eigenvalues):
        """Test that the largest eigenvalue is positive."""
        assert eigenvalues[0] > 0

    def test_eigenvalue_sum_zero(self, eigenvalues):
        """Test that eigenvalue sum equals trace (which is 0)."""
        assert np.allclose(np.sum(eigenvalues), 0, atol=1e-10)


class TestG4SpectralGap:
    """Tests for the spectral gap of G₄."""

    @pytest.fixture
    def spectral_data(self):
        """Compute spectral data of G₄."""
        eigenvalues = np.sort(np.linalg.eigvalsh(G4_ADJACENCY_MATRIX))[::-1]
        spectral_gap = eigenvalues[0] - eigenvalues[1]
        return {
            'eigenvalues': eigenvalues,
            'spectral_gap': spectral_gap,
            'lambda1': eigenvalues[0],
            'lambda2': eigenvalues[1]
        }

    def test_spectral_gap_positive(self, spectral_data):
        """Test that the spectral gap is positive."""
        assert spectral_data['spectral_gap'] > 0

    def test_spectral_gap_value(self, spectral_data):
        """Test spectral gap value is approximately correct."""
        assert spectral_data['spectral_gap'] > SPECTRAL_GAP_LOWER_BOUND
        assert spectral_data['spectral_gap'] < SPECTRAL_GAP_UPPER_BOUND

    def test_ramanujan_bound_comparison(self, spectral_data):
        """Test comparison with Ramanujan bound 2√(d-1).
        
        G₄ has mixed degrees: vertices 0,3 have degree 2, vertices 1,2 have degree 3.
        Using minimum degree d=2 gives Ramanujan bound = 2√(2-1) = 2.
        For an expander, |λ₂| should be at most 2√(d-1).
        """
        ramanujan_bound = 2  # 2√(2-1) = 2, using minimum degree d=2
        assert np.abs(spectral_data['lambda2']) <= ramanujan_bound + 0.1


class TestG4ExpanderProperties:
    """Tests for expander graph properties of G₄."""

    @pytest.fixture
    def graph_data(self):
        """Compute graph properties of G₄."""
        degrees = np.sum(G4_ADJACENCY_MATRIX, axis=1)
        eigenvalues = np.sort(np.linalg.eigvalsh(G4_ADJACENCY_MATRIX))[::-1]
        return {
            'A': G4_ADJACENCY_MATRIX,
            'degrees': degrees,
            'eigenvalues': eigenvalues,
            'edge_count': int(np.sum(G4_ADJACENCY_MATRIX) / 2)
        }

    def test_connected_graph(self, graph_data):
        """Test that G₄ is connected (λ₂ < λ₁)."""
        # A graph is connected iff the spectral gap is positive
        eigenvalues = graph_data['eigenvalues']
        assert eigenvalues[0] > eigenvalues[1]

    def test_vertex_degrees(self, graph_data):
        """Test vertex degrees of G₄."""
        degrees = graph_data['degrees']
        # Vertices 0 and 3 have degree 2
        # Vertices 1 and 2 have degree 3
        assert degrees[0] == 2
        assert degrees[1] == 3
        assert degrees[2] == 3
        assert degrees[3] == 2

    def test_edge_count(self, graph_data):
        """Test that G₄ has correct number of edges."""
        # Sum of degrees = 2 + 3 + 3 + 2 = 10, edges = 10/2 = 5
        assert graph_data['edge_count'] == 5


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
