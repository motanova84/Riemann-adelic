"""
Tests for G₄ spectral analysis validation module.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: CC-BY-4.0
"""

import numpy as np

from validation.spectral_G4_plot import (
    analyze_G4_spectrum,
    compute_eigenvalues,
    compute_spectral_gap,
    get_G4_adjacency_matrix,
)


class TestG4AdjacencyMatrix:
    """Tests for the G₄ adjacency matrix."""

    def test_matrix_shape(self) -> None:
        """Test that adjacency matrix has correct shape."""
        A = get_G4_adjacency_matrix()
        assert A.shape == (4, 4), "Adjacency matrix should be 4×4"

    def test_matrix_symmetric(self) -> None:
        """Test that adjacency matrix is symmetric."""
        A = get_G4_adjacency_matrix()
        assert np.allclose(A, A.T), "Adjacency matrix should be symmetric"

    def test_matrix_binary(self) -> None:
        """Test that adjacency matrix contains only 0s and 1s."""
        A = get_G4_adjacency_matrix()
        assert np.all((A == 0) | (A == 1)), "Adjacency matrix should be binary"

    def test_no_self_loops(self) -> None:
        """Test that there are no self-loops (diagonal is zero)."""
        A = get_G4_adjacency_matrix()
        assert np.all(np.diag(A) == 0), "Diagonal should be zero (no self-loops)"


class TestEigenvalueComputation:
    """Tests for eigenvalue computation."""

    def test_eigenvalue_count(self) -> None:
        """Test that we get 4 eigenvalues for 4×4 matrix."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        assert len(eigenvalues) == 4, "Should have 4 eigenvalues"

    def test_eigenvalues_sorted_descending(self) -> None:
        """Test that eigenvalues are sorted in descending order."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] >= eigenvalues[i + 1], "Eigenvalues should be sorted descending"

    def test_largest_eigenvalue_positive(self) -> None:
        """Test that the largest eigenvalue is positive."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        assert eigenvalues[0] > 0, "Largest eigenvalue should be positive"

    def test_eigenvalue_sum(self) -> None:
        """Test that eigenvalue sum equals trace (which is 0 for adjacency matrix)."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        assert np.isclose(np.sum(eigenvalues), np.trace(A)), "Sum of eigenvalues should equal trace"


class TestSpectralGap:
    """Tests for spectral gap computation."""

    def test_spectral_gap_positive(self) -> None:
        """Test that spectral gap is positive."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        gap = compute_spectral_gap(eigenvalues)
        assert gap > 0, "Spectral gap should be positive for connected graph"

    def test_spectral_gap_formula(self) -> None:
        """Test that spectral gap equals λ₁ − λ₂."""
        A = get_G4_adjacency_matrix()
        eigenvalues = compute_eigenvalues(A)
        gap = compute_spectral_gap(eigenvalues)
        expected = eigenvalues[0] - eigenvalues[1]
        assert np.isclose(gap, expected), "Spectral gap should be λ₁ − λ₂"


class TestG4Analysis:
    """Tests for full G₄ spectral analysis."""

    def test_analyze_returns_tuple(self) -> None:
        """Test that analyze_G4_spectrum returns expected types."""
        eigenvalues, spectral_gap = analyze_G4_spectrum()
        assert isinstance(eigenvalues, np.ndarray), "Eigenvalues should be numpy array"
        assert isinstance(spectral_gap, float), "Spectral gap should be float"

    def test_expected_largest_eigenvalue(self) -> None:
        """Test that largest eigenvalue is approximately 2.56."""
        eigenvalues, _ = analyze_G4_spectrum()
        # Expected λ₁ ≈ 2.5616 based on the problem statement
        assert 2.5 < eigenvalues[0] < 2.7, f"Largest eigenvalue should be ~2.56, got {eigenvalues[0]}"

    def test_expected_spectral_gap(self) -> None:
        """Test that spectral gap is approximately 2.56."""
        _, spectral_gap = analyze_G4_spectrum()
        # Expected gap ≈ 2.56 based on the problem statement
        assert 2.5 < spectral_gap < 2.7, f"Spectral gap should be ~2.56, got {spectral_gap}"

    def test_satisfies_ramanujan_bound(self) -> None:
        """Test that G₄ satisfies Ramanujan bound for non-trivial eigenvalues."""
        eigenvalues, _ = analyze_G4_spectrum()
        # Ramanujan bound for max degree d=3: 2*sqrt(d-1) = 2*sqrt(2) ≈ 2.83
        ramanujan_bound = 2 * np.sqrt(2)
        # Non-trivial eigenvalues are all except λ₁
        max_nontrivial = max(abs(eigenvalues[1]), abs(eigenvalues[-1]))
        assert max_nontrivial <= ramanujan_bound, (
            f"Non-trivial eigenvalues should satisfy Ramanujan bound: "
            f"|λ| = {max_nontrivial:.4f} ≤ {ramanujan_bound:.4f}"
        )
