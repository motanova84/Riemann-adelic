#!/usr/bin/env python3
"""
Tests for Spectral Graph Analysis Module

This module tests the spectral analysis of graphs, focusing on:
- G4 graph eigenvalue computation
- Spectral gap calculation
- Ramanujan graph validation
- Mini-Ramanujan expander properties

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: November 2025
"""

import pytest
import numpy as np

from utils.spectral_graph_analysis import (
    construct_g4_adjacency,
    construct_mini_ramanujan_g4,
    compute_spectral_analysis,
    analyze_g4_graph,
    analyze_mini_ramanujan_g4,
    validate_g4_properties,
    format_spectral_report,
)


class TestG4AdjacencyMatrix:
    """Tests for G4 adjacency matrix construction."""

    def test_g4_adjacency_shape(self):
        """Test that G4 adjacency is 4x4."""
        adj = construct_g4_adjacency()
        assert adj.shape == (4, 4)

    def test_g4_adjacency_symmetric(self):
        """Test that G4 adjacency is symmetric."""
        adj = construct_g4_adjacency()
        assert np.allclose(adj, adj.T)

    def test_g4_adjacency_no_self_loops(self):
        """Test that G4 has no self-loops (diagonal is zero)."""
        adj = construct_g4_adjacency()
        assert np.allclose(np.diag(adj), 0)

    def test_g4_is_2_regular(self):
        """Test that standard G4 is 2-regular."""
        adj = construct_g4_adjacency()
        degrees = np.sum(adj, axis=1)
        assert np.allclose(degrees, 2.0)


class TestMiniRamanujanG4:
    """Tests for Mini-Ramanujan G4 weighted graph."""

    def test_mini_g4_adjacency_shape(self):
        """Test that mini-Ramanujan G4 adjacency is 4x4."""
        adj = construct_mini_ramanujan_g4()
        assert adj.shape == (4, 4)

    def test_mini_g4_adjacency_symmetric(self):
        """Test that mini-Ramanujan G4 adjacency is symmetric."""
        adj = construct_mini_ramanujan_g4()
        assert np.allclose(adj, adj.T)

    def test_mini_g4_adjacency_no_self_loops(self):
        """Test that mini-Ramanujan G4 has no self-loops."""
        adj = construct_mini_ramanujan_g4()
        assert np.allclose(np.diag(adj), 0)

    def test_mini_g4_positive_weights(self):
        """Test that all edge weights are positive."""
        adj = construct_mini_ramanujan_g4()
        assert np.all(adj >= 0)


class TestSpectralAnalysis:
    """Tests for spectral analysis computations."""

    def test_standard_g4_eigenvalues(self):
        """Test standard G4 (4-cycle) eigenvalues."""
        result = analyze_g4_graph()

        # 4-cycle eigenvalues should be: 2, 0, 0, -2
        expected = np.array([2.0, 0.0, 0.0, -2.0])
        assert np.allclose(result.eigenvalues, expected, atol=1e-10)

    def test_standard_g4_spectral_gap(self):
        """Test standard G4 spectral gap."""
        result = analyze_g4_graph()
        assert np.isclose(result.spectral_gap, 2.0)

    def test_standard_g4_is_ramanujan(self):
        """Test that standard G4 (4-cycle) is Ramanujan."""
        result = analyze_g4_graph()
        assert result.is_ramanujan

    def test_mini_g4_eigenvalue_lambda1(self):
        """Test mini-Ramanujan G4 λ₁ ≈ 2.5616."""
        result = analyze_mini_ramanujan_g4()
        assert np.isclose(result.eigenvalues[0], 2.5616, atol=1e-4)

    def test_mini_g4_eigenvalue_lambda2_near_zero(self):
        """Test mini-Ramanujan G4 λ₂ ≈ 0."""
        result = analyze_mini_ramanujan_g4()
        assert np.abs(result.eigenvalues[1]) < 1e-4

    def test_mini_g4_eigenvalue_lambda3(self):
        """Test mini-Ramanujan G4 λ₃ ≈ -1.0."""
        result = analyze_mini_ramanujan_g4()
        assert np.isclose(result.eigenvalues[2], -1.0, atol=1e-4)

    def test_mini_g4_eigenvalue_lambda4(self):
        """Test mini-Ramanujan G4 λ₄ ≈ -1.5616."""
        result = analyze_mini_ramanujan_g4()
        assert np.isclose(result.eigenvalues[3], -1.5616, atol=1e-4)

    def test_mini_g4_spectral_gap(self):
        """Test mini-Ramanujan G4 spectral gap ≈ 2.5616."""
        result = analyze_mini_ramanujan_g4()
        assert np.isclose(result.spectral_gap, 2.5616, atol=1e-4)

    def test_mini_g4_is_expander(self):
        """Test that mini-Ramanujan G4 is a good expander."""
        result = analyze_mini_ramanujan_g4()
        assert result.is_expander

    def test_mini_g4_trace_zero(self):
        """Test that eigenvalue sum (trace) is approximately zero."""
        result = analyze_mini_ramanujan_g4()
        trace = np.sum(result.eigenvalues)
        assert np.abs(trace) < 1e-10


class TestValidation:
    """Tests for G4 property validation."""

    def test_validate_g4_properties_passes(self):
        """Test that validation passes for correctly constructed G4."""
        passed, details = validate_g4_properties()
        assert passed

    def test_validate_g4_all_checks(self):
        """Test that all individual validation checks pass."""
        passed, details = validate_g4_properties()
        for check_name, check_result in details["validations"].items():
            assert check_result, f"Validation check failed: {check_name}"

    def test_validate_g4_eigenvalue_count(self):
        """Test that validation confirms 4 eigenvalues."""
        passed, details = validate_g4_properties()
        assert details["validations"]["has_four_eigenvalues"]

    def test_validate_g4_expander_property(self):
        """Test that validation confirms expander property."""
        passed, details = validate_g4_properties()
        assert details["validations"]["is_good_expander"]

    def test_validate_g4_not_strict_ramanujan(self):
        """Test that validation confirms not strictly Ramanujan."""
        passed, details = validate_g4_properties()
        # The problem statement says λ₁ > 2, so not strictly Ramanujan
        assert details["validations"]["not_strictly_ramanujan"]


class TestSpectralGraphResult:
    """Tests for SpectralGraphResult dataclass."""

    def test_result_to_dict(self):
        """Test conversion to dictionary."""
        result = analyze_g4_graph()
        d = result.to_dict()

        assert "n_nodes" in d
        assert "eigenvalues" in d
        assert "spectral_gap" in d
        assert d["n_nodes"] == 4

    def test_result_has_timestamp(self):
        """Test that result includes timestamp."""
        result = analyze_g4_graph()
        assert result.timestamp is not None
        assert len(result.timestamp) > 0


class TestReportFormatting:
    """Tests for report formatting."""

    def test_format_report_contains_eigenvalues(self):
        """Test that formatted report contains eigenvalue info."""
        result = analyze_g4_graph()
        report = format_spectral_report(result)

        assert "λ1" in report or "λ₁" in report
        assert "Eigenvalues" in report

    def test_format_report_contains_spectral_gap(self):
        """Test that formatted report contains spectral gap."""
        result = analyze_g4_graph()
        report = format_spectral_report(result)

        assert "Spectral Gap" in report

    def test_format_report_contains_expander_status(self):
        """Test that formatted report contains expander status."""
        result = analyze_g4_graph()
        report = format_spectral_report(result)

        assert "Expander" in report


class TestEdgeCases:
    """Tests for edge cases and error handling."""

    def test_asymmetric_matrix_raises_error(self):
        """Test that asymmetric matrix raises ValueError."""
        asymmetric = np.array([
            [0, 1, 0, 0],
            [0, 0, 1, 0],  # Not symmetric
            [0, 0, 0, 1],
            [1, 0, 0, 0],
        ])

        with pytest.raises(ValueError, match="symmetric"):
            compute_spectral_analysis(asymmetric)

    def test_single_node_graph(self):
        """Test spectral analysis of single node graph."""
        single_node = np.array([[0.0]])
        result = compute_spectral_analysis(single_node)

        assert result.n_nodes == 1
        assert len(result.eigenvalues) == 1

    def test_two_node_graph(self):
        """Test spectral analysis of two-node graph."""
        two_nodes = np.array([
            [0, 1],
            [1, 0],
        ])
        result = compute_spectral_analysis(two_nodes)

        assert result.n_nodes == 2
        assert result.n_edges == 1
        assert np.isclose(result.eigenvalues[0], 1.0)
        assert np.isclose(result.eigenvalues[1], -1.0)


class TestRamanujanBound:
    """Tests for Ramanujan bound calculations."""

    def test_ramanujan_bound_2_regular(self):
        """Test Ramanujan bound for 2-regular graph."""
        result = analyze_g4_graph()
        # For d=2: bound = 2√(2-1) = 2
        assert result.ramanujan_bound is not None
        assert np.isclose(result.ramanujan_bound, 2.0)

    def test_ramanujan_bound_irregular_is_none(self):
        """Test that Ramanujan bound is None for irregular graphs."""
        result = analyze_mini_ramanujan_g4()
        # Mini-Ramanujan G4 is irregular
        assert result.ramanujan_bound is None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
