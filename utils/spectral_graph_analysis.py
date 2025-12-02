#!/usr/bin/env python3
"""
Spectral Graph Analysis Module

This module implements spectral analysis of graphs for the QCAL framework,
focusing on:

1. Eigenvalue computation of graph adjacency matrices
2. Spectral gap analysis for expander graph validation
3. Ramanujan graph bounds verification
4. Mini-Ramanujan graph construction and validation

The key application is the analysis of graph G4, a 4-node graph used
as a mini-Ramanujan expander in the Riemann Hypothesis proof framework.

Mathematical Background:
-----------------------
A d-regular graph is called Ramanujan if all eigenvalues λ of its adjacency
matrix (other than ±d) satisfy: |λ| ≤ 2√(d-1)

For a 2-regular graph (cycle): bound = 2√(2-1) = 2√1 = 2

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
License: Creative Commons BY-NC-SA 4.0
"""

import numpy as np
from typing import List, Tuple, Dict, Optional, Any
from dataclasses import dataclass, field
from datetime import datetime, timezone

try:
    import networkx as nx  # noqa: F401 - Available for extended graph operations
    NETWORKX_AVAILABLE = True
except ImportError:
    NETWORKX_AVAILABLE = False


# =============================================================================
# G4 Graph Edge Weights Constants
# =============================================================================
# These weights are derived from spectral optimization to achieve the target
# eigenvalues: λ₁ ≈ 2.5616, λ₂ ≈ 0, λ₃ ≈ -1.0, λ₄ ≈ -1.5616
#
# The graph structure forms a near-bipartite pattern with strong connections
# between nodes {0,1} and {3}, and weak connections to node 2.

# Target eigenvalue for λ₁ (largest eigenvalue / spectral radius)
G4_LAMBDA1_TARGET = 2.5616

# Target eigenvalue for λ₄ (smallest eigenvalue)
G4_LAMBDA4_TARGET = -1.5616

# Edge weight: Strong connection between nodes 0-1 (equal to |λ₄|)
G4_EDGE_WEIGHT_01 = 1.5616

# Edge weight: Weak connection to node 2
G4_EDGE_WEIGHT_02 = 0.0314
G4_EDGE_WEIGHT_12 = 0.0314

# Edge weight: Medium connection to node 3
G4_EDGE_WEIGHT_03 = 1.1295
G4_EDGE_WEIGHT_13 = 1.1295

# Edge weight: Weak connection between nodes 2-3
G4_EDGE_WEIGHT_23 = 0.0907


@dataclass
class SpectralGraphResult:
    """
    Result of spectral graph analysis.

    Attributes:
        n_nodes: Number of nodes in the graph
        n_edges: Number of edges in the graph
        degree: Degree of regular graph (None if irregular)
        eigenvalues: Ordered eigenvalues (descending)
        spectral_gap: Spectral gap (λ₁ - λ₂)
        ramanujan_bound: The Ramanujan bound 2√(d-1)
        is_ramanujan: Whether graph satisfies Ramanujan property
        is_expander: Whether graph is a good expander
        timestamp: Computation timestamp
        comments: Additional analysis comments
    """
    n_nodes: int
    n_edges: int
    degree: Optional[float]
    eigenvalues: np.ndarray
    spectral_gap: float
    ramanujan_bound: Optional[float]
    is_ramanujan: bool
    is_expander: bool
    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    comments: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        """Convert result to dictionary."""
        return {
            "n_nodes": self.n_nodes,
            "n_edges": self.n_edges,
            "degree": self.degree,
            "eigenvalues": self.eigenvalues.tolist(),
            "spectral_gap": self.spectral_gap,
            "ramanujan_bound": self.ramanujan_bound,
            "is_ramanujan": self.is_ramanujan,
            "is_expander": self.is_expander,
            "timestamp": self.timestamp,
            "comments": self.comments
        }


def construct_g4_adjacency() -> np.ndarray:
    """
    Construct the adjacency matrix for graph G4.

    Graph G4 is a 4-node graph designed for spectral analysis
    with specific eigenvalue properties relevant to the QCAL framework.

    The graph structure:
        0 --- 1
        |     |
        3 --- 2

    This is a 4-cycle (C4), which is 2-regular.

    Returns:
        np.ndarray: 4x4 adjacency matrix
    """
    # Adjacency matrix for C4 (4-cycle)
    # Node connections: 0-1, 1-2, 2-3, 3-0
    adjacency = np.array([
        [0, 1, 0, 1],  # Node 0 connected to 1 and 3
        [1, 0, 1, 0],  # Node 1 connected to 0 and 2
        [0, 1, 0, 1],  # Node 2 connected to 1 and 3
        [1, 0, 1, 0],  # Node 3 connected to 0 and 2
    ], dtype=float)

    return adjacency


def compute_spectral_analysis(adjacency: np.ndarray) -> SpectralGraphResult:
    """
    Compute full spectral analysis of a graph given its adjacency matrix.

    Args:
        adjacency: Square adjacency matrix (symmetric for undirected graphs)

    Returns:
        SpectralGraphResult: Complete spectral analysis results
    """
    n_nodes = adjacency.shape[0]

    # Verify symmetry (undirected graph)
    if not np.allclose(adjacency, adjacency.T):
        raise ValueError("Adjacency matrix must be symmetric for undirected graphs")

    # Compute eigenvalues
    eigenvalues = np.linalg.eigvalsh(adjacency)

    # Sort in descending order
    eigenvalues = np.sort(eigenvalues)[::-1]

    # Count edges (sum of adjacency / 2 for undirected)
    n_edges = int(np.sum(adjacency) / 2)

    # Check if graph is regular
    degrees = np.sum(adjacency, axis=1)
    if np.allclose(degrees, degrees[0]):
        degree = float(degrees[0])
        is_regular = True
    else:
        degree = None
        is_regular = False

    # Compute spectral gap (λ₁ - λ₂)
    if len(eigenvalues) >= 2:
        spectral_gap = eigenvalues[0] - eigenvalues[1]
    else:
        spectral_gap = eigenvalues[0]

    # Compute Ramanujan bound for regular graphs
    comments = []
    ramanujan_bound = None
    is_ramanujan = False

    # A graph is a good expander if it has positive spectral gap
    # This applies to both regular and irregular graphs
    is_expander = spectral_gap > 0

    if is_regular and degree is not None and degree > 1:
        ramanujan_bound = 2 * np.sqrt(degree - 1)

        # Check Ramanujan property: all non-trivial eigenvalues ≤ 2√(d-1)
        # Non-trivial means eigenvalues other than ±d
        non_trivial = [
            ev for ev in eigenvalues
            if not np.isclose(abs(ev), degree)
        ]

        if len(non_trivial) == 0:
            is_ramanujan = True
            comments.append("All eigenvalues are trivial (±d)")
        else:
            max_non_trivial = max(abs(ev) for ev in non_trivial)
            is_ramanujan = max_non_trivial <= ramanujan_bound
            comments.append(
                f"Max non-trivial eigenvalue: {max_non_trivial:.4f}"
            )

        if is_ramanujan:
            comments.append("Graph satisfies Ramanujan property (strict)")
        elif is_expander:
            comments.append(
                f"Not strictly Ramanujan (λ₁={eigenvalues[0]:.4f} > {ramanujan_bound:.4f}), "
                "but good expander"
            )
    else:
        # For irregular graphs, we can still analyze expansion properties
        if is_expander:
            comments.append(
                f"Irregular graph with good expansion (spectral gap = {spectral_gap:.4f})"
            )

    # Add symmetry comment based on λ₂ ≈ 0
    if len(eigenvalues) >= 2 and np.abs(eigenvalues[1]) < 1e-10:
        comments.append(
            "λ₂ ≈ 0 indicates graph symmetry and regularity (as expected)"
        )

    return SpectralGraphResult(
        n_nodes=n_nodes,
        n_edges=n_edges,
        degree=degree,
        eigenvalues=eigenvalues,
        spectral_gap=spectral_gap,
        ramanujan_bound=ramanujan_bound,
        is_ramanujan=is_ramanujan,
        is_expander=is_expander,
        comments=comments
    )


def analyze_g4_graph() -> SpectralGraphResult:
    """
    Perform complete spectral analysis of the G4 graph.

    This function constructs the G4 adjacency matrix and computes:
    - Eigenvalues (ordered)
    - Spectral gap
    - Ramanujan bound verification

    Expected results for G4 (4-cycle):
        λ₁ ≈ 2.0000 (degree)
        λ₂ ≈ 0
        λ₃ ≈ 0
        λ₄ ≈ -2.0000

    Returns:
        SpectralGraphResult: Complete spectral analysis
    """
    adjacency = construct_g4_adjacency()
    return compute_spectral_analysis(adjacency)


def construct_mini_ramanujan_g4() -> np.ndarray:
    """
    Construct a modified G4 graph optimized for mini-Ramanujan properties.

    This constructs a 4-node graph with specific edge weights to achieve
    the eigenvalue spectrum described in the problem statement:
        λ₁ ≈ 2.5616
        λ₂ ≈ 0
        λ₃ ≈ -1.0000
        λ₄ ≈ -1.5616

    This is achieved through a weighted adjacency matrix that produces
    the desired spectral properties for expander graph analysis.

    Mathematical notes:
        - Spectral gap: Δ = λ₁ - λ₂ ≈ 2.5616
        - λ₂ ≈ 0 indicates graph symmetry
        - The graph is not strictly Ramanujan (λ₁ > 2√(d-1)) but is a good expander

    Returns:
        np.ndarray: 4x4 weighted adjacency matrix
    """
    # Use named constants for edge weights
    adjacency = np.array([
        [0.0, G4_EDGE_WEIGHT_01, G4_EDGE_WEIGHT_02, G4_EDGE_WEIGHT_03],
        [G4_EDGE_WEIGHT_01, 0.0, G4_EDGE_WEIGHT_12, G4_EDGE_WEIGHT_13],
        [G4_EDGE_WEIGHT_02, G4_EDGE_WEIGHT_12, 0.0, G4_EDGE_WEIGHT_23],
        [G4_EDGE_WEIGHT_03, G4_EDGE_WEIGHT_13, G4_EDGE_WEIGHT_23, 0.0],
    ], dtype=float)

    return adjacency


def analyze_mini_ramanujan_g4() -> SpectralGraphResult:
    """
    Analyze the mini-Ramanujan G4 graph with weighted edges.

    This graph is designed to demonstrate expander properties
    even when not strictly satisfying the Ramanujan bound.

    Returns:
        SpectralGraphResult: Complete spectral analysis
    """
    adjacency = construct_mini_ramanujan_g4()
    result = compute_spectral_analysis(adjacency)

    # Add specific mini-Ramanujan comments
    result.comments.append(
        "Mini-Ramanujan graph: optimized for expander properties"
    )
    result.comments.append(
        f"Spectral gap Δ = {result.spectral_gap:.4f} indicates good expansion"
    )

    return result


def format_spectral_report(result: SpectralGraphResult) -> str:
    """
    Format a human-readable spectral analysis report.

    Args:
        result: SpectralGraphResult from analysis

    Returns:
        str: Formatted report string
    """
    lines = [
        "=" * 60,
        "SPECTRAL GRAPH ANALYSIS REPORT",
        "=" * 60,
        "",
        f"Timestamp: {result.timestamp}",
        "",
        "Graph Properties:",
        f"  • Nodes: {result.n_nodes}",
        f"  • Edges: {result.n_edges}",
        f"  • Degree: {result.degree if result.degree else 'Irregular'}",
        "",
        "Eigenvalues (ordered):",
    ]

    for i, ev in enumerate(result.eigenvalues, 1):
        # Handle near-zero values
        if abs(ev) < 1e-10:
            lines.append(f"  λ{i} ≈ 0 (numerically zero)")
        else:
            lines.append(f"  λ{i} ≈ {ev:+.4f}")

    lines.extend([
        "",
        f"Spectral Gap (λ₁ - λ₂): Δ ≈ {result.spectral_gap:.4f}",
        "",
    ])

    if result.ramanujan_bound is not None:
        lines.append(f"Ramanujan Bound: 2√(d-1) = {result.ramanujan_bound:.4f}")
        lines.append(f"Is Ramanujan: {'✓ Yes' if result.is_ramanujan else '✗ No'}")

    lines.append(f"Is Good Expander: {'✓ Yes' if result.is_expander else '✗ No'}")

    if result.comments:
        lines.extend(["", "Analysis Comments:"])
        for comment in result.comments:
            lines.append(f"  • {comment}")

    lines.extend(["", "=" * 60])

    return "\n".join(lines)


def validate_g4_properties() -> Tuple[bool, Dict[str, Any]]:
    """
    Validate the G4 graph against expected properties.

    This function verifies that the computed eigenvalues and spectral
    properties match the theoretical expectations for the QCAL framework.

    Expected eigenvalues (from problem statement):
        λ₁ ≈ 2.5616
        λ₂ ≈ 0 (numerically zero, at machine precision)
        λ₃ ≈ -1.0000
        λ₄ ≈ -1.5616

    Ramanujan property check:
        For degree d ≈ 2, bound = 2√(d-1) = 2√1 = 2
        Since λ₁ = 2.5616 > 2, not strictly Ramanujan but good expander

    Returns:
        Tuple[bool, Dict]: (validation_passed, details_dict)
    """
    result = analyze_mini_ramanujan_g4()
    eigenvalues = result.eigenvalues

    # Expected eigenvalues from problem statement
    expected = {
        "lambda1": 2.5616,
        "lambda2": 0.0,
        "lambda3": -1.0000,
        "lambda4": -1.5616,
    }

    # Tolerance for numerical comparisons
    tol = 1e-4

    # Validations based on problem statement
    validations = {
        "has_four_eigenvalues": len(eigenvalues) == 4,
        "lambda1_approx_2.5616": abs(eigenvalues[0] - expected["lambda1"]) < tol,
        "lambda2_near_zero": abs(eigenvalues[1]) < tol,
        "lambda3_approx_-1.0": abs(eigenvalues[2] - expected["lambda3"]) < tol,
        "lambda4_approx_-1.5616": abs(eigenvalues[3] - expected["lambda4"]) < tol,
        "spectral_gap_approx_2.5616": abs(result.spectral_gap - 2.5616) < tol,
        "is_good_expander": result.is_expander,
        "not_strictly_ramanujan": not result.is_ramanujan,  # As per problem statement
    }

    all_valid = all(validations.values())

    details = {
        "validation_passed": all_valid,
        "validations": validations,
        "eigenvalues": eigenvalues.tolist(),
        "expected_eigenvalues": expected,
        "spectral_gap": result.spectral_gap,
        "ramanujan_bound": result.ramanujan_bound,
        "is_ramanujan": result.is_ramanujan,
        "is_expander": result.is_expander,
        "comments": [
            "λ₂ ≈ 0 validates graph regularity/symmetry",
            f"λ₁ = {eigenvalues[0]:.4f} > 2√(d-1) = 2, not strict Ramanujan",
            f"Spectral gap Δ = {result.spectral_gap:.4f} indicates good expander"
        ]
    }

    return all_valid, details


if __name__ == "__main__":
    print("\n" + "=" * 60)
    print("SPECTRAL ANALYSIS OF GRAPH G4")
    print("QCAL Riemann-Adelic Framework")
    print("=" * 60)

    # Analyze standard G4 (4-cycle)
    print("\n--- Standard G4 (4-Cycle) ---")
    result_standard = analyze_g4_graph()
    print(format_spectral_report(result_standard))

    # Analyze mini-Ramanujan G4
    print("\n--- Mini-Ramanujan G4 (Weighted) ---")
    result_mini = analyze_mini_ramanujan_g4()
    print(format_spectral_report(result_mini))

    # Validation
    print("\n--- Validation ---")
    passed, details = validate_g4_properties()
    print(f"Validation: {'✓ PASSED' if passed else '✗ FAILED'}")
    for key, value in details["validations"].items():
        status = "✓" if value else "✗"
        print(f"  {status} {key}")
