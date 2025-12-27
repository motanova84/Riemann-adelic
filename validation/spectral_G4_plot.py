#!/usr/bin/env python3
"""
Spectral Analysis of G₄ – Ramanujan Candidate.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: CC-BY-4.0

This module performs spectral analysis of G₄, a handcrafted 4×4 expander graph.
It computes eigenvalues, spectral gap, and compares against the Ramanujan bound.

For a d-regular graph, non-trivial eigenvalues should satisfy |λ| ≤ 2√(d-1).
"""

from typing import Tuple

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray


def get_G4_adjacency_matrix() -> NDArray[np.float64]:
    """
    Return the adjacency matrix of G₄ (a handcrafted expander).

    Returns:
        NDArray[np.float64]: 4×4 symmetric adjacency matrix.
    """
    return np.array([
        [0, 1, 1, 0],
        [1, 0, 1, 1],
        [1, 1, 0, 1],
        [0, 1, 1, 0]
    ], dtype=float)


def compute_eigenvalues(A: NDArray[np.float64]) -> NDArray[np.float64]:
    """
    Compute eigenvalues of a symmetric matrix in descending order.

    Args:
        A: Symmetric adjacency matrix.

    Returns:
        NDArray[np.float64]: Eigenvalues sorted in descending order.
    """
    eigenvalues = np.linalg.eigvalsh(A)
    return np.sort(eigenvalues)[::-1]


def compute_spectral_gap(eigenvalues: NDArray[np.float64]) -> float:
    """
    Compute the spectral gap Δ = λ₁ − λ₂.

    Args:
        eigenvalues: Eigenvalues sorted in descending order.

    Returns:
        float: The spectral gap.
    """
    return float(eigenvalues[0] - eigenvalues[1])


def analyze_G4_spectrum() -> Tuple[NDArray[np.float64], float]:
    """
    Perform complete spectral analysis of the G₄ graph.

    Returns:
        Tuple containing:
        - eigenvalues: Eigenvalues sorted in descending order.
        - spectral_gap: The spectral gap Δ = λ₁ − λ₂.
    """
    A = get_G4_adjacency_matrix()
    eigenvalues = compute_eigenvalues(A)
    spectral_gap = compute_spectral_gap(eigenvalues)
    return eigenvalues, spectral_gap


def plot_G4_spectrum(
    eigenvalues: NDArray[np.float64],
    output_file: str = "G4_spectrum_plot.png",
    show: bool = False
) -> None:
    """
    Plot the spectrum of G₄ with Ramanujan bound.

    Args:
        eigenvalues: Eigenvalues sorted in descending order.
        output_file: Path to save the plot.
        show: Whether to display the plot interactively.
    """
    # Ramanujan bound for max degree d=3: 2*sqrt(d-1) = 2*sqrt(2) ≈ 2.83
    ramanujan_bound = 2 * np.sqrt(2)

    plt.figure(figsize=(6, 4))
    plt.plot(eigenvalues, 'o-', label='Eigenvalues')
    plt.axhline(ramanujan_bound, color='red', linestyle='--',
                label=rf'Ramanujan bound $2\sqrt{{d-1}} \approx {ramanujan_bound:.2f}$')
    plt.axhline(-ramanujan_bound, color='red', linestyle='--')
    plt.title(r"Spectrum of $G_4$ (4×4 Expander)")
    plt.xlabel("Index")
    plt.ylabel("Eigenvalue")
    plt.grid(True)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_file)
    if show:
        plt.show()
    plt.close()


def main() -> None:
    """Main function to run the G₄ spectral analysis."""
    eigenvalues, spectral_gap = analyze_G4_spectrum()

    print("=" * 50)
    print("Spectral Analysis of G₄ – Ramanujan Candidate")
    print("=" * 50)
    print("\nEigenvalues (sorted):")
    for i, eig in enumerate(eigenvalues):
        print(f"  λ_{i} = {eig:.6f}")

    print(f"\nSpectral gap Δ = λ₁ − λ₂ = {spectral_gap:.6f}")

    # Ramanujan bound for d-regular graph: 2*sqrt(d-1)
    # For this graph, vertices have degrees 2, 3, 3, 2 (not regular)
    # Using d=3 (maximum degree) gives bound = 2*sqrt(2) ≈ 2.83
    max_degree = 3
    ramanujan_bound = 2 * np.sqrt(max_degree - 1)  # ≈ 2.83
    print(f"\nRamanujan bound (2√(d-1) for d={max_degree}): {ramanujan_bound:.4f}")

    # Non-trivial eigenvalues (excluding λ₁)
    max_nontrivial = max(abs(eigenvalues[1]), abs(eigenvalues[-1]))

    # Interpretation
    print("\n" + "-" * 50)
    print("Interpretation:")
    print("-" * 50)
    print(f"• λ₁ ≈ {eigenvalues[0]:.4f}, λ₂ ≈ {eigenvalues[1]:.4f}")
    print(f"• Gap ≈ {spectral_gap:.2f} → Good expansion properties")
    print(f"• Max non-trivial eigenvalue: |λ| = {max_nontrivial:.4f}")
    if max_nontrivial <= ramanujan_bound:
        print(f"• Satisfies Ramanujan bound (|λ| = {max_nontrivial:.4f} ≤ {ramanujan_bound:.4f})")
    else:
        print(f"• Not strictly Ramanujan (|λ| = {max_nontrivial:.4f} > {ramanujan_bound:.4f})")
    print("• Usable as a small gadget for expander constructions")

    # Generate plot
    plot_G4_spectrum(eigenvalues)
    print("\n✅ Plot saved to G4_spectrum_plot.png")


if __name__ == "__main__":
    main()
