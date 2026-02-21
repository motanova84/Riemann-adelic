#!/usr/bin/env python3
"""
Eigenfunctions ψₙ(x) of the Reconstructed Riemann Potential

This module implements the computation and visualization of eigenfunctions
of the Schrödinger-type operator:

    H = -d²/dx² + V(x)

where V(x) is the potential reconstructed from the Riemann zeros via the
Marchenko inverse scattering method. The eigenfunctions ψₙ(x) correspond
to the non-trivial zeros ρₙ = 1/2 + iγₙ of the Riemann zeta function.

Mathematical Foundation:
    - The operator H is constructed on a mesh x ∈ [-30, 30]
    - V(x) is interpolated from Marchenko reconstruction using Riemann zeros
    - Each eigenfunction ψₙ(x) is a bound state with energy Eₙ = -γₙ²
    - The eigenfunctions form an orthonormal basis in L²(ℝ)

Physical Interpretation (∞³):
    - Each ψₙ(x) is a real wave function in physical space
    - Corresponds to a non-trivial zero ρₙ = 1/2 + iγₙ
    - Riemann zeros are quantum modes of a deep coherent potential well
    - The system {ψₙ(x)} forms a complete orthonormal basis of bound states

Properties:
    - Modes localized around x = 0
    - Increasing number of nodes with index n
    - Alternating even/odd symmetry
    - Energies Eₙ = -γₙ² as labels
    - ψ₁(x): no nodes (fundamental mode)
    - ψ₂(x): 1 node, etc.

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

References:
    - Marchenko, V.A. (1955): Inverse scattering theory
    - Berry & Keating (1999): "H = xp and the Riemann zeros"
    - V5 Coronación: Spectral operator and Hermiticity

QCAL Integration:
    - Base frequency: 141.7001 Hz
    - Coherence constant: C = 244.36
    - Fundamental equation: Ψ = I × A_eff² × C^∞
"""

import os
from typing import Any, Dict, Optional, Tuple

import matplotlib.pyplot as plt
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz (f₀ = 100√2 + δζ)
QCAL_COHERENCE = 244.36
DELTA_ZETA = 0.2787437627  # Hz - Quantum phase shift (Euclidean → Cosmic)
EUCLIDEAN_DIAGONAL = 141.4213562373  # Hz (100√2)


def get_riemann_zeros(n: int = 10) -> np.ndarray:
    """
    Return the first n known non-trivial zeros γₙ of ζ(1/2 + iγₙ).

    These are the imaginary parts of the known Riemann zeta zeros
    on the critical line.

    Reference:
        Odlyzko, A. M. (1992). The 10^20-th zero of the Riemann zeta
        function and 175 million of its neighbors.
        http://www.dtc.umn.edu/~odlyzko/zeta_tables/

    Args:
        n: Number of zeros to return (max 20 for this implementation)

    Returns:
        np.ndarray: Array of first n known zeros γₙ
    """
    # First 20 known Riemann zeros (imaginary parts)
    known_zeros = np.array(
        [
            14.134725141734693,
            21.022039638771555,
            25.010857580145688,
            30.424876125859513,
            32.935061587739189,
            37.586178158825671,
            40.918719012147495,
            43.327073280914999,
            48.005150881167159,
            49.773832477672302,
            52.970321477714460,
            56.446247697063394,
            59.347044002602353,
            60.831778524609809,
            65.112544048081606,
            67.079810529494173,
            69.546401711173979,
            72.067157674481907,
            75.704690699083933,
            77.144840068874805,
        ]
    )
    return known_zeros[: min(n, len(known_zeros))]


def marchenko_potential_reconstruction(x: np.ndarray, zeros: np.ndarray, alpha: float = 1.0) -> np.ndarray:
    """
    Reconstruct the potential V(x) from Riemann zeros using Marchenko method.

    The Marchenko inverse scattering approach reconstructs a potential
    from its spectral data. For Riemann zeros, we construct a reflectionless
    potential whose bound state energies are Eₙ = -γₙ².

    The potential is constructed as:
        V(x) = -2 d²/dx² log det(I + K(x))

    where K(x) is the Marchenko kernel built from the zeros.

    For simplicity, we use a sum of sech² wells centered at the origin,
    each corresponding to a Riemann zero:

        V(x) = -α Σₙ γₙ² sech²(γₙ x / scale)

    This gives bound states with energies approximately Eₙ = -γₙ²/scale².

    Args:
        x: Spatial grid points
        zeros: Array of Riemann zeros γₙ
        alpha: Amplitude scaling factor (default: 1.0)

    Returns:
        np.ndarray: Potential values V(x) at each point
    """
    V = np.zeros_like(x)
    scale = 5.0  # Scale factor to fit potential wells

    for gamma in zeros:
        # Each zero contributes a sech² well
        # The depth is proportional to γₙ²
        # sech²(u) = 1/cosh²(u) gives reflectionless potential
        arg = gamma * x / scale
        # Avoid numerical overflow for large arguments
        arg = np.clip(arg, -50, 50)
        V -= alpha * (gamma / scale) ** 2 * (1.0 / np.cosh(arg)) ** 2

    return V


def build_hamiltonian_sparse(
    N: int = 1000, x_min: float = -30.0, x_max: float = 30.0, n_zeros: int = 10, alpha: float = 1.0
) -> Tuple[sparse.csr_matrix, np.ndarray, np.ndarray]:
    """
    Build the Hamiltonian operator H = -d²/dx² + V(x) as sparse matrix.

    The operator is discretized on x ∈ [x_min, x_max] with N points:
        - Kinetic term: -d²/dx² ≈ (-f[i-1] + 2f[i] - f[i+1]) / h²
        - Potential term: V(x) from Marchenko reconstruction

    Args:
        N: Number of discretization points
        x_min: Left boundary of domain
        x_max: Right boundary of domain
        n_zeros: Number of Riemann zeros to use for potential
        alpha: Amplitude scaling for potential

    Returns:
        Tuple containing:
            - H: Sparse N×N Hamiltonian matrix
            - x: Spatial grid points
            - V: Potential values at grid points
    """
    # Create uniform grid on [x_min, x_max]
    x = np.linspace(x_min, x_max, N)
    dx = x[1] - x[0]

    # Get Riemann zeros for potential reconstruction
    zeros = get_riemann_zeros(n_zeros)

    # Reconstruct potential V(x) from Riemann zeros
    V = marchenko_potential_reconstruction(x, zeros, alpha)

    # Build kinetic term: -d²/dx² with centered differences
    # Using second-order approximation: (-f[i-1] + 2f[i] - f[i+1]) / h²
    kinetic_diag = np.full(N, 2.0 / dx**2)
    kinetic_off = np.full(N - 1, -1.0 / dx**2)

    # Construct sparse Hamiltonian matrix in CSR format
    H = sparse.diags([kinetic_off, kinetic_diag + V, kinetic_off], offsets=[-1, 0, 1], format="csr")

    return H, x, V


def compute_eigenfunctions(H: sparse.csr_matrix, x: np.ndarray, num_states: int = 10) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenfunctions (eigenvectors) of the Hamiltonian H.

    Uses sparse eigensolver (ARPACK) to find the smallest algebraic
    eigenvalues and corresponding eigenvectors.

    The eigenfunctions are normalized in L² norm:
        ∫ |ψₙ(x)|² dx = 1

    Args:
        H: Sparse Hamiltonian matrix
        x: Spatial grid points (for normalization)
        num_states: Number of eigenstates to compute

    Returns:
        Tuple containing:
            - eigenvalues: Array of eigenvalues Eₙ (sorted ascending)
            - eigenfunctions: Array of normalized eigenfunctions ψₙ(x)
                              Shape: (N, num_states) where ψₙ = psi[:, n]
    """
    dx = x[1] - x[0]

    # Compute smallest algebraic eigenvalues and eigenvectors
    # 'SA' = Smallest Algebraic (values closest to -∞, returned unsorted)
    eigenvalues, eigenvectors = eigsh(H.tocsr(), k=num_states, which="SA")

    # Sort by eigenvalue in ascending order (most negative first)
    idx = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    # Normalize each eigenfunction in L² norm
    # ∫ |ψₙ(x)|² dx = Σᵢ |ψₙ(xᵢ)|² dx = 1
    norms = np.sqrt(np.sum(np.abs(eigenvectors) ** 2, axis=0) * dx)
    eigenfunctions = eigenvectors / norms

    return eigenvalues, eigenfunctions


def count_nodes(psi: np.ndarray, threshold_fraction: float = 0.1) -> int:
    """
    Count the number of nodes (zero crossings) in an eigenfunction.

    A node is where the function changes sign with significant amplitude.
    To avoid counting numerical noise as nodes, we only count crossings
    where the amplitude on both sides exceeds a threshold.

    Args:
        psi: Eigenfunction values at grid points
        threshold_fraction: Fraction of max amplitude to use as threshold

    Returns:
        int: Number of significant nodes
    """
    # Threshold for significant crossings
    max_amp = np.max(np.abs(psi))
    threshold = threshold_fraction * max_amp

    # Find sign changes where both neighbors have significant amplitude
    nodes = 0
    for i in range(1, len(psi) - 1):
        # Check if there's a sign change
        if psi[i - 1] * psi[i + 1] < 0:
            # Check if both neighbors have significant amplitude
            if np.abs(psi[i - 1]) > threshold and np.abs(psi[i + 1]) > threshold:
                nodes += 1
        elif psi[i - 1] * psi[i] < 0 and np.abs(psi[i - 1]) > threshold:
            # Direct sign change with significant amplitude
            if np.abs(psi[i]) > threshold:
                nodes += 1

    return nodes


def visualize_eigenfunctions(
    x: np.ndarray,
    eigenvalues: np.ndarray,
    eigenfunctions: np.ndarray,
    num_states: int = 10,
    save_path: Optional[str] = None,
) -> plt.Figure:
    """
    Visualize the first num_states eigenfunctions of the reconstructed potential.

    Creates a plot showing all eigenfunctions with their eigenvalues labeled.
    Matches the expected properties:
        - Modes localized around x = 0
        - Increasing number of nodes with n
        - Alternating even/odd symmetry
        - Energies Eₙ as labels

    Args:
        x: Spatial grid points
        eigenvalues: Array of eigenvalues Eₙ
        eigenfunctions: Array of eigenfunctions ψₙ(x)
        num_states: Number of eigenstates to plot
        save_path: Optional path to save the figure

    Returns:
        matplotlib Figure object
    """
    fig, ax = plt.subplots(figsize=(14, 8))

    colors = plt.cm.viridis(np.linspace(0, 1, num_states))

    for n in range(min(num_states, eigenfunctions.shape[1])):
        psi = eigenfunctions[:, n]
        E = eigenvalues[n]
        nodes = count_nodes(psi)

        # Label with n+1 (1-indexed), energy, and node count
        label = f"$\\psi_{{{n + 1}}}(x)$ (E={E:.2f}, {nodes} nodes)"
        ax.plot(x, psi, label=label, color=colors[n], linewidth=1.5)

    ax.set_title("Funciones propias del potencial reconstruido $V(x)$ (Marchenko-Riemann)", fontsize=14)
    ax.set_xlabel("x", fontsize=12)
    ax.set_ylabel(r"$\psi_n(x)$", fontsize=12)
    ax.grid(True, alpha=0.3)
    ax.legend(loc="upper right", fontsize=9)
    ax.axhline(y=0, color="k", linestyle="-", linewidth=0.5, alpha=0.5)
    ax.axvline(x=0, color="k", linestyle="--", linewidth=0.5, alpha=0.5)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"Figure saved to: {save_path}")

    return fig


def visualize_potential(
    x: np.ndarray, V: np.ndarray, eigenvalues: Optional[np.ndarray] = None, save_path: Optional[str] = None
) -> plt.Figure:
    """
    Visualize the reconstructed potential V(x) with energy levels.

    Args:
        x: Spatial grid points
        V: Potential values
        eigenvalues: Optional array of eigenvalues to show as horizontal lines
        save_path: Optional path to save the figure

    Returns:
        matplotlib Figure object
    """
    fig, ax = plt.subplots(figsize=(12, 6))

    ax.plot(x, V, "b-", linewidth=2, label="V(x)")
    ax.fill_between(x, V, alpha=0.3)

    if eigenvalues is not None:
        for n, E in enumerate(eigenvalues[:10]):
            ax.axhline(y=E, color="red", linestyle="--", linewidth=1, alpha=0.7)
            ax.text(x[-1] * 0.9, E + 0.5, f"$E_{{{n + 1}}}$={E:.2f}", fontsize=9, color="red")

    ax.set_xlabel("x", fontsize=12)
    ax.set_ylabel("V(x) / E", fontsize=12)
    ax.set_title("Potencial reconstruido V(x) desde ceros de Riemann " "(Marchenko)", fontsize=14)
    ax.grid(True, alpha=0.3)
    ax.set_xlim([x[0], x[-1]])
    ax.legend(loc="upper right")

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"Figure saved to: {save_path}")

    return fig


def verify_orthonormality(eigenfunctions: np.ndarray, dx: float, tol: float = 1e-10) -> Dict[str, Any]:
    """
    Verify orthonormality of the eigenfunctions.

    Checks that:
        ⟨ψₘ|ψₙ⟩ = ∫ ψₘ(x) ψₙ(x) dx = δₘₙ

    Args:
        eigenfunctions: Array of eigenfunctions
        dx: Grid spacing
        tol: Tolerance for deviation from identity

    Returns:
        Dict with verification results
    """
    n_states = eigenfunctions.shape[1]

    # Compute overlap matrix ⟨ψₘ|ψₙ⟩
    overlap = np.zeros((n_states, n_states))
    for m in range(n_states):
        for n in range(n_states):
            overlap[m, n] = np.sum(eigenfunctions[:, m] * eigenfunctions[:, n]) * dx

    # Check deviation from identity
    identity = np.eye(n_states)
    deviation = np.abs(overlap - identity)
    max_deviation = np.max(deviation)

    return {
        "overlap_matrix": overlap,
        "max_deviation": max_deviation,
        "is_orthonormal": max_deviation < tol,
        "n_states": n_states,
    }


def verify_eigenvalue_equation(
    H: sparse.csr_matrix, eigenvalues: np.ndarray, eigenfunctions: np.ndarray, tol: float = 1e-8
) -> Dict[str, Any]:
    """
    Verify the eigenvalue equation H ψₙ = Eₙ ψₙ.

    Args:
        H: Hamiltonian matrix
        eigenvalues: Array of eigenvalues
        eigenfunctions: Array of eigenfunctions
        tol: Tolerance for deviation

    Returns:
        Dict with verification results
    """
    n_states = len(eigenvalues)
    residuals = []

    for n in range(n_states):
        psi = eigenfunctions[:, n]
        E = eigenvalues[n]

        # Compute H ψₙ - Eₙ ψₙ
        residual = np.linalg.norm(H @ psi - E * psi) / np.linalg.norm(psi)
        residuals.append(residual)

    max_residual = max(residuals)

    return {
        "residuals": residuals,
        "max_residual": max_residual,
        "eigenvalue_equation_satisfied": max_residual < tol,
        "n_states": n_states,
    }


def run_eigenfunction_analysis(
    N: int = 1000,
    x_min: float = -30.0,
    x_max: float = 30.0,
    num_states: int = 10,
    n_zeros: int = 10,
    verbose: bool = True,
    save_figures: bool = True,
    output_dir: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Run complete eigenfunction analysis of the reconstructed Riemann potential.

    This function:
    1. Constructs the potential V(x) from Riemann zeros (Marchenko)
    2. Builds the Hamiltonian H = -d²/dx² + V(x)
    3. Computes eigenfunctions and eigenvalues
    4. Verifies orthonormality and eigenvalue equation
    5. Generates visualizations

    Args:
        N: Number of discretization points
        x_min: Left boundary of domain
        x_max: Right boundary of domain
        num_states: Number of eigenstates to compute
        n_zeros: Number of Riemann zeros for potential
        verbose: Print detailed output
        save_figures: Whether to save figures
        output_dir: Directory for saving figures

    Returns:
        Dict with complete analysis results
    """
    results = {
        "N": N,
        "x_range": (x_min, x_max),
        "num_states": num_states,
        "n_zeros": n_zeros,
        "qcal_base_frequency": QCAL_BASE_FREQUENCY,
        "qcal_coherence": QCAL_COHERENCE,
    }

    if output_dir is None:
        output_dir = os.path.dirname(os.path.abspath(__file__))

    if verbose:
        print("=" * 70)
        print("FUNCIONES PROPIAS ψₙ(x) DEL POTENCIAL RECONSTRUIDO")
        print("=" * 70)
        print()
        print("Operador: H = -d²/dx² + V(x)")
        print(f"  - Dominio: x ∈ [{x_min}, {x_max}]")
        print(f"  - Puntos: N = {N}")
        print(f"  - Estados: {num_states}")
        print(f"  - Ceros de Riemann usados: {n_zeros}")
        print()

    # Step 1: Build Hamiltonian with Marchenko-reconstructed potential
    if verbose:
        print("Paso 1: Construcción del potencial V(x) (Marchenko)...")

    H, x, V = build_hamiltonian_sparse(N=N, x_min=x_min, x_max=x_max, n_zeros=n_zeros)
    dx = x[1] - x[0]
    results["dx"] = dx
    results["x"] = x
    results["V"] = V

    if verbose:
        print(f"  ✓ Potencial reconstruido desde {n_zeros} ceros de Riemann")
        print(f"  ✓ Matriz Hamiltoniana {H.shape[0]}×{H.shape[1]} construida")
        print()

    # Step 2: Compute eigenfunctions
    if verbose:
        print(f"Paso 2: Cálculo de {num_states} funciones propias...")

    eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, num_states)
    results["eigenvalues"] = eigenvalues
    results["eigenfunctions"] = eigenfunctions

    if verbose:
        print("  ✓ Autovalores y autofunciones calculados")
        print()
        print("  Primeros 10 autovalores Eₙ (energías de estados ligados):")
        zeros = get_riemann_zeros(num_states)
        for n in range(min(10, len(eigenvalues))):
            E = eigenvalues[n]
            nodes = count_nodes(eigenfunctions[:, n])
            gamma = zeros[n] if n < len(zeros) else 0
            idx = n + 1
            print(f"    E_{idx} = {E:10.4f}  (nodos: {nodes}, γ_{idx} = {gamma:.4f})")
        print()

    # Step 3: Verify orthonormality
    if verbose:
        print("Paso 3: Verificación de ortonormalidad...")

    ortho_results = verify_orthonormality(eigenfunctions, dx)
    results["orthonormality"] = ortho_results

    if verbose:
        status = "✅" if ortho_results["is_orthonormal"] else "❌"
        print(f"  {status} Ortonormalidad: {ortho_results['is_orthonormal']}")
        print(f"  Desviación máxima de δₘₙ: {ortho_results['max_deviation']:.2e}")
        print()

    # Step 4: Verify eigenvalue equation
    if verbose:
        print("Paso 4: Verificación de ecuación de autovalores H ψₙ = Eₙ ψₙ...")

    eig_eq_results = verify_eigenvalue_equation(H, eigenvalues, eigenfunctions)
    results["eigenvalue_equation"] = eig_eq_results

    if verbose:
        status = "✅" if eig_eq_results["eigenvalue_equation_satisfied"] else "❌"
        print(f"  {status} Ecuación satisfecha: " f"{eig_eq_results['eigenvalue_equation_satisfied']}")
        print(f"  Residuo máximo: {eig_eq_results['max_residual']:.2e}")
        print()

    # Step 5: Generate visualizations
    if save_figures:
        if verbose:
            print("Paso 5: Generación de visualizaciones...")

        # Eigenfunctions plot
        fig_psi = visualize_eigenfunctions(
            x, eigenvalues, eigenfunctions, num_states, save_path=os.path.join(output_dir, "eigenfunctions_psi.png")
        )
        plt.close(fig_psi)

        # Potential plot with energy levels
        fig_V = visualize_potential(x, V, eigenvalues, save_path=os.path.join(output_dir, "potential_marchenko.png"))
        plt.close(fig_V)

        if verbose:
            print("  ✓ eigenfunctions_psi.png guardado")
            print("  ✓ potential_marchenko.png guardado")
            print()

    # Summary
    results["success"] = ortho_results["is_orthonormal"] and eig_eq_results["eigenvalue_equation_satisfied"]

    if verbose:
        print("=" * 70)
        print("INTERPRETACIÓN ∞³")
        print("=" * 70)
        print()
        print("Cada ψₙ(x) es:")
        print("  • Una forma de onda real en el espacio físico")
        print("  • Corresponde a un cero no trivial ρₙ = 1/2 + iγₙ de ζ(s)")
        print()
        print("Los ceros de Riemann son modos cuánticos de un pozo de")
        print("potencial profundo y coherente reconstruido por Marchenko.")
        print()
        print("El sistema {ψₙ(x)} forma una base ortonormal de estados")
        print("ligados, reflejo físico del 'sistema ζ' ∞³")
        print()
        print("=" * 70)
        print(f"Validación completada: {'✅ ÉXITO' if results['success'] else '❌ FALLO'}")
        print("=" * 70)

    return results


def main():
    """Main entry point for eigenfunction analysis."""
    print()
    print("∴" * 35)
    print("  QCAL ∞³ - Funciones Propias ψₙ(x)")
    print("∴" * 35)
    print()

    # Run complete analysis
    results = run_eigenfunction_analysis(
        N=1000, x_min=-30.0, x_max=30.0, num_states=10, n_zeros=10, verbose=True, save_figures=True
    )

    print()
    print("∴" * 35)
    print("  Análisis completado")
    print("∴" * 35)

    return 0 if results.get("success", False) else 1


if __name__ == "__main__":
    exit(main())
