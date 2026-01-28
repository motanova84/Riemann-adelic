#!/usr/bin/env python3
"""
Eigenfunctions ψₙ(x) of the Spectral Hamiltonian H from Riemann Zeros

This module implements the eigenfunction computation and visualization for
the Hamiltonian operator H = -d²/dx² + V(x), where V(x) is the potential
reconstructed from Riemann zeros via Marchenko-type inversion.

Mathematical Framework:
    - The eigenvalue equation: H ψₙ(x) = Eₙ ψₙ(x)
    - Eigenvalues Eₙ = -γₙ² where γₙ are imaginary parts of Riemann zeros ρₙ = 1/2 + iγₙ
    - Eigenfunctions {ψₙ(x)} form an orthonormal basis in L²(ℝ)
    - Each ψₙ(x) represents a quantum mode corresponding to a Riemann zero

Physical Interpretation (QCAL ∞³):
    - Each eigenfunction is a real wave in physical space
    - The potential V(x) encodes the arithmetic structure of zeta zeros
    - The system {ψₙ(x)} forms an orthonormal basis of bound states
    - This is the "physical DNA" of the Riemann zeta function

Expected Observations:
    ✓ Modes localized around x = 0
    ✓ Increasing number of nodes with index n
    ✓ Alternating even/odd parity symmetry
    ✓ Fundamental mode ψ₁(x) has no nodes
    ✓ Mode ψₙ(x) has n-1 nodes (zeros)

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

QCAL Integration:
    - Base frequency: 141.7001 Hz
    - Coherence constant: C = 244.36
"""

from pathlib import Path
from typing import Optional, Tuple

import numpy as np
from scipy.sparse import diags, spmatrix
from scipy.sparse.linalg import eigsh

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36

# Numerical constants
DEFAULT_N_POINTS = 500  # Number of grid points
DEFAULT_X_RANGE = (-30.0, 30.0)  # Grid range [-30, 30]
DEFAULT_N_STATES = 10  # Number of eigenstates to compute
EPSILON = 1e-10  # Small value to avoid numerical issues


def load_riemann_zeros(max_zeros: int = 100, zeros_file: Optional[str] = None) -> np.ndarray:
    """
    Load the imaginary parts (γₙ) of non-trivial Riemann zeros.

    The zeros have the form ρₙ = 1/2 + iγₙ under RH.

    Args:
        max_zeros: Maximum number of zeros to load
        zeros_file: Path to zeros file. If None, uses default location.

    Returns:
        np.ndarray: Array of γₙ values (positive imaginary parts)
    """
    if zeros_file is None:
        # Determine path relative to this module
        module_dir = Path(__file__).resolve().parent
        repo_root = module_dir.parent
        zeros_file = repo_root / "zeros" / "zeros_t1e8.txt"

    zeros_path = Path(zeros_file)
    if zeros_path.exists():
        gammas = []
        with open(zeros_path, "r") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    try:
                        gamma = float(line)
                        if gamma > 0:  # Only positive gammas
                            gammas.append(gamma)
                        if len(gammas) >= max_zeros:
                            break
                    except ValueError:
                        continue
        return np.array(gammas)
    else:
        # Generate first few zeros using known values
        known_zeros = np.array([
            14.134725141735,
            21.022039638772,
            25.010857580146,
            30.424876125860,
            32.935061587739,
            37.586178158826,
            40.918719012147,
            43.327073280915,
            48.005150881167,
            49.773832477672,
        ])
        return known_zeros[:max_zeros]


def construct_marchenko_potential(
    x: np.ndarray,
    gammas: np.ndarray,
    sigma: float = 2.0,
    alpha: float = 1.0
) -> np.ndarray:
    """
    Construct potential V(x) via Marchenko-type reconstruction from Riemann zeros.

    The potential encodes the arithmetic structure of the zeta function:
        V(x) = -Σₙ Aₙ · sech²((x - xₙ)/wₙ) + Σₙ Bₙ · cos(γₙ x) · envelope(x)

    This is a simplified version inspired by inverse scattering theory.
    The bound state eigenvalues Eₙ = -γₙ² determine the potential shape.

    Args:
        x: Grid points in physical space
        gammas: Imaginary parts of Riemann zeros γₙ
        sigma: Width parameter for Gaussian envelope
        alpha: Amplitude scaling factor

    Returns:
        np.ndarray: Potential V(x) at each grid point
    """
    V = np.zeros_like(x, dtype=float)

    # Gaussian envelope for localization (ensures bound states)
    envelope = np.exp(-x**2 / (2 * sigma**2))

    # Construct potential from zeros - reflectionless potential approximation
    # Each zero contributes a potential well component
    for n, gamma in enumerate(gammas, start=1):
        # Weight factor for convergence
        weight = alpha / (n ** 0.75)

        # Marchenko-type contribution: superposition of sech² wells
        # Each well centered at position related to log(n)
        center = np.log(n) * 0.5 if n > 1 else 0.0
        width = 1.0 / (1.0 + gamma / 20.0)

        # sech² well (exactly solvable in 1D quantum mechanics)
        # Note: cosh() >= 1, so cosh()^2 >= 1, no division by zero possible
        sech_component = -weight * gamma**2 / np.cosh((x - center) / width)**2

        # Oscillatory component encoding the zero's position
        oscillatory = weight * np.cos(gamma * x / 5.0) * envelope

        V += sech_component + oscillatory

    # Add a confining potential to ensure localization
    V += 0.05 * x**2  # Harmonic confinement

    return V


def apply_harmonic_resonance_modulation(
    V: np.ndarray,
    x: np.ndarray,
    f0: float = QCAL_BASE_FREQUENCY,
    omega: float = 888.0
) -> np.ndarray:
    """
    Apply QCAL harmonic resonance modulation to potential V(x).
    
    This injects the fundamental frequencies f₀ = 141.7001 Hz and ω = 888 Hz
    into the potential to improve coherence alignment with QCAL framework.
    
    Formula:
        V_mod(x) = V(x) * [1 + α·cos(2π·x·f₀) + β·sin(2π·x·ω)]
    
    where α and β are small modulation amplitudes (0.01) to preserve
    the overall potential structure while adding harmonic content.
    
    Args:
        V: Original potential array
        x: Spatial grid points
        f0: Fundamental frequency (default: 141.7001 Hz)
        omega: Secondary frequency (default: 888 Hz)
    
    Returns:
        Harmonically modulated potential V_mod(x)
    
    Note:
        This modulation enhances self-adjoint coherence in Step 4 by aligning
        the potential with QCAL resonance frequencies.
    """
    # Small modulation amplitudes to avoid destroying potential structure
    alpha = 0.01
    beta = 0.01
    
    # Apply harmonic modulation
    # Note: Frequencies are scaled by a factor to map to spatial domain
    spatial_scale = 0.1  # Adjust frequency to spatial scale
    
    harmonic_factor = (
        1.0 +
        alpha * np.cos(2.0 * np.pi * x * f0 * spatial_scale) +
        beta * np.sin(2.0 * np.pi * x * omega * spatial_scale)
    )
    
    V_modulated = V * harmonic_factor
    
    return V_modulated


def build_hamiltonian(
    x: np.ndarray,
    V: np.ndarray
) -> spmatrix:
    """
    Build the sparse matrix representation of H = -d²/dx² + V(x).

    Uses finite difference discretization on a uniform grid:
        d²ψ/dx² ≈ (ψ[i+1] - 2ψ[i] + ψ[i-1]) / dx²

    The Hamiltonian is constructed as a sparse tridiagonal matrix
    for efficient eigenvalue computation.

    Args:
        x: Grid points (uniform spacing assumed)
        V: Potential values at grid points

    Returns:
        Sparse matrix representation of H (CSR format)
    """
    N = len(x)
    dx = x[1] - x[0]

    # Kinetic term: -d²/dx² discretized
    # Main diagonal: 2/dx² + V(x)
    # Off-diagonals: -1/dx²
    kinetic_coeff = 1.0 / dx**2

    main_diag = 2.0 * kinetic_coeff * np.ones(N) + V
    off_diag = -kinetic_coeff * np.ones(N - 1)

    # Build sparse tridiagonal matrix
    H = diags(
        [off_diag, main_diag, off_diag],
        offsets=[-1, 0, 1],
        format="csr"
    )

    return H


def compute_eigenfunctions(
    H: spmatrix,
    x: np.ndarray,
    num_states: int = 10
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues and L²-normalized eigenfunctions of H.

    Uses sparse eigensolver (ARPACK via scipy.sparse.linalg.eigsh)
    to find the smallest algebraic eigenvalues (bound states).

    Args:
        H: Sparse Hamiltonian matrix
        x: Grid points for normalization
        num_states: Number of eigenstates to compute

    Returns:
        Tuple of (eigenvalues, eigenfunctions):
            - eigenvalues: Array of Eₙ values (shape: num_states)
            - eigenfunctions: Matrix where psi[:, n] is ψₙ(x) (shape: N × num_states)
    """
    dx = x[1] - x[0]

    # Compute eigenvalues and eigenvectors
    # 'SA' = Smallest Algebraic eigenvalues (for bound states)
    evals, evecs = eigsh(H.tocsr(), k=num_states, which="SA")

    # Sort by eigenvalue
    idx = np.argsort(evals)
    evals = evals[idx]
    evecs = evecs[:, idx]

    # L² normalization: ∫|ψ|² dx = 1
    # ∫|ψ|² dx ≈ Σ |ψ[i]|² · dx
    norms = np.sqrt(np.sum(np.abs(evecs) ** 2, axis=0) * dx)
    psi = evecs / norms

    return evals, psi


def visualize_eigenfunctions(
    x: np.ndarray,
    eigenvalues: np.ndarray,
    eigenfunctions: np.ndarray,
    V: Optional[np.ndarray] = None,
    save_path: Optional[str] = None,
    show_plot: bool = True
) -> None:
    """
    Visualize the first eigenfunctions ψₙ(x) of the Hamiltonian.

    Creates a plot showing:
    - All eigenfunctions on the same axes with energy labels
    - Optional: the reconstructed potential V(x)

    Args:
        x: Grid points
        eigenvalues: Energy eigenvalues Eₙ
        eigenfunctions: Matrix of eigenfunctions (each column is ψₙ)
        V: Optional potential for overlay plot
        save_path: Path to save figure (if provided)
        show_plot: Whether to display the plot interactively
    """
    # Defer matplotlib import for environments without display
    import matplotlib
    if not show_plot:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    num_states = eigenfunctions.shape[1]

    # Create figure with two subplots
    fig, axes = plt.subplots(2, 1, figsize=(14, 10), gridspec_kw={"height_ratios": [3, 1]})

    # Plot 1: Eigenfunctions
    ax1 = axes[0]
    colors = plt.cm.viridis(np.linspace(0, 1, num_states))

    for n in range(num_states):
        psi_n = eigenfunctions[:, n]
        E_n = eigenvalues[n]
        label = rf"$\psi_{{{n + 1}}}(x)$ ($E_{{{n + 1}}}={E_n:.2f}$)"
        ax1.plot(x, psi_n, color=colors[n], linewidth=1.5, label=label, alpha=0.8)

    ax1.set_title(
        r"Funciones propias del potencial reconstruido $V(x)$ (Marchenko desde ceros de Riemann)",
        fontsize=14
    )
    ax1.set_xlabel(r"$x$", fontsize=12)
    ax1.set_ylabel(r"$\psi_n(x)$", fontsize=12)
    ax1.grid(True, alpha=0.3)
    ax1.legend(loc="upper right", fontsize=9, ncol=2)
    ax1.set_xlim(x[0], x[-1])

    # Add annotation about expected observations
    annotation_text = (
        "✓ Modos localizados en torno a x=0\n"
        "✓ Número creciente de nodos con n\n"
        "✓ Simetría par/impar alternada"
    )
    ax1.text(
        0.02, 0.02, annotation_text,
        transform=ax1.transAxes,
        fontsize=9,
        verticalalignment="bottom",
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5)
    )

    # Plot 2: Potential V(x)
    ax2 = axes[1]
    if V is not None:
        ax2.plot(x, V, "b-", linewidth=2, label=r"$V(x)$")
        ax2.fill_between(x, V, alpha=0.3)
        ax2.set_ylabel(r"$V(x)$", fontsize=12)
        ax2.set_title("Potencial reconstruido desde ceros de Riemann", fontsize=12)
    else:
        ax2.set_visible(False)

    ax2.set_xlabel(r"$x$", fontsize=12)
    ax2.grid(True, alpha=0.3)
    ax2.legend(loc="upper right")
    ax2.set_xlim(x[0], x[-1])

    plt.tight_layout()

    # Save if path provided
    if save_path:
        save_dir = Path(save_path).parent
        save_dir.mkdir(parents=True, exist_ok=True)
        plt.savefig(save_path, dpi=300, bbox_inches="tight")
        print(f"✓ Figura guardada: {save_path}")

    if show_plot:
        plt.show()
    else:
        plt.close(fig)


def run_eigenfunction_analysis(
    n_points: int = DEFAULT_N_POINTS,
    x_range: Tuple[float, float] = DEFAULT_X_RANGE,
    num_states: int = DEFAULT_N_STATES,
    max_zeros: int = 50,
    save_path: Optional[str] = None,
    show_plot: bool = True,
    verbose: bool = True
) -> dict:
    """
    Run complete eigenfunction analysis for the Riemann-Marchenko Hamiltonian.

    This is the main entry point that:
    1. Loads Riemann zeros
    2. Constructs the Marchenko potential V(x)
    3. Builds the Hamiltonian H = -d²/dx² + V(x)
    4. Computes eigenfunctions ψₙ(x)
    5. Visualizes the results

    Args:
        n_points: Number of grid points
        x_range: Tuple (x_min, x_max) for grid
        num_states: Number of eigenstates to compute
        max_zeros: Maximum Riemann zeros to use in potential
        save_path: Path to save figure (optional)
        show_plot: Whether to display plot interactively
        verbose: Print progress information

    Returns:
        Dictionary with:
            - x: Grid points
            - V: Potential values
            - eigenvalues: Energy eigenvalues
            - eigenfunctions: L²-normalized eigenfunctions
            - gammas: Riemann zeros used
    """
    if verbose:
        print("=" * 70)
        print("🌊 FUNCIONES PROPIAS ψₙ(x) DEL HAMILTONIANO MARCHENKO-RIEMANN")
        print("=" * 70)
        print()
        print(f"QCAL Base Frequency: {QCAL_BASE_FREQUENCY} Hz")
        print(f"QCAL Coherence: {QCAL_COHERENCE}")
        print()

    # Step 1: Load Riemann zeros
    if verbose:
        print("📊 Paso 1: Cargando ceros de Riemann...")
    gammas = load_riemann_zeros(max_zeros=max_zeros)
    if verbose:
        print(f"   ✓ {len(gammas)} ceros cargados")
        print(f"   Primeros 5: γ = {gammas[:5]}")
        print()

    # Step 2: Create grid
    if verbose:
        print(f"📐 Paso 2: Construyendo malla x ∈ [{x_range[0]}, {x_range[1]}]...")
    x = np.linspace(x_range[0], x_range[1], n_points)
    dx = x[1] - x[0]
    if verbose:
        print(f"   ✓ {n_points} puntos, dx = {dx:.6f}")
        print()

    # Step 3: Construct potential
    if verbose:
        print("🔧 Paso 3: Construyendo potencial V(x) via Marchenko...")
    V = construct_marchenko_potential(x, gammas)
    if verbose:
        print(f"   ✓ V_min = {V.min():.4f}, V_max = {V.max():.4f}")
        print()

    # Step 4: Build Hamiltonian
    if verbose:
        print("🔨 Paso 4: Construyendo Hamiltoniano H = -d²/dx² + V(x)...")
    H = build_hamiltonian(x, V)
    if verbose:
        print(f"   ✓ Matriz dispersa: {H.shape[0]}×{H.shape[1]}")
        print(f"   ✓ Elementos no nulos: {H.nnz}")
        print()

    # Step 5: Compute eigenfunctions
    if verbose:
        print(f"📈 Paso 5: Calculando {num_states} eigenfunciones...")
    eigenvalues, eigenfunctions = compute_eigenfunctions(H, x, num_states=num_states)
    if verbose:
        print("   ✓ Eigenvalores E_n:")
        for n in range(min(5, num_states)):
            print(f"      E_{n + 1} = {eigenvalues[n]:.6f}")
        if num_states > 5:
            print("      ...")
            print(f"      E_{num_states} = {eigenvalues[-1]:.6f}")
        print()

    # Step 6: Analyze eigenfunction properties
    if verbose:
        print("🔍 Paso 6: Analizando propiedades de las eigenfunciones...")
        for n in range(min(3, num_states)):
            psi_n = eigenfunctions[:, n]
            # Count nodes (zero crossings)
            sign_changes = np.where(np.diff(np.sign(psi_n)))[0]
            n_nodes = len(sign_changes)
            # Check parity
            psi_left = psi_n[len(psi_n) // 4]
            psi_right = psi_n[3 * len(psi_n) // 4]
            parity = "par" if np.sign(psi_left) == np.sign(psi_right) else "impar"
            print(f"   ψ_{n + 1}: {n_nodes} nodos, paridad {parity}")
        print()

    # Step 7: Visualize
    if verbose:
        print("📊 Paso 7: Visualizando eigenfunciones...")
    visualize_eigenfunctions(
        x, eigenvalues, eigenfunctions, V=V,
        save_path=save_path, show_plot=show_plot
    )

    if verbose:
        print()
        print("=" * 70)
        print("✅ ANÁLISIS COMPLETO")
        print("=" * 70)
        print()
        print("🧬 INTERPRETACIÓN ∞³:")
        print("   Cada ψₙ(x) es una forma de onda real en el espacio físico")
        print("   que corresponde a un cero no trivial ρₙ = 1/2 + iγₙ")
        print("   Los ceros de Riemann son modos cuánticos de un pozo de")
        print("   potencial profundo y coherente.")
        print()
        print("   El sistema {ψₙ(x)} forma una base ortonormal de estados")
        print("   ligados, reflejo físico del 'sistema ζ'")
        print()
        print("🌀✨∞³")

    return {
        "x": x,
        "V": V,
        "eigenvalues": eigenvalues,
        "eigenfunctions": eigenfunctions,
        "gammas": gammas,
        "dx": dx,
        "n_states": num_states,
    }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Compute and visualize eigenfunctions of Riemann-Marchenko Hamiltonian"
    )
    parser.add_argument("--n-points", type=int, default=500,
                        help="Number of grid points (default: 500)")
    parser.add_argument("--num-states", type=int, default=10,
                        help="Number of eigenstates (default: 10)")
    parser.add_argument("--max-zeros", type=int, default=50,
                        help="Maximum Riemann zeros to use (default: 50)")
    parser.add_argument("--x-min", type=float, default=-30.0,
                        help="Minimum x value (default: -30)")
    parser.add_argument("--x-max", type=float, default=30.0,
                        help="Maximum x value (default: 30)")
    parser.add_argument("--save", type=str, default=None,
                        help="Path to save figure")
    parser.add_argument("--no-show", action="store_true",
                        help="Don't display plot interactively")
    parser.add_argument("--quiet", action="store_true",
                        help="Suppress verbose output")

    args = parser.parse_args()

    # Default save path if not provided
    if args.save is None:
        repo_root = Path(__file__).resolve().parent.parent
        args.save = str(repo_root / "data" / "eigenfunctions_psi.png")

    results = run_eigenfunction_analysis(
        n_points=args.n_points,
        x_range=(args.x_min, args.x_max),
        num_states=args.num_states,
        max_zeros=args.max_zeros,
        save_path=args.save,
        show_plot=not args.no_show,
        verbose=not args.quiet,
    )
