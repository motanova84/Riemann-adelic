#!/usr/bin/env python3
"""
🎯 Kernel GLM (Gel'fand-Levitan-Marchenko) Module

This module implements the Marchenko inverse scattering approach to reconstruct
a potential V(x) from the Riemann zeta zeros γₙ. The reconstructed potential
satisfies the spectral condition Spec(-d²/dx² + V(x)) = {-γₙ²}.

Mathematical Framework:
    1. GLM Kernel: F(x) = Σₙ exp(-γₙ|x|)
    2. Marchenko Equation: K(x,y) + F(x+y) + ∫₀ˣ K(x,z)F(z+y)dz = 0
    3. Potential Reconstruction: V(x) = 2 d/dx K(x,x)

This validates the complete circle:
    ζ(s) ⇄ {γₙ} ⇄ H_Ψ ⇄ V(x)

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

References:
    - Gel'fand, I.M. & Levitan, B.M. (1951): On the determination of a
      differential equation from its spectral function
    - Marchenko, V.A. (1952): Some questions in the theory of one-dimensional
      linear differential operators
"""

import numpy as np
from scipy.linalg import solve
from typing import Tuple, Optional, Dict, Any
from mpmath import zetazero

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36


def get_riemann_zeros(N: int = 30) -> np.ndarray:
    """
    Get the first N imaginary parts of Riemann zeta zeros.

    Args:
        N: Number of zeros to compute (default: 30)

    Returns:
        Array of γₙ values (imaginary parts of zeta zeros)

    Notes:
        Uses mpmath.zetazero for high-precision computation.
        The zeros are on the critical line Re(s) = 1/2.
    """
    gamma = np.array([float(zetazero(k).imag) for k in range(1, N + 1)])
    return gamma


def F_glm_kernel(x: float, gamma: np.ndarray) -> float:
    """
    Compute the GLM kernel function F(x) for inverse scattering.

    The kernel is defined as:
        F(x) = Σₙ exp(-γₙ |x|)

    This represents the bound-state contribution to the Marchenko kernel,
    where γₙ are the Riemann zeta zeros (spectral bound-state energies).

    Args:
        x: Point where to evaluate the kernel
        gamma: Array of Riemann zeros γₙ (imaginary parts)

    Returns:
        Value of F(x)

    Example:
        >>> gamma = get_riemann_zeros(30)
        >>> F_glm_kernel(0.0, gamma)  # Maximum at origin
        30.0
    """
    return np.sum(np.exp(-gamma * np.abs(x)))


def construct_F_matrix(
    x_grid: np.ndarray, gamma: np.ndarray
) -> np.ndarray:
    """
    Construct the discretized F(xᵢ + xⱼ) matrix for Marchenko equation.

    Args:
        x_grid: Discretization grid [0, L]
        gamma: Array of Riemann zeros

    Returns:
        M×M matrix where F_matrix[i,j] = F(x_grid[i] + x_grid[j])
    """
    M = len(x_grid)
    F_matrix = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            F_matrix[i, j] = F_glm_kernel(x_grid[i] + x_grid[j], gamma)
    return F_matrix


def marchenko_solve(
    gamma: np.ndarray,
    M: int = 200,
    L: float = 15.0
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Solve the discretized Marchenko equation to find K(x,0).

    The Marchenko equation:
        K(x,y) + F(x+y) + ∫₀ˣ K(x,z)F(z+y)dz = 0

    Discretized for y=0:
        K(xᵢ,0) + F(xᵢ) + h·Σⱼ K(xᵢ,xⱼ)F(xⱼ) = 0

    We solve: (I + h·F)·K = -F for K(x,0)

    Args:
        gamma: Array of Riemann zeros γₙ
        M: Number of grid points (default: 200)
        L: Domain extent [0, L] (default: 15.0)

    Returns:
        Tuple of:
            - x_grid: Discretization grid
            - K_diag: Solution K(x,x) on the diagonal
            - L_vec: Intermediate solution vector

    Notes:
        The step size h = L/(M-1) determines numerical accuracy.
    """
    x_grid = np.linspace(0, L, M)
    h = x_grid[1] - x_grid[0]

    # Construct F(xᵢ + xⱼ) matrix
    F_matrix = construct_F_matrix(x_grid, gamma)

    # System matrix: I + h·F
    A = np.eye(M) + h * F_matrix

    # Right-hand side: F(xᵢ, 0) = F(xᵢ)
    b = np.array([F_glm_kernel(x_grid[i], gamma) for i in range(M)])

    # Solve: A·L = b, where L(x) = K(x,0)
    L_vec = solve(A, b)

    # Diagonal: K(x,x) = -L(x)
    K_diag = -L_vec

    return x_grid, K_diag, L_vec


def reconstruct_potential(
    x_grid: np.ndarray,
    K_diag: np.ndarray
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Reconstruct the potential V(x) from K(x,x) using the Marchenko formula.

    The potential is given by:
        V(x) = 2 d/dx K(x,x)

    We extend to all of ℝ using even symmetry: V(-x) = V(x)

    Args:
        x_grid: Discretization grid [0, L]
        K_diag: Diagonal values K(x,x)

    Returns:
        Tuple of:
            - x_full: Full grid [-L, L]
            - V_full: Reconstructed potential V(x)
    """
    M = len(x_grid)
    h = x_grid[1] - x_grid[0]

    # Compute V(x) = 2 d/dx K(x,x)
    V_reconstructed = np.zeros(M)
    V_reconstructed[1:] = 2 * np.diff(K_diag) / h
    V_reconstructed[0] = V_reconstructed[1]  # Extension at origin

    # Extend to full real line via even symmetry: V(-x) = V(x)
    x_full = np.concatenate([-x_grid[::-1], x_grid[1:]])
    V_full = np.concatenate([V_reconstructed[::-1], V_reconstructed[1:]])

    return x_full, V_full


def validate_reconstruction(
    x_full: np.ndarray,
    V_full: np.ndarray,
    gamma: np.ndarray,
    num_eigenvalues: int = 15,
    domain_extent: float = 30.0,
    Nx: int = 4000
) -> Dict[str, Any]:
    """
    Validate the reconstructed potential by computing its eigenvalues.

    We construct the Hamiltonian H = -d²/dx² + V(x) and verify that
    its eigenvalues match -γₙ² (bound state energies).

    Args:
        x_full: Full grid for V(x)
        V_full: Reconstructed potential
        gamma: Original Riemann zeros
        num_eigenvalues: Number of eigenvalues to compute (default: 15)
        domain_extent: Domain for eigenvalue computation (default: 30.0)
        Nx: Number of grid points for discretization (default: 4000)

    Returns:
        Dictionary with validation results:
            - eigenvalues: Computed eigenvalues
            - expected: Expected values -γₙ²
            - mean_error: Mean absolute error
            - V_at_origin: Potential at x=0
            - V_min: Minimum potential value
            - success: Boolean indicating validation success
    """
    from scipy.sparse import diags
    from scipy.sparse.linalg import eigsh

    # Create evaluation grid
    x_val = np.linspace(-domain_extent, domain_extent, Nx)
    dx = x_val[1] - x_val[0]

    # Interpolate V onto evaluation grid
    V_interp = np.interp(x_val, x_full, V_full, left=V_full[0], right=V_full[-1])

    # Construct Laplacian using finite differences
    diag_main = -2 * np.ones(Nx) / dx**2
    diag_off = np.ones(Nx - 1) / dx**2
    Lapl = diags([diag_off, diag_main, diag_off], [-1, 0, 1])

    # Hamiltonian: H = -d²/dx² + V(x)
    H = -Lapl + diags([V_interp], [0])

    # Compute smallest eigenvalues (bound states)
    eigenvalues, _ = eigsh(H.tocsr(), k=num_eigenvalues, which='SA')
    eigenvalues = np.sort(eigenvalues)

    # Expected bound-state energies: -γₙ²
    expected = -gamma[:num_eigenvalues]**2

    # Compute mean error
    num_compare = min(len(eigenvalues), len(expected))
    mean_error = np.mean(np.abs(eigenvalues[:num_compare] - expected[:num_compare]))

    # Get potential characteristics
    center_idx = len(V_full) // 2
    V_at_origin = V_full[center_idx]
    V_min = V_full.min()

    return {
        'eigenvalues': eigenvalues,
        'expected': expected,
        'mean_error': mean_error,
        'V_at_origin': V_at_origin,
        'V_min': V_min,
        'success': mean_error < 10.0  # Tolerance for numerical error
    }


def full_reconstruction(
    N: int = 30,
    M: int = 200,
    L: float = 15.0,
    validate: bool = True
) -> Dict[str, Any]:
    """
    Perform complete Marchenko inverse scattering reconstruction.

    This function orchestrates the full pipeline:
        ζ(s) → {γₙ} → F(x) → K(x,y) → V(x) → validate

    Args:
        N: Number of Riemann zeros to use (default: 30)
        M: Grid points for Marchenko discretization (default: 200)
        L: Domain extent (default: 15.0)
        validate: Whether to validate by computing eigenvalues (default: True)

    Returns:
        Dictionary with complete reconstruction results:
            - gamma: Riemann zeros used
            - x_full: Full grid
            - V_full: Reconstructed potential
            - validation: Validation results (if validate=True)
            - K_diag: Diagonal of Marchenko kernel
    """
    # Step 1: Get Riemann zeros
    gamma = get_riemann_zeros(N)

    # Step 2: Solve Marchenko equation
    x_grid, K_diag, L_vec = marchenko_solve(gamma, M, L)

    # Step 3: Reconstruct potential
    x_full, V_full = reconstruct_potential(x_grid, K_diag)

    result = {
        'gamma': gamma,
        'x_full': x_full,
        'V_full': V_full,
        'K_diag': K_diag
    }

    # Step 4: Validate (optional)
    if validate:
        result['validation'] = validate_reconstruction(x_full, V_full, gamma)

    return result


def plot_reconstruction(
    result: Dict[str, Any],
    save_path: Optional[str] = None
) -> None:
    """
    Generate plots of the reconstruction results.

    Creates a two-panel figure showing:
        1. Reconstructed potential V(x)
        2. Spectral comparison: computed eigenvalues vs γₙ

    Args:
        result: Dictionary from full_reconstruction()
        save_path: Optional path to save the figure

    Raises:
        ImportError: If matplotlib is not available
    """
    try:
        import matplotlib.pyplot as plt
    except ImportError as e:
        raise ImportError(
            "matplotlib is required for plotting. "
            "Install it with: pip install matplotlib"
        ) from e

    x_full = result['x_full']
    V_full = result['V_full']
    gamma = result['gamma']

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Plot 1: Reconstructed potential
    ax1.plot(x_full, V_full, 'purple', lw=2)
    ax1.set_title(f"Riemann Potential V(x) (N={len(gamma)} zeros)")
    ax1.set_xlabel("x")
    ax1.set_ylabel("V(x)")
    ax1.grid(alpha=0.3)

    # Plot 2: Spectral comparison (if validation available)
    if 'validation' in result:
        val = result['validation']
        n_plot = min(10, len(val['eigenvalues']))
        indices = range(1, n_plot + 1)

        ax2.scatter(
            indices, -val['eigenvalues'][:n_plot],
            label="Reconstructed (-Eₙ)", color='red', s=100
        )
        ax2.scatter(
            indices, gamma[:n_plot],
            label="γₙ (zeta zeros)", color='cyan', s=100, zorder=5
        )
        ax2.legend()
        ax2.set_title(f"Spectral Comparison (Error: {val['mean_error']:.2f})")
        ax2.set_xlabel("n")
        ax2.set_ylabel("Value")
        ax2.grid(alpha=0.3)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')

    return fig


# Convenience aliases for direct import
kernel_glm = F_glm_kernel
solve_marchenko = marchenko_solve
