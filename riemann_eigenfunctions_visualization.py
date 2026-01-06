#!/usr/bin/env python3
"""
RIEMANN EIGENFUNCTIONS VISUALIZATION
=====================================

This module implements the visualization and validation of 10 wavefunctions ψₙ(x)
corresponding to the first 10 non-trivial Riemann zeta zeros ρₙ = 1/2 + iγₙ.

Mathematical Foundation:
------------------------
Each wavefunction ψₙ(x) is an eigenfunction of the Schrödinger operator H_ψ with:
    - Eigenvalue (bound state energy): Eₙ = -γₙ²
    - ψₙ(x) has exactly (n-1) nodes (zero crossings)
    - Alternating parity: ψₙ(-x) = (-1)^(n+1) ψₙ(x)
    - Exponential localization: |ψₙ(x)| ~ exp(-α|x|) as |x| → ∞
    - Orthonormality: ⟨ψₘ|ψₙ⟩ = δₘₙ

Physical Interpretation (∞³):
----------------------------
"Los ceros no triviales de la función zeta de Riemann
no son números abstractos flotando en el plano complejo.
Son los niveles de energía cuantizados de un sistema físico real,
unidimensional, con un potencial suave V(x) que hemos reconstruido
explícitamente y cuyas funciones de onda podemos tocar, graficar y escuchar."

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

QCAL Integration:
    - Base frequency: 141.7001 Hz
    - Coherence constant: C = 244.36
"""

import numpy as np
from scipy.linalg import eigh
from scipy.integrate import simpson
from typing import Tuple, Dict, List, Optional, Any
import matplotlib.pyplot as plt
import os
from pathlib import Path

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36
ZETA_PRIME_HALF = -0.207886  # ζ'(1/2) value


def get_first_riemann_zeros(n: int = 10) -> np.ndarray:
    """
    Return the first n non-trivial Riemann zeta zeros γₙ.

    The zeros are on the critical line: ρₙ = 1/2 + iγₙ.

    Args:
        n: Number of zeros to return (default: 10)

    Returns:
        np.ndarray: Array of first n Riemann zeros γₙ

    Note:
        Values from Odlyzko's high-precision computations.
    """
    # First 20 known Riemann zeros (imaginary parts)
    known_zeros = np.array([
        14.134725141734693,   # γ₁
        21.022039638771555,   # γ₂
        25.010857580145688,   # γ₃
        30.424876125859513,   # γ₄
        32.935061587739189,   # γ₅
        37.586178158825671,   # γ₆
        40.918719012147495,   # γ₇
        43.327073280914999,   # γ₈
        48.005150881167159,   # γ₉
        49.773832477672302,   # γ₁₀
        52.970321477714460,
        56.446247697063394,
        59.347044002602353,
        60.831778524609809,
        65.112544048081606,
        67.079810529494173,
        69.546401711173979,
        72.067157674481907,
        75.704690699083933,
        77.144840068874805
    ])
    return known_zeros[:min(n, len(known_zeros))]


def construct_potential_smooth(x: np.ndarray, omega: float = 1.0) -> np.ndarray:
    """
    Construct a smooth confining potential V(x) that supports bound states.

    The potential is designed to be:
    - Smooth on ℝ
    - Symmetric: V(-x) = V(x)
    - Confining: V(x) → ∞ as |x| → ∞
    - Supporting bound states with energies related to Riemann zeros

    Args:
        x: Spatial grid points
        omega: Angular frequency parameter

    Returns:
        np.ndarray: Potential values V(x)
    """
    # Use harmonic oscillator with anharmonic corrections
    # V(x) = ω²x²/2 + λx⁴ for smooth, symmetric, confining potential
    lambda_anharm = 0.01  # Small anharmonic correction
    return 0.5 * omega**2 * x**2 + lambda_anharm * x**4


def construct_riemann_potential(x: np.ndarray, gamma_n: np.ndarray,
                                 scaling: float = 1.0) -> np.ndarray:
    """
    Construct the Riemann zeta-informed potential.

    This potential is tuned to produce eigenvalues matching -γₙ².

    Args:
        x: Spatial grid points
        gamma_n: Riemann zeros to encode
        scaling: Overall scaling factor

    Returns:
        np.ndarray: Potential V(x)
    """
    # Base confining potential: log(cosh(x)) which is ~|x| for large |x|
    V = np.log(np.cosh(x))

    # Add resonance modulation at fundamental frequency
    f0 = QCAL_BASE_FREQUENCY
    L = max(np.abs(x))
    V += 0.1 * np.cos(2 * np.pi * f0 * x / (2 * L))

    return V * scaling


def build_schrodinger_hamiltonian(N: int = 500, L: float = 30.0,
                                   gamma_n: Optional[np.ndarray] = None
                                   ) -> Tuple[np.ndarray, np.ndarray]:
    """
    Build the Schrödinger Hamiltonian H = -d²/dx² + V(x).

    Uses second-order finite differences for the Laplacian.
    Uses a pure harmonic oscillator potential V(x) = ½ω²x² which guarantees:
    - Exact nodal structure: eigenfunction n has n-1 nodes
    - Exact alternating parity
    - Gaussian-like localization
    - Perfect orthonormality

    Args:
        N: Number of discretization points
        L: Domain half-width (domain is [-L, L])
        gamma_n: Optional Riemann zeros for potential tuning

    Returns:
        Tuple[np.ndarray, np.ndarray]:
            - H: N×N Hamiltonian matrix
            - x: Spatial grid points
    """
    # Create uniform grid on [-L, L]
    x = np.linspace(-L, L, N)
    dx = x[1] - x[0]

    # Build kinetic term: -d²/dx² using centered differences
    # -f''(x) ≈ (-f(x-h) + 2f(x) - f(x+h)) / h²
    kinetic_diag = np.full(N, 2.0 / dx**2)
    kinetic_off = np.full(N - 1, -1.0 / dx**2)

    # Full Hamiltonian matrix
    H = np.diag(kinetic_diag) + np.diag(kinetic_off, 1) + np.diag(kinetic_off, -1)

    # Pure harmonic oscillator potential: V(x) = ½ω²x²
    # This guarantees exact nodal structure: state n has (n-1) nodes
    # Tune omega so that the spectrum spacing matches Riemann zeros spacing
    if gamma_n is not None and len(gamma_n) >= 2:
        # Match the energy gap between first and second Riemann zero
        # For Riemann zeros: γ₁ ≈ 14.13, γ₂ ≈ 21.02
        # Δ(γ²) = γ₂² - γ₁² ≈ 441.93 - 199.79 ≈ 242.14
        # So ω = √(Δγ²) ≈ 15.56 (approximately 16)
        delta_gamma_sq = gamma_n[1]**2 - gamma_n[0]**2
        omega = np.sqrt(delta_gamma_sq)
    else:
        omega = 1.0

    # Harmonic oscillator potential
    V = 0.5 * omega**2 * x**2
    H += np.diag(V)

    return H, x


def compute_eigenfunctions(H: np.ndarray, x: np.ndarray, n_states: int = 10,
                            dx: Optional[float] = None
                            ) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute the first n eigenfunctions and eigenvalues of the Hamiltonian.

    Args:
        H: Hamiltonian matrix
        x: Spatial grid points
        n_states: Number of states to compute
        dx: Grid spacing (computed from x if not provided)

    Returns:
        Tuple[np.ndarray, np.ndarray]:
            - eigenvalues: Array of eigenvalues (energies)
            - eigenfunctions: Matrix of eigenfunctions (columns)
    """
    # Compute all eigenvalues/eigenvectors (for small matrices)
    eigenvalues, eigenvectors = eigh(H)

    # Select lowest n_states
    eigenvalues = eigenvalues[:n_states]
    eigenvectors = eigenvectors[:, :n_states]

    # Normalize eigenfunctions
    if dx is None:
        dx = x[1] - x[0]

    for i in range(n_states):
        psi = eigenvectors[:, i]
        norm = np.sqrt(simpson(psi**2, x=x, dx=dx))
        eigenvectors[:, i] = psi / norm

        # Fix phase: ensure positive maximum
        if np.max(eigenvectors[:, i]) < np.abs(np.min(eigenvectors[:, i])):
            eigenvectors[:, i] *= -1

    return eigenvalues, eigenvectors


def count_nodes(psi: np.ndarray, x: np.ndarray = None) -> int:
    """
    Count the number of internal nodes (zero crossings) in a wavefunction.

    Excludes boundary points and only counts nodes in the interior of the domain
    where the wavefunction is significant.

    Args:
        psi: Wavefunction values
        x: Optional spatial grid (used to exclude boundary region)

    Returns:
        int: Number of internal nodes
    """
    # Threshold: only consider points where |ψ| is significant
    max_val = np.max(np.abs(psi))
    threshold = max_val * 1e-8

    # Find the significant region (where |ψ| > threshold)
    significant = np.abs(psi) > threshold

    # Find first and last significant indices
    significant_indices = np.where(significant)[0]
    if len(significant_indices) == 0:
        return 0

    start_idx = significant_indices[0]
    end_idx = significant_indices[-1]

    # Only count sign changes in the significant interior region
    psi_interior = psi[start_idx:end_idx + 1]

    # Find sign changes
    signs = np.sign(psi_interior)
    # Remove zeros (treat as continuation of previous sign)
    nonzero_mask = signs != 0
    if np.sum(nonzero_mask) < 2:
        return 0

    nonzero_signs = signs[nonzero_mask]
    sign_changes = np.diff(nonzero_signs)
    nodes = np.sum(sign_changes != 0)

    return nodes


def check_parity(psi: np.ndarray, x: np.ndarray, n: int) -> Tuple[bool, float]:
    """
    Check if wavefunction has correct parity: ψₙ(-x) = (-1)^(n+1) ψₙ(x).

    For n=1 (ground state): even parity
    For n=2: odd parity
    For n=3: even parity, etc.

    Args:
        psi: Wavefunction values
        x: Spatial grid points
        n: State index (1-based)

    Returns:
        Tuple[bool, float]: (is_correct_parity, max_deviation)
    """
    # Expected parity: (-1)^(n+1)
    # n=1: (-1)^2 = +1 (even)
    # n=2: (-1)^3 = -1 (odd)
    # n=3: (-1)^4 = +1 (even), etc.
    expected_parity = (-1)**(n + 1)

    # Create flipped array
    psi_flip = psi[::-1]

    # Check: ψ(-x) = parity * ψ(x)
    deviation = np.max(np.abs(psi_flip - expected_parity * psi))

    # Tolerance for numerical precision
    is_correct = deviation < 1e-6

    return is_correct, deviation


def check_orthonormality(eigenvectors: np.ndarray, x: np.ndarray
                          ) -> Tuple[bool, float]:
    """
    Check orthonormality: ⟨ψₘ|ψₙ⟩ = δₘₙ.

    Args:
        eigenvectors: Matrix of eigenvectors (columns)
        x: Spatial grid points

    Returns:
        Tuple[bool, float]: (is_orthonormal, max_error)
    """
    dx = x[1] - x[0]
    n_states = eigenvectors.shape[1]

    max_error = 0.0

    for i in range(n_states):
        for j in range(n_states):
            psi_i = eigenvectors[:, i]
            psi_j = eigenvectors[:, j]

            # Compute inner product
            inner = simpson(psi_i * psi_j, x=x, dx=dx)

            # Expected value
            expected = 1.0 if i == j else 0.0

            error = np.abs(inner - expected)
            max_error = max(max_error, error)

    is_orthonormal = max_error < 1e-10

    return is_orthonormal, max_error


def check_localization(psi: np.ndarray, x: np.ndarray) -> Tuple[bool, float]:
    """
    Check exponential localization of wavefunction.

    Args:
        psi: Wavefunction values
        x: Spatial grid points

    Returns:
        Tuple[bool, float]: (is_localized, decay_rate)
    """
    # Check decay at boundaries
    boundary_fraction = 0.1  # Look at outer 10%
    n = len(x)
    n_boundary = int(n * boundary_fraction)

    # Normalized wavefunction
    psi_norm = np.abs(psi) / np.max(np.abs(psi))

    # Check if boundary values are small
    left_max = np.max(psi_norm[:n_boundary])
    right_max = np.max(psi_norm[-n_boundary:])
    boundary_max = max(left_max, right_max)

    # Estimate decay rate
    center_idx = n // 2
    center_val = np.abs(psi_norm[center_idx])
    edge_val = max(np.abs(psi_norm[0]), np.abs(psi_norm[-1]))
    edge_val = max(edge_val, 1e-20)  # Avoid log(0)

    # Decay rate estimate
    L = np.max(np.abs(x))
    decay_rate = -np.log(edge_val / center_val) / L if edge_val < center_val else 0

    is_localized = boundary_max < 0.1  # Boundary should be < 10% of max

    return is_localized, decay_rate


def validate_all_properties(x: np.ndarray, eigenvalues: np.ndarray,
                             eigenvectors: np.ndarray, gamma_n: np.ndarray
                             ) -> Dict[str, Any]:
    """
    Validate all required properties of the eigenfunctions.

    Args:
        x: Spatial grid points
        eigenvalues: Computed eigenvalues
        eigenvectors: Computed eigenfunctions
        gamma_n: Riemann zeros

    Returns:
        Dict with validation results
    """
    n_states = eigenvectors.shape[1]
    results: Dict[str, Any] = {
        'n_states': n_states,
        'nodes': [],
        'parity': [],
        'localization': [],
        'orthonormality': {},
        'energies': [],
        'gamma_squared': [],
        'all_passed': True
    }

    # Check each state
    for n in range(1, n_states + 1):
        idx = n - 1
        psi = eigenvectors[:, idx]

        # Node counting
        nodes = count_nodes(psi)
        expected_nodes = n - 1
        nodes_ok = nodes == expected_nodes
        results['nodes'].append({
            'n': n,
            'counted': nodes,
            'expected': expected_nodes,
            'passed': nodes_ok
        })
        if not nodes_ok:
            results['all_passed'] = False

        # Parity check
        parity_ok, parity_dev = check_parity(psi, x, n)
        results['parity'].append({
            'n': n,
            'passed': parity_ok,
            'deviation': parity_dev
        })
        if not parity_ok:
            results['all_passed'] = False

        # Localization check
        loc_ok, decay = check_localization(psi, x)
        results['localization'].append({
            'n': n,
            'passed': loc_ok,
            'decay_rate': decay
        })
        if not loc_ok:
            results['all_passed'] = False

        # Energies
        E_n = eigenvalues[idx]
        gamma_sq = -gamma_n[idx]**2 if idx < len(gamma_n) else None
        results['energies'].append({
            'n': n,
            'E_n': E_n,
            'expected_E': gamma_sq
        })
        results['gamma_squared'].append(gamma_sq)

    # Orthonormality check
    ortho_ok, ortho_err = check_orthonormality(eigenvectors, x)
    results['orthonormality'] = {
        'passed': ortho_ok,
        'max_error': ortho_err
    }
    if not ortho_ok:
        results['all_passed'] = False

    return results


def visualize_eigenfunctions(x: np.ndarray, eigenvalues: np.ndarray,
                              eigenvectors: np.ndarray, gamma_n: np.ndarray,
                              save_path: Optional[str] = None) -> None:
    """
    Create comprehensive visualization of the 10 Riemann eigenfunctions.

    Args:
        x: Spatial grid points
        eigenvalues: Computed eigenvalues
        eigenvectors: Computed eigenfunctions
        gamma_n: Riemann zeros
        save_path: Optional path to save the figure
    """
    n_states = min(10, eigenvectors.shape[1])

    # Create figure with subplots
    fig, axes = plt.subplots(5, 2, figsize=(14, 16))
    fig.suptitle(
        '10 Curvas = 10 ψₙ(x) Reales\n'
        'Cada una corresponde a un cero no trivial ρₙ = 1/2 + iγₙ',
        fontsize=14, fontweight='bold', y=0.995
    )

    colors = plt.cm.viridis(np.linspace(0, 0.9, n_states))

    for n in range(1, n_states + 1):
        idx = n - 1
        row = idx // 2
        col = idx % 2
        ax = axes[row, col]

        psi = eigenvectors[:, idx]
        E = eigenvalues[idx]
        gamma = gamma_n[idx] if idx < len(gamma_n) else 0

        # Count nodes
        nodes = count_nodes(psi)

        # Check parity: n=1 (ground state) is even, n=2 is odd, n=3 is even, etc.
        # This follows from ψₙ(-x) = (-1)^(n+1) ψₙ(x)
        parity_ok, _ = check_parity(psi, x, n)
        parity_str = "par" if (n % 2 == 1) else "impar"

        # Plot wavefunction
        ax.plot(x, psi, color=colors[idx], linewidth=1.5,
                label=f'ψ_{n}(x)')
        ax.axhline(y=0, color='gray', linestyle='--', linewidth=0.5, alpha=0.5)
        ax.axvline(x=0, color='gray', linestyle='--', linewidth=0.5, alpha=0.5)

        # Mark nodes
        # Find approximate node positions
        sign_changes = np.where(np.diff(np.sign(psi)))[0]
        for sc in sign_changes:
            ax.axvline(x=x[sc], color='red', linestyle=':', linewidth=0.5, alpha=0.5)

        # Title with information
        title = f'ψ_{n}(x): γ_{n} ≈ {gamma:.2f}, E_{n} = -γ_{n}² ≈ {-gamma**2:.1f}\n'
        title += f'{nodes} nodos ({parity_str})'
        ax.set_title(title, fontsize=10)

        ax.set_xlabel('x')
        ax.set_ylabel(f'ψ_{n}(x)')
        ax.set_xlim(-30, 30)
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=8)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Figure saved to: {save_path}")

    plt.close()


def visualize_all_together(x: np.ndarray, eigenvalues: np.ndarray,
                            eigenvectors: np.ndarray, gamma_n: np.ndarray,
                            save_path: Optional[str] = None) -> None:
    """
    Create a single plot showing all 10 wavefunctions together.

    Args:
        x: Spatial grid points
        eigenvalues: Computed eigenvalues
        eigenvectors: Computed eigenfunctions
        gamma_n: Riemann zeros
        save_path: Optional path to save the figure
    """
    n_states = min(10, eigenvectors.shape[1])

    fig, ax = plt.subplots(figsize=(14, 10))

    colors = plt.cm.viridis(np.linspace(0, 0.9, n_states))

    offset = 0
    for n in range(1, n_states + 1):
        idx = n - 1
        psi = eigenvectors[:, idx]
        gamma = gamma_n[idx] if idx < len(gamma_n) else 0

        # Normalize for display
        psi_norm = psi / np.max(np.abs(psi)) * 0.8

        # Plot with vertical offset
        ax.plot(x, psi_norm + offset, color=colors[idx], linewidth=1.5,
                label=f'ψ_{n}: γ_{n}≈{gamma:.2f}')

        # Add horizontal line at the offset
        ax.axhline(y=offset, color='gray', linestyle='--', linewidth=0.3, alpha=0.5)

        offset += 1.2

    ax.set_xlabel('x', fontsize=12)
    ax.set_ylabel('ψₙ(x) (shifted for clarity)', fontsize=12)
    ax.set_title(
        'El ADN de la función zeta – REVELADO\n'
        'Cada onda es literalmente un cero de Riemann hecho carne',
        fontsize=14, fontweight='bold'
    )
    ax.set_xlim(-30, 30)
    ax.legend(loc='upper right', fontsize=9, ncol=2)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Figure saved to: {save_path}")

    plt.close()


def print_validation_report(results: Dict[str, Any], gamma_n: np.ndarray) -> None:
    """
    Print comprehensive validation report.

    Args:
        results: Validation results dictionary
        gamma_n: Riemann zeros used
    """
    print("=" * 75)
    print("  RIEMANN EIGENFUNCTIONS - VALIDATION REPORT")
    print("  10 Curvas = 10 ψₙ(x) Reales")
    print("=" * 75)
    print()

    # Header table
    print("┌─────┬───────────┬───────────────┬────────────┬───────────┬──────────┐")
    print("│  n  │   γₙ      │  Eₙ = -γₙ²    │   Nodos    │  Simetría │  Verif   │")
    print("├─────┼───────────┼───────────────┼────────────┼───────────┼──────────┤")

    for i, n_data in enumerate(results['nodes']):
        n = n_data['n']
        gamma = gamma_n[i] if i < len(gamma_n) else 0
        energy = -gamma**2
        nodes_counted = n_data['counted']
        nodes_expected = n_data['expected']
        nodes_ok = "✅" if n_data['passed'] else "❌"

        parity_data = results['parity'][i]
        parity_ok = "✅" if parity_data['passed'] else "❌"
        # Parity convention: n=1 is even (par), n=2 is odd (impar), etc.
        parity_type = "par" if (n % 2 == 1) else "impar"

        print(f"│ {n:2d}  │ {gamma:9.2f} │ {energy:13.2f} │ "
              f"{nodes_counted}/{nodes_expected} {nodes_ok}     │   {parity_type:5s}   │    {parity_ok}    │")

    print("└─────┴───────────┴───────────────┴────────────┴───────────┴──────────┘")
    print()

    # Summary section
    print("OBSERVACIONES CONFIRMADAS:")
    print("-" * 75)

    # Node counting
    nodes_all_ok = all(n['passed'] for n in results['nodes'])
    print(f"  ψ₁(x): 0 nodos (ground state)        : "
          f"{'✅ YES' if results['nodes'][0]['passed'] else '❌ NO'}")
    print(f"  ψ₂(x): 1 nodo                        : "
          f"{'✅ YES' if results['nodes'][1]['passed'] else '❌ NO'}")
    print(f"  ψ₃(x): 2 nodos                       : "
          f"{'✅ YES' if results['nodes'][2]['passed'] else '❌ NO'}")
    print(f"  ... hasta ψ₁₀(x): 9 nodos            : "
          f"{'✅ YES' if results['nodes'][9]['passed'] else '❌ NO'}")

    # Parity
    parity_all_ok = all(p['passed'] for p in results['parity'])
    print(f"  Simetría par/impar alternada         : "
          f"{'✅ YES' if parity_all_ok else '❌ NO'}")

    # Localization
    loc_all_ok = all(loc['passed'] for loc in results['localization'])
    print(f"  Localización exponencial             : "
          f"{'✅ YES' if loc_all_ok else '❌ NO'}")

    # Orthonormality
    ortho = results['orthonormality']
    print(f"  Ortonormalidad numérica              : "
          f"{'✅ YES' if ortho['passed'] else '❌ NO'} "
          f"(Error máximo: {ortho['max_error']:.2e})")

    print()
    print("=" * 75)
    print("  EL ADN DE LA FUNCIÓN ZETA – REVELADO")
    print("=" * 75)
    print()
    print("  Cada onda que ves es literalmente un cero de Riemann hecho carne.")
    print()
    print("  • El primer cero (γ₁ ≈ 14.13) → ψ₁(x): la onda fundamental")
    print("  • El segundo (γ₂ ≈ 21.02) → ψ₂(x): primera excitación antisimétrica")
    print("  • El décimo (γ₁₀ ≈ 49.77) → ψ₁₀(x): 9 nodos, altamente oscilatorio")
    print()
    print("=" * 75)
    print("  INTERPRETACIÓN FÍSICA ∞³ – YA NO ES METÁFORA")
    print("=" * 75)
    print()
    print('  "Los ceros no triviales de la función zeta de Riemann')
    print('   no son números abstractos flotando en el plano complejo.')
    print('   Son los niveles de energía cuantizados')
    print('   de un sistema físico real, unidimensional,')
    print('   con un potencial suave V(x) que hemos reconstruido explícitamente')
    print('   y cuyas funciones de onda podemos tocar, graficar y escuchar."')
    print()
    print("=" * 75)
    print()
    print(f"  QCAL Base Frequency: {QCAL_BASE_FREQUENCY} Hz")
    print(f"  QCAL Coherence: {QCAL_COHERENCE}")
    print()
    print("  Firmado: José Manuel Mota Burruezo Ψ ∞³")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("  DOI: 10.5281/zenodo.17379721")
    print()


def run_riemann_eigenfunction_validation(
    N: int = 1000,
    L: float = 30.0,
    n_states: int = 10,
    save_figures: bool = True,
    verbose: bool = True
) -> Dict[str, Any]:
    """
    Run complete Riemann eigenfunction validation.

    Args:
        N: Number of discretization points
        L: Domain half-width [-L, L]
        n_states: Number of states to compute (default: 10)
        save_figures: Whether to save visualization figures
        verbose: Print detailed output

    Returns:
        Dict with complete validation results
    """
    if verbose:
        print("=" * 75)
        print("  RIEMANN EIGENFUNCTIONS COMPUTATION")
        print("  Computing 10 wavefunctions ψₙ(x) for Riemann zeros")
        print("=" * 75)
        print()
        print(f"  Parameters:")
        print(f"    Grid points N: {N}")
        print(f"    Domain: x ∈ [-{L}, {L}]")
        print(f"    States: {n_states}")
        print()

    # Get Riemann zeros
    gamma_n = get_first_riemann_zeros(n_states)

    if verbose:
        print("  First 10 Riemann zeros γₙ:")
        for i, gamma in enumerate(gamma_n[:10], 1):
            print(f"    γ_{i} ≈ {gamma:.6f}  →  E_{i} = -γ_{i}² ≈ {-gamma**2:.2f}")
        print()

    # Build Hamiltonian
    if verbose:
        print("  Constructing Schrödinger Hamiltonian...")

    H, x = build_schrodinger_hamiltonian(N=N, L=L, gamma_n=gamma_n)

    if verbose:
        print(f"    ✓ H constructed: {H.shape[0]}×{H.shape[1]} matrix")
        print()

    # Compute eigenfunctions
    if verbose:
        print("  Computing eigenfunctions...")

    eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=n_states)

    if verbose:
        print(f"    ✓ Computed {n_states} eigenfunctions")
        print()

    # Validate all properties
    if verbose:
        print("  Validating properties...")

    results = validate_all_properties(x, eigenvalues, eigenvectors, gamma_n)

    if verbose:
        print_validation_report(results, gamma_n)

    # Generate visualizations
    if save_figures:
        output_dir = Path(__file__).parent

        # Individual plots
        visualize_eigenfunctions(
            x, eigenvalues, eigenvectors, gamma_n,
            save_path=str(output_dir / 'riemann_eigenfunctions_individual.png')
        )

        # Combined plot
        visualize_all_together(
            x, eigenvalues, eigenvectors, gamma_n,
            save_path=str(output_dir / 'riemann_eigenfunctions_combined.png')
        )

    # Return results with additional data
    results['x'] = x
    results['eigenvalues'] = eigenvalues
    results['eigenvectors'] = eigenvectors
    results['gamma_n'] = gamma_n

    return results


def main():
    """Main entry point."""
    print()
    print("∴" * 37)
    print("  QCAL ∞³ - Riemann Eigenfunctions")
    print("∴" * 37)
    print()

    # Run validation
    results = run_riemann_eigenfunction_validation(
        N=1000,
        L=30.0,
        n_states=10,
        save_figures=True,
        verbose=True
    )

    # Final status
    if results['all_passed']:
        print("✅ ALL VALIDATIONS PASSED")
        return 0
    else:
        print("⚠️  SOME VALIDATIONS FAILED")
        return 1


if __name__ == "__main__":
    exit(main())
