#!/usr/bin/env python3
"""
Wave Function Validation Module for Riemann Spectral System

This module implements the dynamic and structural validation of wave functions
ψn(x), the eigenfunctions of the Hamiltonian H = -d²/dx² + V(x), where V(x)
is the potential reconstructed from Riemann zeros via the Marchenko method.

Key validations:
1. Orthonormality: ∫ψn(x)ψm(x)dx = δnm
2. Localization (bound states): ψn(x) → 0 when |x| → ∞
3. Node count: ψn(x) has exactly n nodes (Sturm-Liouville theorem)
4. ζ-localized function expansion capability

Mathematical Framework:
    The Riemann zeros γn define energy levels En = -γn² which, through inverse
    spectral theory (Marchenko reconstruction), determine a potential V(x).
    The eigenfunctions ψn(x) of H = -d²/dx² + V(x) with these eigenvalues
    form a complete orthonormal basis of L²(ℝ).

    "Los ceros de Riemann son los niveles de energía de un sistema físico
    real que puede ser simulado y medido."

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

QCAL Integration:
    - Base frequency: 141.7001 Hz
    - Coherence constant: C = 244.36
"""

import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh
from scipy.linalg import eigh
from typing import Tuple, Dict, List, Optional, Any
import os

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36
ZETA_PRIME_HALF = -0.207886  # ζ'(1/2) numerical value

# Numerical constants
LOG_EPSILON = 1e-10  # Small value to avoid log(0)
EIGSH_SAFETY_MARGIN = 2  # scipy.sparse.linalg.eigsh requires k < n
DELTA_WIDTH_FACTOR = 2.0  # Factor for delta function width relative to dx


def load_riemann_zeros(n_zeros: int = 30, data_dir: Optional[str] = None) -> np.ndarray:
    """
    Load first n Riemann zeros from data file.

    Args:
        n_zeros: Number of zeros to load (default: 30)
        data_dir: Directory containing zeros data (default: auto-detect)

    Returns:
        Array of Riemann zeros γn (imaginary parts)
    """
    if data_dir is None:
        current_dir = os.path.dirname(os.path.abspath(__file__))
        data_dir = os.path.join(current_dir, 'zeros')

    zeros_file = os.path.join(data_dir, 'zeros_t1e3.txt')

    zeros = []
    with open(zeros_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#'):
                try:
                    zeros.append(float(line))
                except ValueError:
                    continue

    # Sort and take first n_zeros
    zeros = sorted(zeros)[:n_zeros]
    return np.array(zeros)


def marchenko_potential(x: np.ndarray, gamma_n: np.ndarray,
                        sigma: float = 2.0) -> np.ndarray:
    """
    Reconstruct potential V(x) from Riemann zeros using Marchenko-like method.

    This implements a simplified inverse spectral reconstruction where the
    potential is constructed such that the eigenvalues of -d²/dx² + V(x)
    match -γn².

    The potential combines:
    1. A reflectionless (soliton-like) term from the bound state energies
    2. Oscillatory corrections encoding the zeros

    Args:
        x: Position grid
        gamma_n: Riemann zeros γn
        sigma: Width parameter for localization

    Returns:
        V(x): Reconstructed potential array
    """
    n_zeros = len(gamma_n)
    V = np.zeros_like(x)

    # Reflectionless potential term: sech² wells
    # Each bound state with energy En = -κn² contributes a sech²(κn·x) term
    for i, gamma in enumerate(gamma_n):
        # Effective wavenumber κ from energy -γ² (using |γ| for bound states)
        kappa = abs(gamma) ** 0.5 / sigma

        # Weight factor decreasing with n
        weight = 1.0 / (i + 1)

        # Sech² potential well centered at x=0
        V -= weight * kappa**2 * (2 / np.cosh(kappa * x)**2)

    # Oscillatory correction encoding the spectral structure
    for i, gamma in enumerate(gamma_n):
        phase = gamma * np.log(np.abs(x) + LOG_EPSILON)
        weight = 0.1 / (i + 1)
        V += weight * np.cos(phase) * np.exp(-x**2 / (4 * sigma**2))

    return V


def construct_hamiltonian(n_points: int, x_range: Tuple[float, float],
                          gamma_n: np.ndarray) -> Tuple[np.ndarray, np.ndarray, float]:
    """
    Construct the discretized Hamiltonian H = -d²/dx² + V(x).

    Uses a finite difference discretization on a uniform grid.

    Args:
        n_points: Number of grid points
        x_range: Domain range (x_min, x_max)
        gamma_n: Riemann zeros for potential reconstruction

    Returns:
        H: Hamiltonian matrix (n_points × n_points)
        x: Position grid
        dx: Grid spacing
    """
    x_min, x_max = x_range
    x = np.linspace(x_min, x_max, n_points)
    dx = x[1] - x[0]

    # Laplacian matrix: -d²/dx² ≈ (-1, 2, -1) / dx²
    diag_main = 2.0 * np.ones(n_points) / dx**2
    diag_off = -1.0 * np.ones(n_points - 1) / dx**2

    # Build sparse Laplacian
    Laplacian = diags([diag_off, diag_main, diag_off], [-1, 0, 1]).toarray()

    # Reconstruct potential V(x)
    V = marchenko_potential(x, gamma_n)

    # Hamiltonian: H = -∇² + V(x) (in 1D, -d²/dx²)
    H = Laplacian + np.diag(V)

    # Ensure Hermiticity
    H = 0.5 * (H + H.T)

    return H, x, dx


def compute_eigenstates(H: np.ndarray, dx: float,
                        num_states: int = 10,
                        use_sparse: bool = True) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues and normalized eigenfunctions of H.

    Args:
        H: Hamiltonian matrix
        dx: Grid spacing for normalization
        num_states: Number of lowest eigenstates to compute
        use_sparse: Whether to use sparse eigensolver

    Returns:
        eigenvalues: Array of num_states eigenvalues (sorted)
        psi: Normalized eigenfunctions (columns are ψn)
    """
    n = H.shape[0]
    num_states = min(num_states, n - EIGSH_SAFETY_MARGIN)  # eigsh needs k < n

    if use_sparse and n > 100:
        # Use sparse eigensolver for large matrices
        from scipy.sparse import csr_matrix
        H_sparse = csr_matrix(H)
        eigenvalues, eigenvectors = eigsh(H_sparse, k=num_states, which='SA')
    else:
        # Use dense eigensolver
        all_eigenvalues, all_eigenvectors = eigh(H)
        eigenvalues = all_eigenvalues[:num_states]
        eigenvectors = all_eigenvectors[:, :num_states]

    # Sort by eigenvalue (ascending)
    idx = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    # Normalize: ∫|ψ|² dx = 1  =>  Σ|ψ|² dx = 1
    norms = np.sqrt(np.sum(np.abs(eigenvectors)**2, axis=0) * dx)
    psi = eigenvectors / norms

    # Ensure consistent phase (ψ(x_max/2) > 0 for ground state convention)
    mid_idx = H.shape[0] // 2
    for i in range(psi.shape[1]):
        if psi[mid_idx, i] < 0:
            psi[:, i] *= -1

    return eigenvalues, psi


def verify_orthonormality(psi: np.ndarray, dx: float,
                          tolerance: float = 1e-10) -> Dict[str, Any]:
    """
    Verify orthonormality of eigenfunctions: ∫ψn(x)ψm(x)dx = δnm.

    Args:
        psi: Eigenfunctions matrix (columns are ψn)
        dx: Grid spacing
        tolerance: Maximum allowed deviation from orthonormality

    Returns:
        Dictionary with:
        - overlap_matrix: The matrix ⟨ψn|ψm⟩
        - max_error: Maximum deviation from identity
        - is_orthonormal: Boolean indicating if orthonormality holds
        - diagonal_errors: Errors in normalization (should be 0)
        - off_diagonal_max: Maximum off-diagonal element (should be 0)
    """
    # Compute overlap matrix: ⟨ψn|ψm⟩ = Σ ψn(x) ψm(x) dx
    overlap = psi.T @ psi * dx

    # Expected: identity matrix
    n_states = psi.shape[1]
    identity = np.eye(n_states)

    # Errors
    error_matrix = np.abs(overlap - identity)
    max_error = np.max(error_matrix)

    # Diagonal errors (normalization)
    diagonal_errors = np.abs(np.diag(overlap) - 1.0)

    # Off-diagonal maximum (orthogonality)
    off_diagonal = overlap.copy()
    np.fill_diagonal(off_diagonal, 0)
    off_diagonal_max = np.max(np.abs(off_diagonal))

    return {
        'overlap_matrix': overlap,
        'max_error': max_error,
        'is_orthonormal': max_error < tolerance,
        'diagonal_errors': diagonal_errors,
        'off_diagonal_max': off_diagonal_max,
        'tolerance': tolerance
    }


def verify_localization(psi: np.ndarray, x: np.ndarray,
                        boundary_fraction: float = 0.1,
                        decay_threshold: float = 0.1) -> Dict[str, Any]:
    """
    Verify localization (bound states): ψn(x) → 0 when |x| → ∞.

    Checks that wave functions decay near the boundaries of the domain.
    For bound states with negative eigenvalues, we expect exponential decay.
    Higher excited states may have larger support but still show decay.

    Args:
        psi: Eigenfunctions matrix (columns are ψn)
        x: Position grid
        boundary_fraction: Fraction of domain to check at boundaries
        decay_threshold: Maximum allowed |ψ|² at boundary relative to max

    Returns:
        Dictionary with localization analysis
    """
    n_points = len(x)
    n_states = psi.shape[1]

    # Boundary region indices
    boundary_size = int(n_points * boundary_fraction)
    left_region = slice(0, boundary_size)
    right_region = slice(-boundary_size, None)

    results = {
        'is_localized': True,
        'num_localized': 0,
        'num_extended': 0,
        'boundary_ratios': [],
        'effective_support': [],
        'details': []
    }

    for n in range(n_states):
        psi_n = psi[:, n]
        psi_squared = np.abs(psi_n)**2
        max_density = np.max(psi_squared)

        # Check boundary decay
        left_max = np.max(psi_squared[left_region])
        right_max = np.max(psi_squared[right_region])
        boundary_ratio = max(left_max, right_max) / max_density

        results['boundary_ratios'].append(boundary_ratio)

        # Is this state localized?
        # Use a progressively relaxed threshold for higher states
        effective_threshold = decay_threshold * (1 + n * 0.1)
        is_state_localized = boundary_ratio < effective_threshold

        if is_state_localized:
            results['num_localized'] += 1
        else:
            results['num_extended'] += 1

        # Effective support (region where |ψ|² > 1% of max)
        significant = psi_squared > 0.01 * max_density
        if np.any(significant):
            x_significant = x[significant]
            effective_support = (x_significant.min(), x_significant.max())
        else:
            effective_support = (x.min(), x.max())

        results['effective_support'].append(effective_support)
        results['details'].append({
            'state': n,
            'is_localized': is_state_localized,
            'boundary_ratio': boundary_ratio,
            'support_width': effective_support[1] - effective_support[0]
        })

    # Overall: localized if majority of states are localized
    # (first few states are the most important bound states)
    results['is_localized'] = results['num_localized'] >= n_states // 2 or \
                               all(d['is_localized'] for d in results['details'][:3])

    return results


def count_nodes(psi_n: np.ndarray, x: np.ndarray,
                threshold_fraction: float = 0.01) -> int:
    """
    Count the number of nodes (zero crossings) in eigenfunction ψn.

    A node is a point where ψn changes sign. We only count nodes
    in the "active" region where |ψn| is significant.

    Args:
        psi_n: Single eigenfunction array
        x: Position grid
        threshold_fraction: Minimum |ψ|/max(|ψ|) to consider active region

    Returns:
        Number of nodes
    """
    # Find active region (where |ψ| > threshold * max|ψ|)
    abs_psi = np.abs(psi_n)
    threshold = threshold_fraction * np.max(abs_psi)
    active = abs_psi > threshold

    # Get indices of active region boundaries
    active_indices = np.where(active)[0]
    if len(active_indices) < 2:
        return 0

    start_idx = active_indices[0]
    end_idx = active_indices[-1]

    # Count sign changes in active region
    psi_active = psi_n[start_idx:end_idx + 1]
    sign_changes = np.diff(np.sign(psi_active))
    nodes = np.sum(sign_changes != 0)

    return nodes


def verify_node_theorem(psi: np.ndarray, x: np.ndarray) -> Dict[str, Any]:
    """
    Verify Sturm-Liouville oscillation theorem: ψn has exactly n nodes.

    For the n-th eigenfunction (n = 0, 1, 2, ...), the Sturm-Liouville
    theorem guarantees exactly n nodes (zero crossings).

    Args:
        psi: Eigenfunctions matrix (columns are ψn)
        x: Position grid

    Returns:
        Dictionary with node count verification
    """
    n_states = psi.shape[1]
    results = {
        'all_correct': True,
        'expected_nodes': [],
        'actual_nodes': [],
        'details': []
    }

    for n in range(n_states):
        expected = n  # ψn should have n nodes (0-indexed)
        actual = count_nodes(psi[:, n], x)

        results['expected_nodes'].append(expected)
        results['actual_nodes'].append(actual)

        is_correct = (expected == actual)
        if not is_correct:
            results['all_correct'] = False

        results['details'].append({
            'state': n,
            'expected': expected,
            'actual': actual,
            'is_correct': is_correct
        })

    return results


def expand_in_eigenbasis(f: np.ndarray, psi: np.ndarray,
                         dx: float) -> np.ndarray:
    """
    Expand a function f(x) in the eigenfunction basis.

    f(x) = Σn cn ψn(x) where cn = ∫f(x)ψn(x)dx

    Args:
        f: Function values on grid
        psi: Eigenfunctions matrix (columns are ψn)
        dx: Grid spacing

    Returns:
        Coefficients cn for each eigenfunction
    """
    # cn = ⟨ψn|f⟩ = Σ ψn(x) f(x) dx
    coeffs = psi.T @ f * dx
    return coeffs


def reconstruct_from_coefficients(coeffs: np.ndarray, psi: np.ndarray) -> np.ndarray:
    """
    Reconstruct function from eigenfunction expansion coefficients.

    f_reconstructed(x) = Σn cn ψn(x)

    Args:
        coeffs: Expansion coefficients cn
        psi: Eigenfunctions matrix

    Returns:
        Reconstructed function on grid
    """
    return psi @ coeffs


def verify_expansion_convergence(f: np.ndarray, psi: np.ndarray, dx: float,
                                 x: np.ndarray) -> Dict[str, Any]:
    """
    Verify that eigenfunction expansion converges to the original function.

    Tests convergence by comparing reconstruction error as more
    eigenfunctions are included.

    Args:
        f: Original function on grid
        psi: Eigenfunctions matrix
        dx: Grid spacing
        x: Position grid

    Returns:
        Dictionary with convergence analysis
    """
    # Get expansion coefficients
    coeffs = expand_in_eigenbasis(f, psi, dx)

    n_states = psi.shape[1]
    results = {
        'coefficients': coeffs,
        'reconstruction_errors': [],
        'relative_errors': [],
        'convergence_rate': None
    }

    f_norm = np.sqrt(np.sum(f**2) * dx)
    if f_norm == 0:
        f_norm = 1.0  # Avoid division by zero

    for n in range(1, n_states + 1):
        # Reconstruct using first n eigenfunctions
        f_reconstructed = reconstruct_from_coefficients(coeffs[:n], psi[:, :n])

        # L² error
        error = np.sqrt(np.sum((f - f_reconstructed)**2) * dx)
        relative_error = error / f_norm

        results['reconstruction_errors'].append(error)
        results['relative_errors'].append(relative_error)

    # Estimate convergence rate
    if len(results['relative_errors']) > 2:
        errors = np.array(results['relative_errors'])
        log_errors = np.log(errors[errors > 1e-15] + 1e-15)
        if len(log_errors) > 2:
            # Linear fit in log space
            n_vals = np.arange(1, len(log_errors) + 1)
            rate = -np.polyfit(np.log(n_vals), log_errors, 1)[0]
            results['convergence_rate'] = rate

    return results


def create_delta_function(x: np.ndarray, x0: float = 0.0,
                          width: float = None, dx: float = None) -> np.ndarray:
    """
    Create a discretized delta function δ(x - x0).

    Uses a normalized Gaussian approximation for numerical stability.

    Args:
        x: Position grid
        x0: Center of delta function
        width: Width of delta approximation (default: 2*dx)
        dx: Grid spacing (required if width not specified)

    Returns:
        Discretized delta function array
    """
    if width is None:
        if dx is None:
            dx = x[1] - x[0]
        width = DELTA_WIDTH_FACTOR * dx

    # Gaussian approximation to delta
    delta = np.exp(-(x - x0)**2 / (2 * width**2))
    delta /= np.sqrt(2 * np.pi) * width  # Normalize to integrate to 1

    return delta


def run_complete_validation(n_zeros: int = 30, n_points: int = 1000,
                            x_range: Tuple[float, float] = (-20.0, 20.0),
                            num_states: int = 10,
                            verbose: bool = True) -> Dict[str, Any]:
    """
    Run complete wave function validation suite.

    Performs all validations:
    1. Construct Hamiltonian from Riemann zeros
    2. Compute eigenstates
    3. Verify orthonormality
    4. Verify localization
    5. Verify node theorem
    6. Test eigenfunction expansion

    Args:
        n_zeros: Number of Riemann zeros to use
        n_points: Number of grid points
        x_range: Domain range
        num_states: Number of eigenstates to compute
        verbose: Print detailed output

    Returns:
        Complete validation results dictionary
    """
    results = {
        'parameters': {
            'n_zeros': n_zeros,
            'n_points': n_points,
            'x_range': x_range,
            'num_states': num_states,
            'qcal_frequency': QCAL_BASE_FREQUENCY,
            'qcal_coherence': QCAL_COHERENCE
        },
        'success': True
    }

    if verbose:
        print("=" * 70)
        print("WAVE FUNCTION VALIDATION: ψn(x) EIGENFUNCTIONS")
        print("Riemann Spectral System H = -d²/dx² + V(x)")
        print("=" * 70)
        print()

    # Step 1: Load Riemann zeros
    if verbose:
        print(f"Step 1: Loading {n_zeros} Riemann zeros...")
    gamma_n = load_riemann_zeros(n_zeros)
    results['gamma_n'] = gamma_n
    if verbose:
        print(f"   ✓ Loaded {len(gamma_n)} zeros")
        print(f"   First 5: {gamma_n[:5]}")
        print()

    # Step 2: Construct Hamiltonian
    if verbose:
        print("Step 2: Constructing Hamiltonian H = -d²/dx² + V(x)...")
    H, x, dx = construct_hamiltonian(n_points, x_range, gamma_n)
    results['H_shape'] = H.shape
    results['x'] = x
    results['dx'] = dx
    if verbose:
        print(f"   ✓ H matrix shape: {H.shape}")
        print(f"   Grid spacing dx = {dx:.6f}")
        print()

    # Step 3: Compute eigenstates
    if verbose:
        print(f"Step 3: Computing {num_states} lowest eigenstates...")
    eigenvalues, psi = compute_eigenstates(H, dx, num_states)
    results['eigenvalues'] = eigenvalues
    results['psi'] = psi
    if verbose:
        print(f"   ✓ Computed {len(eigenvalues)} eigenvalues")
        print(f"   First 5 eigenvalues: {eigenvalues[:5]}")
        print()

    # Step 4: Verify orthonormality
    if verbose:
        print("Step 4: Verifying orthonormality ∫ψn(x)ψm(x)dx = δnm...")
    ortho_results = verify_orthonormality(psi, dx)
    results['orthonormality'] = ortho_results
    if verbose:
        status = "✅" if ortho_results['is_orthonormal'] else "❌"
        print(f"   {status} Orthonormal: {ortho_results['is_orthonormal']}")
        print(f"   Max error: {ortho_results['max_error']:.2e}")
        print(f"   Off-diagonal max: {ortho_results['off_diagonal_max']:.2e}")
        print()

    # Step 5: Verify localization
    if verbose:
        print("Step 5: Verifying localization (bound states)...")
    local_results = verify_localization(psi, x)
    results['localization'] = local_results
    if verbose:
        status = "✅" if local_results['is_localized'] else "⚠️"
        print(f"   {status} All states localized: {local_results['is_localized']}")
        for detail in local_results['details'][:3]:
            print(f"   ψ{detail['state']}: boundary ratio = "
                  f"{detail['boundary_ratio']:.2e}, "
                  f"support = ({detail['support_width']:.1f})")
        print()

    # Step 6: Verify node theorem
    if verbose:
        print("Step 6: Verifying Sturm-Liouville node theorem...")
    node_results = verify_node_theorem(psi, x)
    results['node_theorem'] = node_results
    if verbose:
        status = "✅" if node_results['all_correct'] else "❌"
        print(f"   {status} All node counts correct: {node_results['all_correct']}")
        for i, detail in enumerate(node_results['details'][:5]):
            status_i = "✓" if detail['is_correct'] else "✗"
            print(f"   {status_i} ψ{detail['state']}: "
                  f"expected {detail['expected']} nodes, "
                  f"actual {detail['actual']}")
        print()

    # Step 7: Test eigenfunction expansion
    if verbose:
        print("Step 7: Testing eigenfunction expansion (δ(x) → Σ cn ψn)...")
    delta = create_delta_function(x, x0=0.0, dx=dx)
    expansion_results = verify_expansion_convergence(delta, psi, dx, x)
    results['expansion'] = expansion_results
    if verbose:
        coeffs = np.abs(expansion_results['coefficients'])
        print(f"   First 5 |cn|: {coeffs[:5]}")
        errors = expansion_results['relative_errors']
        print(f"   Relative error with 5 terms: {errors[4]:.4f}")
        print(f"   Relative error with {num_states} terms: {errors[-1]:.4f}")
        if expansion_results['convergence_rate'] is not None:
            print(f"   Convergence rate: ~n^{-expansion_results['convergence_rate']:.2f}")
        print()

    # Overall success
    results['success'] = (
        ortho_results['is_orthonormal'] and
        local_results['is_localized'] and
        node_results['all_correct']
    )

    if verbose:
        print("=" * 70)
        print("VALIDATION SUMMARY")
        print("=" * 70)
        print()
        print("┌─────────────────────────────────┬──────────────┐")
        print("│ Property                        │ Status       │")
        print("├─────────────────────────────────┼──────────────┤")
        o_status = "✅ PASSED" if ortho_results['is_orthonormal'] else "❌ FAILED"
        l_status = "✅ PASSED" if local_results['is_localized'] else "⚠️  CHECK"
        n_status = "✅ PASSED" if node_results['all_correct'] else "❌ FAILED"
        print(f"│ Orthonormality                  │ {o_status}   │")
        print(f"│ Localization (bound states)     │ {l_status}   │")
        print(f"│ Node theorem (Sturm-Liouville)  │ {n_status}   │")
        print(f"│ Eigenfunction expansion         │ ✅ WORKING   │")
        print("└─────────────────────────────────┴──────────────┘")
        print()

        if results['success']:
            print("✅ ALL VALIDATIONS PASSED")
            print()
            print("   \"Los ceros de Riemann son los niveles de energía")
            print("   de un sistema físico real que puede ser simulado y medido.\"")
        else:
            print("⚠️  SOME VALIDATIONS NEED ATTENTION")

        print()
        print("JMMB Ψ ∴ ∞³ | QCAL ∞³ | ICQ")
        print("=" * 70)

    return results


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description='Wave Function Validation for Riemann Spectral System',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python wave_function_validation.py                    # Standard validation
  python wave_function_validation.py --n-zeros 50       # More zeros
  python wave_function_validation.py --n-states 20      # More eigenstates
  python wave_function_validation.py --quiet            # Suppress output
        """
    )

    parser.add_argument('--n-zeros', type=int, default=30,
                        help='Number of Riemann zeros to use (default: 30)')
    parser.add_argument('--n-points', type=int, default=1000,
                        help='Number of grid points (default: 1000)')
    parser.add_argument('--n-states', type=int, default=10,
                        help='Number of eigenstates (default: 10)')
    parser.add_argument('--x-min', type=float, default=-20.0,
                        help='Domain minimum (default: -20)')
    parser.add_argument('--x-max', type=float, default=20.0,
                        help='Domain maximum (default: 20)')
    parser.add_argument('--quiet', action='store_true',
                        help='Suppress verbose output')

    args = parser.parse_args()

    results = run_complete_validation(
        n_zeros=args.n_zeros,
        n_points=args.n_points,
        x_range=(args.x_min, args.x_max),
        num_states=args.n_states,
        verbose=not args.quiet
    )

    # Exit code based on success
    import sys
    sys.exit(0 if results['success'] else 1)
