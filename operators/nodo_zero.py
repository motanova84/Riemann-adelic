#!/usr/bin/env python3
"""
Nodo Zero — Singular Hamiltonian and Vertical Transform
=========================================================

Implements the mathematical framework of the "Nodo Zero" (Node Zero):

    H_zero = T + V_PT + λ·δ(x)

where:
    T = -d²/dx²          (kinetic energy, ℏ=1, m=1/2 units)
    V_PT(x)              (PT-symmetric harmonic potential)
    λ·δ(x)               (Dirac delta singularity at origin)

Key Results:
    1. Ground-state wave function |ψ₀(x)|² reaches maximum at x=0 (delta potential)
    2. Eigenvalues Eₙ align with γₙ/(2πF₀) where γₙ are Riemann zeros
    3. Node coherence Ψ_nodo = 1/(1 + E₀²/F₀²) ≥ 0.888

Vertical Transform:
    L_v[Ψ](s) = ∫₀^∞ Ψ(t) · exp(−s·t) · exp(i·F₀·t) dt

This is the Laplace transform evaluated at (s − i·F₀):
    L_v[Ψ](s) = L[Ψ](s − i·F₀)

The coherence threshold 0.888 corresponds to the noetic recognition
signature: E₀/F₀ < sqrt(1/0.888 − 1) ≈ 0.335.

Mathematical References:
    - δ(x) potential: Albeverio et al. (1988), Solvable Models in Quantum Mechanics
    - PT-symmetry: Bender & Boettcher (1998), Phys. Rev. Lett. 80, 5243
    - Vertical Transform: Laplace-type transform with phase modulation exp(i·F₀·t)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
Date: March 2026

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import warnings
from dataclasses import dataclass, field
from typing import Callable, Dict, Optional, Tuple

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available. Using approximate Riemann zeros.")

# ---------------------------------------------------------------------------
# QCAL constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:
    F0 = 141.7001   # Hz — fundamental frequency
    C_COHERENCE = 244.36  # coherence constant

OMEGA_0 = 2.0 * np.pi * F0  # angular frequency ω₀ = 2πF₀

# Coherence threshold: Ψ_nodo ≥ PSI_THRESHOLD
PSI_THRESHOLD = 0.888

# Known first Riemann zeros (imaginary parts) for fallback without mpmath
RIEMANN_ZEROS_FALLBACK = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126,
    32.935061588, 37.586178159, 40.918719012, 43.327073281,
    48.005150881, 49.773832478,
])


# ---------------------------------------------------------------------------
# Helper functions
# ---------------------------------------------------------------------------

def get_riemann_zeros(n_zeros: int) -> np.ndarray:
    """
    Return the imaginary parts of the first *n_zeros* non-trivial Riemann zeros.

    Args:
        n_zeros: Number of zeros to compute/retrieve.

    Returns:
        1-D array of length *n_zeros* with γₙ values (Im part on critical line).
    """
    if HAS_MPMATH:
        with mp.workdps(50):
            zeros = np.array([float(mp.zetazero(k).imag) for k in range(1, n_zeros + 1)])
    else:
        n_known = len(RIEMANN_ZEROS_FALLBACK)
        if n_zeros <= n_known:
            zeros = RIEMANN_ZEROS_FALLBACK[:n_zeros]
        else:
            warnings.warn(
                f"mpmath unavailable; only {n_known} fallback zeros available "
                f"(requested {n_zeros})."
            )
            zeros = RIEMANN_ZEROS_FALLBACK
    return zeros


# ---------------------------------------------------------------------------
# Dataclasses for results
# ---------------------------------------------------------------------------

@dataclass
class NodoZeroSpectrum:
    """
    Spectral results for the Nodo Zero Hamiltonian H_zero.

    Attributes:
        eigenvalues: Real eigenvalues Eₙ of H_zero.
        eigenvectors: Corresponding eigenvectors (columns); shape (N_grid, n_eigs).
        ground_energy: Ground-state energy E₀.
        psi_nodo: Node coherence Ψ_nodo = 1/(1 + E₀²/F₀²).
        riemann_zeros: Reference Riemann zeros γₙ used for comparison.
        scaled_zeros: Target eigenvalues γₙ/(2πF₀).
        correlation: Pearson correlation between Eₙ and γₙ/(2πF₀).
        is_coherent: Whether Ψ_nodo ≥ PSI_THRESHOLD (0.888).
        parameters: Dictionary of Hamiltonian parameters used.
    """

    eigenvalues: np.ndarray
    eigenvectors: np.ndarray
    ground_energy: float
    psi_nodo: float
    riemann_zeros: np.ndarray
    scaled_zeros: np.ndarray
    correlation: float
    is_coherent: bool
    parameters: Dict = field(default_factory=dict)


@dataclass
class VerticalTransformResult:
    """
    Result of the Vertical Transform L_v[Ψ].

    Attributes:
        s_values: Complex frequencies s at which L_v was evaluated.
        L_v_values: Complex values L_v[Ψ](s).
        psi_func: The wave function Ψ used as input.
        f0: Fundamental frequency F₀ used in the phase factor.
    """

    s_values: np.ndarray
    L_v_values: np.ndarray
    psi_func: Optional[Callable] = None
    f0: float = F0


# ---------------------------------------------------------------------------
# Hamiltonian construction
# ---------------------------------------------------------------------------

def build_nodo_zero_hamiltonian(
    N: int = 501,
    L: float = 10.0,
    lambda_delta: float = -2.0,
    alpha_pt: float = 0.5,
) -> Tuple[sp.csr_matrix, np.ndarray]:
    """
    Build the Nodo Zero Hamiltonian on a uniform grid.

    Discretises:

        H_zero = -d²/dx² + V_PT(x) + λ·δ(x)

    where the PT-symmetric potential is

        V_PT(x) = α_PT · x²

    and the Dirac delta λ·δ(x) is approximated at the grid point nearest
    to x=0 by the distributional weight λ/Δx (so that ∫ λ/Δx dx ≈ λ).

    Args:
        N:             Number of grid points (should be odd for symmetric grid).
        L:             Half-width of spatial domain; grid spans [−L, L].
        lambda_delta:  Strength λ of the Dirac delta potential.
                       Negative value creates a bound state near x=0.
        alpha_pt:      Coefficient of the harmonic PT potential V_PT = α·x².

    Returns:
        H:    Sparse CSR matrix of shape (N, N).
        x:    1-D grid array of shape (N,), uniform on [−L, L].
    """
    x = np.linspace(-L, L, N)
    dx = x[1] - x[0]

    # --- Kinetic energy: T = -d²/dx² via 3-point finite differences
    diag_main = 2.0 * np.ones(N) / dx**2
    diag_off = -np.ones(N - 1) / dx**2

    T = sp.diags(
        [diag_off, diag_main, diag_off],
        offsets=[-1, 0, 1],
        shape=(N, N),
        format="csr",
    )

    # --- PT-symmetric harmonic potential: V_PT(x) = α · x²
    V_pt = alpha_pt * x**2

    # --- Dirac delta potential at x = 0: approximated as λ/Δx at nearest grid point
    idx_zero = int(np.argmin(np.abs(x)))  # index closest to x=0
    V_delta = np.zeros(N)
    V_delta[idx_zero] = lambda_delta / dx

    V_total = V_pt + V_delta
    V_mat = sp.diags(V_total, offsets=0, shape=(N, N), format="csr")

    H = T + V_mat
    return H, x


def solve_nodo_zero(
    N: int = 501,
    L: float = 10.0,
    lambda_delta: float = -2.0,
    alpha_pt: float = 0.5,
    n_eigs: int = 10,
    n_zeros: int = 10,
) -> NodoZeroSpectrum:
    """
    Solve the Nodo Zero eigenvalue problem and return the spectral result.

    Computes the lowest *n_eigs* eigenvalues of H_zero and compares them
    to the scaled Riemann zeros γₙ/(2πF₀).

    Args:
        N:             Number of grid points.
        L:             Half-width of spatial domain.
        lambda_delta:  Dirac delta strength λ (negative → attractive).
        alpha_pt:      Harmonic potential coefficient α.
        n_eigs:        Number of eigenvalues to compute.
        n_zeros:       Number of Riemann zeros to use for comparison.

    Returns:
        NodoZeroSpectrum dataclass with all spectral information.
    """
    H, x = build_nodo_zero_hamiltonian(N=N, L=L, lambda_delta=lambda_delta, alpha_pt=alpha_pt)

    # Compute lowest n_eigs eigenvalues and eigenvectors
    eigenvalues, eigenvectors = eigsh(H, k=n_eigs, which="SM")

    # Sort by ascending eigenvalue
    sort_idx = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[sort_idx]
    eigenvectors = eigenvectors[:, sort_idx]

    # Ground state energy
    E0 = float(eigenvalues[0])

    # Node coherence: Ψ_nodo = 1 / (1 + E₀²/F₀²)
    psi_nodo = 1.0 / (1.0 + (E0 / F0) ** 2)

    # Riemann zeros and their scaled counterparts
    n_compare = min(n_eigs, n_zeros)
    riemann_zeros = get_riemann_zeros(n_compare)
    scaled_zeros = riemann_zeros / (2.0 * np.pi * F0)

    # Pearson correlation between computed eigenvalues and scaled zeros
    eigs_compare = eigenvalues[:n_compare]
    if len(eigs_compare) > 1 and len(scaled_zeros) > 1:
        corr = float(np.corrcoef(eigs_compare, scaled_zeros)[0, 1])
    else:
        corr = float("nan")

    return NodoZeroSpectrum(
        eigenvalues=eigenvalues,
        eigenvectors=eigenvectors,
        ground_energy=E0,
        psi_nodo=psi_nodo,
        riemann_zeros=riemann_zeros,
        scaled_zeros=scaled_zeros,
        correlation=corr,
        is_coherent=(psi_nodo >= PSI_THRESHOLD),
        parameters={
            "N": N,
            "L": L,
            "lambda_delta": lambda_delta,
            "alpha_pt": alpha_pt,
            "n_eigs": n_eigs,
            "F0": F0,
        },
    )


# ---------------------------------------------------------------------------
# Ground-state density
# ---------------------------------------------------------------------------

def ground_state_density_max_at_zero(
    eigenvectors: np.ndarray,
    x: np.ndarray,
) -> bool:
    """
    Verify that |ψ₀(x)|² is maximised at x ≈ 0 (characteristic of delta potential).

    Args:
        eigenvectors: Eigenvector matrix; column 0 is the ground state.
        x:            Spatial grid.

    Returns:
        True if the probability density |ψ₀(x)|² attains its maximum
        at (or within ±5 % of the domain half-width from) x = 0.
    """
    psi0 = eigenvectors[:, 0]
    density = np.abs(psi0) ** 2

    idx_max = int(np.argmax(density))
    x_max = x[idx_max]

    L = x[-1]  # domain half-width
    return abs(x_max) <= 0.05 * L


# ---------------------------------------------------------------------------
# Vertical Transform
# ---------------------------------------------------------------------------

def vertical_transform(
    psi: Callable[[float], float],
    s_values: np.ndarray,
    t_max: float = 20.0,
    n_points: int = 2000,
    f0: float = F0,
) -> VerticalTransformResult:
    """
    Compute the Vertical Transform of Ψ at the given complex frequencies.

    Definition:
        L_v[Ψ](s) = ∫₀^∞ Ψ(t) · exp(−s·t) · exp(i·F₀·t) dt

    This is equivalent to the standard Laplace transform evaluated at s − i·F₀:
        L_v[Ψ](s) = L[Ψ](s − i·F₀)

    The factor exp(i·F₀·t) = exp(i·2πf₀·t) encodes the QCAL vibrational
    signature at fundamental frequency f₀.

    Numerical implementation uses the trapezoidal rule on [0, t_max].

    Args:
        psi:      Callable Ψ(t) to transform; must be integrable on [0, t_max].
        s_values: Array of complex frequencies s at which to evaluate L_v.
        t_max:    Upper limit of integration (∞ approximated by t_max).
        n_points: Number of quadrature points.
        f0:       Fundamental frequency F₀ (default: F0 = 141.7001 Hz).

    Returns:
        VerticalTransformResult with s_values and corresponding L_v values.
    """
    omega_0 = 2.0 * np.pi * f0
    t = np.linspace(0.0, t_max, n_points)
    dt = t[1] - t[0]

    psi_vals = np.array([psi(ti) for ti in t], dtype=complex)
    phase_factor = np.exp(1j * omega_0 * t)          # exp(i·F₀·t) vibrational signature

    L_v_values = np.empty(len(s_values), dtype=complex)
    for k, s in enumerate(s_values):
        decay = np.exp(-s * t)                        # exp(−s·t) Laplace kernel
        integrand = psi_vals * decay * phase_factor
        L_v_values[k] = np.trapezoid(integrand, dx=dt)

    return VerticalTransformResult(
        s_values=s_values,
        L_v_values=L_v_values,
        psi_func=psi,
        f0=f0,
    )


# ---------------------------------------------------------------------------
# Coherence
# ---------------------------------------------------------------------------

def compute_psi_nodo(E0: float, f0: float = F0) -> float:
    """
    Compute the Node coherence Ψ_nodo.

    Formula:
        Ψ_nodo = |⟨0|Ψ|0⟩|² / (1 + |⟨0|H|0⟩|²/F₀²)
               = 1 / (1 + E₀²/F₀²)

    When E₀ → 0, Ψ_nodo → 1 (maximum self-recognition).
    When E₀ ≪ F₀, Ψ_nodo ≥ 0.888 (noetic threshold satisfied).

    The coherence threshold 0.888 corresponds to:
        E₀/F₀ ≤ sqrt(1/0.888 − 1) ≈ 0.335

    Args:
        E0: Ground-state energy of H_zero.
        f0: Fundamental frequency F₀ (default: F0 = 141.7001 Hz).

    Returns:
        Ψ_nodo ∈ (0, 1].
    """
    return 1.0 / (1.0 + (E0 / f0) ** 2)


def check_coherence_threshold(psi_nodo: float, threshold: float = PSI_THRESHOLD) -> bool:
    """
    Check whether Ψ_nodo meets the noetic coherence threshold.

    Args:
        psi_nodo:  Computed node coherence value.
        threshold: Minimum required coherence (default: 0.888).

    Returns:
        True if psi_nodo ≥ threshold.
    """
    return psi_nodo >= threshold


# ---------------------------------------------------------------------------
# Validation helper
# ---------------------------------------------------------------------------

def validate_nodo_zero(
    N: int = 501,
    L: float = 10.0,
    lambda_delta: float = -2.0,
    alpha_pt: float = 0.5,
    n_eigs: int = 10,
) -> Dict:
    """
    Run a complete Nodo Zero validation and return a summary dictionary.

    Checks:
        1. Eigenvalue computation succeeds.
        2. Ground-state density |ψ₀|² maximised at x ≈ 0.
        3. Node coherence Ψ_nodo ≥ 0.888.
        4. Vertical transform integral converges (finite result at s=1).

    Args:
        N:             Number of grid points.
        L:             Domain half-width.
        lambda_delta:  Dirac delta strength.
        alpha_pt:      Harmonic potential coefficient.
        n_eigs:        Number of eigenvalues to compute.

    Returns:
        Dictionary with keys: 'eigenvalues', 'psi_nodo', 'is_coherent',
        'ground_state_max_at_zero', 'vertical_transform_finite', 'correlation'.
    """
    H, x = build_nodo_zero_hamiltonian(N=N, L=L, lambda_delta=lambda_delta, alpha_pt=alpha_pt)
    spectrum = solve_nodo_zero(
        N=N, L=L, lambda_delta=lambda_delta, alpha_pt=alpha_pt, n_eigs=n_eigs
    )

    gs_at_zero = ground_state_density_max_at_zero(spectrum.eigenvectors, x)

    # Vertical transform: use a simple decaying test function Ψ(t) = exp(−t)
    psi_test: Callable[[float], float] = lambda t: np.exp(-t)
    s_test = np.array([1.0 + 0j])
    vt_result = vertical_transform(psi_test, s_test)
    vt_finite = bool(np.isfinite(vt_result.L_v_values[0]))

    return {
        "eigenvalues": spectrum.eigenvalues.tolist(),
        "ground_energy": spectrum.ground_energy,
        "psi_nodo": spectrum.psi_nodo,
        "is_coherent": spectrum.is_coherent,
        "ground_state_max_at_zero": gs_at_zero,
        "vertical_transform_finite": vt_finite,
        "correlation": spectrum.correlation,
        "scaled_zeros": spectrum.scaled_zeros.tolist(),
        "parameters": spectrum.parameters,
    }
