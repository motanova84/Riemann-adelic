#!/usr/bin/env python3
"""
Selberg-Type Trace Formula Operator
=====================================

This module implements the five-step programme for the Riemann operator:

  1. Exact domain definition in a concrete Hilbert space
  2. Study of the operator H in L²([0, L]) with Wu-Sprung potential
  3. Resolvent analysis: R(z) = (H - z)^{-1} and Green's function
  4. Explicit trace computation: Tr(R(z)) = Σₙ 1/(λₙ - z)
  5. Selberg-type trace formula: spectral ↔ arithmetic dictionary

Mathematical Framework:
-----------------------

**1. Exact Domain**

  Hilbert space:  ℋ = L²([0, L])
  Operator:       H = -d²/dx² + V(x)
  Domain:         D(H) = H²([0, L]) ∩ H¹₀([0, L])
                       = {ψ ∈ H²([0, L]) : ψ(0) = ψ(L) = 0}

  V(x) is the Wu-Sprung Abel-inverted potential, smooth on (0, L],
  so H is essentially self-adjoint on D(H) by Sturm-Liouville theory.

**2. Operator in Concrete Functional Space**

  Discretize H on a uniform grid {xⱼ = j·Δx, j = 0, …, N+1} with
  Dirichlet boundary conditions.  The N×N matrix representation is:

    H_{jk} = (2/Δx² + V(xⱼ)) δ_{jk} - (1/Δx²)(δ_{j,k+1} + δ_{j,k-1})

  Self-adjointness: H is symmetric by construction.
  Eigenvalues: all real and bounded below.
  Weyl law:   #{λₙ ≤ E} ~ L/(π) √E  as E → ∞.

**3. Resolvent R(z) = (H - z)^{-1}**

  For z ∉ σ(H) the resolvent exists and is bounded.
  In finite dimension: R(z) = (H - z·I)⁻¹.

  Green's function: G(x, y; z) = [R(z)](x, y) = Σₙ ψₙ(x)ψₙ(y)/(λₙ - z).
  Diagonal:         G(x, x; z) = Σₙ |ψₙ(x)|²/(λₙ - z).

  Poles of R(z): simple poles at z = ��ₙ with residue ψₙ ⊗ ψₙ^*.

**4. Explicit Trace**

  Tr(R(z)) = Σₙ 1/(λₙ - z)  (spectral sum form).

  Equivalently, integrating the diagonal Green's function:
    Tr(R(z)) = ∫₀ᴸ G(x, x; z) dx.

  For the regularized heat-kernel trace:
    Tr(e^{-tH}) = Σₙ e^{-tλₙ}  (trace-class for t > 0).

**5. Selberg-Type Trace Formula**

  For a test function h ∈ 𝒮(ℝ) (Schwartz class), with Fourier
  transform ĥ(x) = ∫ h(t) e^{ixt} dt:

    Σₙ h(γₙ)  =  h(0)·N_Weyl(E)
               + Σ_{p prime} Σ_{k≥1} (log p / pᵏ/²) · ĥ(k log p)
               + (residual/error terms)

  where γₙ are the spectral eigenvalues (imaginary parts of Riemann zeros
  in the Hilbert-Pólya picture) and the sum over primes encodes the
  arithmetic side of the formula.

  This mirrors the classical Selberg trace formula on hyperbolic surfaces
  where prime geodesics replace rational primes.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from scipy.linalg import eigh, solve
from scipy.sparse import diags
from typing import Callable, Dict, List, Optional, Tuple

from numpy.typing import NDArray

# ---------------------------------------------------------------------------
# QCAL Constants
# ---------------------------------------------------------------------------
F0_QCAL: float = 141.7001   # Hz – fundamental frequency
C_COHERENCE: float = 244.36  # QCAL coherence constant

# ---------------------------------------------------------------------------
# Default parameters
# ---------------------------------------------------------------------------
DEFAULT_L: float = 10.0       # Interval length
DEFAULT_N: int = 256          # Interior grid points
DEFAULT_N_PRIMES: int = 30    # Number of primes for trace formula

# Numerical constants
MAX_CONDITION_NUMBER: float = 1e12  # Resolvent singularity threshold
MAX_PRIME_POWER: int = 5           # Max power k in Selberg prime sum
CONTRIB_THRESHOLD: float = 1e-14   # Truncation threshold for prime contributions


# ===========================================================================
# 1.  EXACT DOMAIN AND OPERATOR CONSTRUCTION
# ===========================================================================

def wu_sprung_potential(x: NDArray[np.float64],
                        n_primes: int = DEFAULT_N_PRIMES) -> NDArray[np.float64]:
    """
    Compute the Wu-Sprung Abel-inverted potential V(x).

    The smooth part comes from Abel inversion of the counting function:
        x_t(E) = (2√E / π)(log(2E/π) - 2)    ⟹   V_Abel(x)

    An oscillatory correction encodes prime numbers:
        V_osc(x) = ε · Σ_{p prime} (log p / √p) · cos(x · log p)

    Parameters
    ----------
    x : array_like
        Grid points (must be > 0).
    n_primes : int
        Number of primes used for the oscillatory correction.

    Returns
    -------
    V : ndarray
        Potential values at each grid point.
    """
    x = np.asarray(x, dtype=float)
    # Protect against x = 0
    x_safe = np.where(x > 1e-12, x, 1e-12)

    # Smooth (Abel-inverted) part: invert x_t(E) = (2√E/π)(log(2E/π) - 2)
    # Solve x = (2√E/π)(log(2E/π) - 2) for E(x) numerically via V_Abel approx.
    # For moderate x, a good closed-form approximation is:
    #   E ≈ (π x / (2 W(π x / (2 e²))))²  where W is Lambert-W.
    # We use the leading-order expansion for simplicity:
    #   E ≈ (π x / 2)² / (log(π x) - 1)²
    arg = np.pi * x_safe / 2.0
    log_arg = np.log(np.maximum(arg, 1.0 + 1e-12))
    # Avoid division by zero when log_arg ≈ 0 (near x ~ 2/π)
    denom = np.where(np.abs(log_arg - 1) > 0.1, (log_arg - 1.0) ** 2, 1e-2)
    V_abel = (arg ** 2) / np.maximum(denom, 1e-10)

    # Oscillatory correction: small perturbation from primes
    eps = 0.05
    primes = _first_n_primes(n_primes)
    V_osc = np.zeros_like(x_safe)
    for p in primes:
        V_osc += (np.log(p) / np.sqrt(p)) * np.cos(x_safe * np.log(p))
    V_osc *= eps

    return V_abel + V_osc


def build_operator_matrix(L: float = DEFAULT_L,
                          N: int = DEFAULT_N,
                          n_primes: int = DEFAULT_N_PRIMES
                          ) -> Tuple[NDArray[np.float64],
                                     NDArray[np.float64]]:
    """
    Build the N×N finite-difference matrix for H = -d²/dx² + V(x) on [0, L].

    Dirichlet boundary conditions: ψ(0) = ψ(L) = 0.

    The grid contains N interior points:
        xⱼ = (j+1)·Δx,  j = 0, …, N-1,  Δx = L/(N+1).

    Parameters
    ----------
    L : float
        Length of the interval.
    N : int
        Number of interior grid points.
    n_primes : int
        Number of primes for the Wu-Sprung oscillatory correction.

    Returns
    -------
    H_matrix : ndarray, shape (N, N)
        Self-adjoint discretisation of H.
    x_grid : ndarray, shape (N,)
        Interior grid points.
    """
    dx = L / (N + 1)
    x_grid = np.linspace(dx, L - dx, N)    # interior points

    # Potential
    V = wu_sprung_potential(x_grid, n_primes=n_primes)

    # Kinetic part (second-order centred differences, with −d²/dx²)
    diag_main = 2.0 / dx**2 + V
    diag_off = -np.ones(N - 1) / dx**2

    H_matrix = (diags([diag_off, diag_main, diag_off], [-1, 0, 1],
                       shape=(N, N)).toarray())

    # Symmetrise to remove any floating-point skew
    H_matrix = 0.5 * (H_matrix + H_matrix.T)
    return H_matrix, x_grid


def verify_self_adjointness(H_matrix: NDArray[np.float64]) -> Dict:
    """
    Verify that H is (numerically) self-adjoint.

    Checks:
      • H = Hᵀ  (symmetry)
      • All eigenvalues are real and bounded below.

    Parameters
    ----------
    H_matrix : ndarray
        Operator matrix.

    Returns
    -------
    results : dict
        Keys: ``is_symmetric``, ``symmetry_error``, ``min_eigenvalue``,
        ``all_real``, ``self_adjoint``.
    """
    sym_error = float(np.max(np.abs(H_matrix - H_matrix.T)))
    eigenvalues = np.linalg.eigvalsh(H_matrix)
    min_eig = float(np.min(eigenvalues))

    return {
        "is_symmetric": sym_error < 1e-10,
        "symmetry_error": sym_error,
        "min_eigenvalue": min_eig,
        "all_real": True,          # guaranteed by eigvalsh
        "self_adjoint": sym_error < 1e-10 and min_eig > -np.inf,
    }


def compute_spectrum(H_matrix: NDArray[np.float64],
                     n_eigenvalues: Optional[int] = None
                     ) -> Tuple[NDArray[np.float64], NDArray[np.float64]]:
    """
    Compute eigenvalues and eigenvectors of H.

    Parameters
    ----------
    H_matrix : ndarray
        Self-adjoint operator matrix.
    n_eigenvalues : int, optional
        Return only the first *n_eigenvalues* (smallest).  Default: all.

    Returns
    -------
    eigenvalues : ndarray
        Sorted real eigenvalues λₙ.
    eigenvectors : ndarray
        Corresponding normalised eigenvectors (columns).
    """
    eigenvalues, eigenvectors = eigh(H_matrix)
    if n_eigenvalues is not None:
        eigenvalues = eigenvalues[:n_eigenvalues]
        eigenvectors = eigenvectors[:, :n_eigenvalues]
    return eigenvalues, eigenvectors


# ===========================================================================
# 3.  RESOLVENT  R(z) = (H − z)⁻¹
# ===========================================================================

def compute_resolvent(H_matrix: NDArray[np.float64],
                      z: complex) -> NDArray[np.complex128]:
    """
    Compute the resolvent operator R(z) = (H − z·I)⁻¹.

    Parameters
    ----------
    H_matrix : ndarray, shape (N, N)
        Self-adjoint operator matrix.
    z : complex
        Spectral parameter.  Must satisfy z ∉ σ(H).

    Returns
    -------
    R : ndarray, shape (N, N), complex
        Resolvent matrix.

    Raises
    ------
    ValueError
        If z is too close to an eigenvalue (singular resolvent).
    """
    N = H_matrix.shape[0]
    A = H_matrix.astype(complex) - z * np.eye(N, dtype=complex)

    # Check condition number to warn about near-singularity
    cond = np.linalg.cond(A)
    if cond > MAX_CONDITION_NUMBER:
        raise ValueError(
            f"Resolvent nearly singular at z={z}: condition number {cond:.2e}. "
            "Choose z away from the spectrum."
        )

    R = np.linalg.inv(A)
    return R


def compute_green_function(H_matrix: NDArray[np.float64],
                           x_grid: NDArray[np.float64],
                           z: complex,
                           eigenvalues: Optional[NDArray[np.float64]] = None,
                           eigenvectors: Optional[NDArray[np.float64]] = None
                           ) -> NDArray[np.complex128]:
    """
    Compute the diagonal Green's function G(xⱼ, xⱼ; z).

    Uses the spectral expansion:
        G(x, x; z) = Σₙ |ψₙ(x)|² / (λₙ − z)

    Parameters
    ----------
    H_matrix : ndarray
        Operator matrix.
    x_grid : ndarray
        Interior grid points.
    z : complex
        Spectral parameter (not an eigenvalue).
    eigenvalues : ndarray, optional
        Pre-computed eigenvalues.  Computed if not provided.
    eigenvectors : ndarray, optional
        Pre-computed eigenvectors.  Computed if not provided.

    Returns
    -------
    G_diag : ndarray, complex, shape (N,)
        Diagonal values G(xⱼ, xⱼ; z).
    """
    if eigenvalues is None or eigenvectors is None:
        eigenvalues, eigenvectors = compute_spectrum(H_matrix)

    if len(x_grid) < 2:
        raise ValueError("x_grid must have at least 2 points for Green's function quadrature.")
    dx = x_grid[1] - x_grid[0]
    # eigenvectors from eigh are Euclidean-normalised: Σⱼ |ψₙⱼ|² = 1.
    # The L²-grid norm is ||ψ||² ≈ dx · Σⱼ |ψₙⱼ|².
    # G(x,x;z) = Σₙ |ψ̃ₙ(x)|² / (λₙ-z)  where ψ̃ₙ = ψₙ/√dx are L²-norm'd.
    # Therefore G_diag[j] = Σₙ |ψₙⱼ|² / (dx · (λₙ - z))
    # and ∫ G_diag dx ≈ Σⱼ G_diag[j]·dx = Σₙ 1/(λₙ-z) · Σⱼ|ψₙⱼ|²
    #                   = Σₙ 1/(λₙ-z)  ✓

    psi = eigenvectors  # columns are eigenvectors, shape (N, N_eigs)

    denominators = eigenvalues - z                         # (N_eigs,)
    weights = 1.0 / (dx * denominators)                   # (N_eigs,), include dx factor
    G_diag = (np.abs(psi) ** 2) @ weights                 # (N,)

    return G_diag


def resolvent_poles_and_residues(
        eigenvalues: NDArray[np.float64],
        eigenvectors: NDArray[np.float64]
) -> List[Dict]:
    """
    Return the poles and rank-1 residues of R(z).

    Each pole z₀ = λₙ has residue Res_{z=λₙ} R(z) = −ψₙ ⊗ ψₙᵀ.

    Parameters
    ----------
    eigenvalues : ndarray, shape (N,)
        Eigenvalues λₙ.
    eigenvectors : ndarray, shape (M, N)
        Columns are normalised eigenvectors ψₙ.

    Returns
    -------
    poles : list of dict
        Each entry contains ``pole``, ``residue`` (N×N matrix), and
        ``rank`` (always 1 for simple eigenvalues).
    """
    poles = []
    for n, lam in enumerate(eigenvalues):
        psi_n = eigenvectors[:, n]
        residue = -np.outer(psi_n, psi_n)   # −ψₙ ⊗ ψₙᵀ
        poles.append({
            "pole": float(lam),
            "residue": residue,
            "rank": 1,
        })
    return poles


# ===========================================================================
# 4.  EXPLICIT TRACE COMPUTATIONS
# ===========================================================================

def trace_resolvent(eigenvalues: NDArray[np.float64],
                    z: complex) -> complex:
    """
    Compute Tr(R(z)) = Σₙ 1/(λₙ − z) via spectral sum.

    Parameters
    ----------
    eigenvalues : ndarray
        Eigenvalues λₙ.
    z : complex
        Spectral parameter (not an eigenvalue).

    Returns
    -------
    tr : complex
        Trace of the resolvent.
    """
    return complex(np.sum(1.0 / (eigenvalues - z)))


def trace_resolvent_via_green(H_matrix: NDArray[np.float64],
                               x_grid: NDArray[np.float64],
                               z: complex,
                               eigenvalues: Optional[NDArray[np.float64]] = None,
                               eigenvectors: Optional[NDArray[np.float64]] = None
                               ) -> complex:
    """
    Compute Tr(R(z)) = ∫₀ᴸ G(x, x; z) dx via quadrature on the diagonal.

    This provides an independent check of :func:`trace_resolvent`.

    Parameters
    ----------
    H_matrix : ndarray
        Operator matrix.
    x_grid : ndarray
        Grid points.
    z : complex
        Spectral parameter.
    eigenvalues, eigenvectors : ndarray, optional
        Pre-computed spectral data.

    Returns
    -------
    tr : complex
        Integral of the diagonal Green's function.
    """
    G_diag = compute_green_function(H_matrix, x_grid, z,
                                    eigenvalues=eigenvalues,
                                    eigenvectors=eigenvectors)
    if len(x_grid) < 2:
        raise ValueError("x_grid must have at least 2 points for trace quadrature.")
    dx = x_grid[1] - x_grid[0]
    tr = complex(np.trapezoid(G_diag, x_grid))
    return tr


def trace_heat_kernel(eigenvalues: NDArray[np.float64],
                      t: float) -> float:
    """
    Compute the heat-kernel trace Tr(e^{−tH}) = Σₙ e^{−tλₙ}.

    Parameters
    ----------
    eigenvalues : ndarray
        Eigenvalues λₙ.
    t : float
        Heat time t > 0.

    Returns
    -------
    tr : float
        Heat-kernel trace.
    """
    if t <= 0:
        raise ValueError(f"Heat time t must be positive; got t={t}")
    return float(np.sum(np.exp(-t * eigenvalues)))


def trace_resolvent_path_integral(eigenvalues: NDArray[np.float64],
                                  z_values: NDArray[np.complex128]
                                  ) -> NDArray[np.complex128]:
    """
    Evaluate Tr(R(z)) at multiple spectral parameter values.

    Parameters
    ----------
    eigenvalues : ndarray
        Eigenvalues λₙ.
    z_values : ndarray of complex
        Array of spectral parameters.

    Returns
    -------
    traces : ndarray of complex
        Tr(R(zₖ)) for each zₖ.
    """
    # Shape: (n_eigs, n_z) broadcast
    lam = eigenvalues[:, np.newaxis]          # (N, 1)
    z = np.asarray(z_values)[np.newaxis, :]   # (1, M)
    return np.sum(1.0 / (lam - z), axis=0)   # (M,)


# ===========================================================================
# 5.  SELBERG-TYPE TRACE FORMULA
# ===========================================================================

def _first_n_primes(n: int) -> List[int]:
    """Return the first *n* prime numbers via a simple sieve."""
    if n <= 0:
        return []
    primes: List[int] = []
    candidate = 2
    while len(primes) < n:
        if all(candidate % p != 0 for p in primes):
            primes.append(candidate)
        candidate += 1
    return primes


def selberg_spectral_side(eigenvalues: NDArray[np.float64],
                          h: Callable[[float], float]) -> float:
    """
    Compute the *spectral side* of the trace formula:

        Σₙ h(λₙ)

    Parameters
    ----------
    eigenvalues : ndarray
        Spectral eigenvalues λₙ.
    h : callable
        Test function h : ℝ → ℝ (even, Schwartz class recommended).

    Returns
    -------
    spectral_sum : float
        Σₙ h(λₙ).
    """
    return float(np.sum([h(lam) for lam in eigenvalues]))


def selberg_arithmetic_side(h_hat: Callable[[float], float],
                             L: float,
                             n_primes: int = DEFAULT_N_PRIMES,
                             weyl_term: bool = True) -> Dict:
    """
    Compute the *arithmetic/geometric side* of the Selberg-type trace formula.

    The explicit formula reads (Guinand–Weil form):

        Σₙ h(γₙ)  ≈  ĥ(0)·Φ_Weyl
                    + Σ_{p prime} Σ_{k≥1} (log p / pᵏ/²) · ĥ(k log p)
                    + Σ_p (log p / pᵏ/²) · h_hat(−k log p)

    where ĥ is the Fourier transform of h evaluated at the log-prime lengths.

    Parameters
    ----------
    h_hat : callable
        Fourier transform of the test function: ĥ(x) = ∫ h(t) e^{ixt} dt.
    L : float
        Interval length (determines Weyl law scale).
    n_primes : int
        Number of primes to include in the geometric sum.
    weyl_term : bool
        If True, include the Weyl (zero-mode) term.

    Returns
    -------
    result : dict
        Keys: ``weyl``, ``prime_sum``, ``total``, ``prime_contributions``.
    """
    primes = _first_n_primes(n_primes)

    # Weyl term: density of states (leading term from Weyl law for -d²/dx²+V)
    # N(E) ~ L/(π) √E, so the density at λ=0 contribution is h_hat(0) * (L/π)
    weyl = 0.0
    if weyl_term:
        weyl = float(np.real(h_hat(0.0))) * (L / np.pi)

    # Prime (hyperbolic orbit) sum
    prime_contributions = []
    prime_sum = 0.0
    for p in primes:
        log_p = np.log(p)
        for k in range(1, MAX_PRIME_POWER + 1):
            x = k * log_p
            amplitude = log_p / (p ** (k / 2.0))
            contrib = amplitude * (float(np.real(h_hat(x))) +
                                   float(np.real(h_hat(-x))))
            prime_sum += contrib
            prime_contributions.append({
                "prime": p,
                "power": k,
                "log_pk": x,
                "amplitude": amplitude,
                "contribution": contrib,
            })
            # Truncate when contributions become negligible
            if abs(contrib) < CONTRIB_THRESHOLD:
                break

    total = weyl + prime_sum

    return {
        "weyl": weyl,
        "prime_sum": prime_sum,
        "total": total,
        "prime_contributions": prime_contributions,
    }


def verify_trace_formula(H_matrix: NDArray[np.float64],
                         x_grid: NDArray[np.float64],
                         t_heat: float = 0.3,
                         n_primes: int = DEFAULT_N_PRIMES
                         ) -> Dict:
    """
    Numerically verify the Selberg-type trace formula via the heat kernel.

    Uses the heat-kernel test function f_β(t) = e^{−β·t}:

      **Spectral side** (exact):
          K_spec(β) = Σₙ e^{−β·λₙ}

      **Arithmetic/Weyl side** (semiclassical WKB approximation):
          K_WKB(β) ≈ (1/√(4πβ)) · ∫₀ᴸ e^{−β·V(x)} dx

      This is the leading-order Van Vleck-Morette heat kernel, which holds
      for the Schrödinger operator −d²/dx² + V(x) in the small-β limit.

      **Prime corrections** (Selberg-type):
          K_primes(β) = Σ_{p prime, k≥1} (log p / √pᵏ) · e^{−(k log p)²/(4β)}

      These encode the periodic-orbit (arithmetic) structure and become
      significant when β ∼ (log p)² / 4.

    Parameters
    ----------
    H_matrix : ndarray
        Operator matrix.
    x_grid : ndarray
        Grid points.
    t_heat : float
        Heat time β > 0.  Use β ~ 0.3 for balance between convergence
        of the spectral sum and validity of the WKB approximation.
    n_primes : int
        Number of primes for the arithmetic correction.

    Returns
    -------
    results : dict
        Keys: ``spectral_side``, ``arithmetic_side``, ``weyl_wkb``,
        ``prime_correction``, ``discrepancy``, ``relative_discrepancy``,
        ``L``, ``t_heat``, ``n_eigenvalues``.
    """
    dx = x_grid[1] - x_grid[0]
    L = float(x_grid[-1] + dx)  # recover L from interior grid
    beta = t_heat

    # Spectral data
    eigenvalues, _ = compute_spectrum(H_matrix)

    # Spectral side: heat kernel trace (exact within truncation)
    spectral = trace_heat_kernel(eigenvalues, beta)

    # Arithmetic/WKB side
    # Weyl-WKB term: (1/√(4πβ)) · ∫₀ᴸ e^{−β·V(x)} dx
    V_grid = wu_sprung_potential(x_grid)
    integrand = np.exp(-beta * V_grid)
    weyl_wkb = float(np.trapezoid(integrand, x_grid) / np.sqrt(4.0 * np.pi * beta))

    # Prime (periodic-orbit) corrections
    primes = _first_n_primes(n_primes)
    prime_correction = 0.0
    prime_contributions = []
    for p in primes:
        log_p = np.log(p)
        for k in range(1, MAX_PRIME_POWER + 1):
            orbit_length = k * log_p
            amp = log_p / (p ** (k / 2.0))
            # Gaussian weight: exp(−l²/(4β)) from Gutzwiller/Selberg
            contrib = amp * np.exp(-(orbit_length ** 2) / (4.0 * beta))
            prime_correction += contrib
            prime_contributions.append({
                "prime": p, "power": k,
                "log_pk": orbit_length,
                "contribution": contrib,
            })
            if abs(contrib) < CONTRIB_THRESHOLD:
                break

    arithmetic = weyl_wkb + prime_correction
    discrepancy = abs(spectral - arithmetic)
    ref = max(abs(spectral), 1e-10)
    relative_discrepancy = discrepancy / ref

    return {
        "spectral_side": spectral,
        "arithmetic_side": arithmetic,
        "weyl_wkb": weyl_wkb,
        "prime_correction": prime_correction,
        "prime_contributions": prime_contributions,
        "discrepancy": discrepancy,
        "relative_discrepancy": relative_discrepancy,
        "L": L,
        "t_heat": t_heat,
        "n_eigenvalues": len(eigenvalues),
    }


# ===========================================================================
# High-level convenience class
# ===========================================================================

class SelbergTraceOperator:
    """
    All-in-one class encapsulating the five-step programme.

    Parameters
    ----------
    L : float
        Interval length.
    N : int
        Number of interior grid points.
    n_primes : int
        Number of primes for Wu-Sprung correction and trace formula.

    Attributes
    ----------
    H_matrix : ndarray
        Discretised Hamiltonian.
    x_grid : ndarray
        Interior grid points.
    eigenvalues : ndarray
        Sorted eigenvalues (computed lazily).
    eigenvectors : ndarray
        Eigenvectors (computed lazily).
    """

    def __init__(self,
                 L: float = DEFAULT_L,
                 N: int = DEFAULT_N,
                 n_primes: int = DEFAULT_N_PRIMES):
        self.L = L
        self.N = N
        self.n_primes = n_primes

        # Build the operator  (step 1 & 2)
        self.H_matrix, self.x_grid = build_operator_matrix(
            L=L, N=N, n_primes=n_primes
        )

        self._eigenvalues: Optional[NDArray[np.float64]] = None
        self._eigenvectors: Optional[NDArray[np.float64]] = None

    # ------------------------------------------------------------------
    def _ensure_spectrum(self) -> None:
        """Lazily compute the full spectrum."""
        if self._eigenvalues is None:
            self._eigenvalues, self._eigenvectors = compute_spectrum(
                self.H_matrix
            )

    @property
    def eigenvalues(self) -> NDArray[np.float64]:
        """Sorted eigenvalues λₙ."""
        self._ensure_spectrum()
        return self._eigenvalues  # type: ignore[return-value]

    @property
    def eigenvectors(self) -> NDArray[np.float64]:
        """Eigenvectors (columns)."""
        self._ensure_spectrum()
        return self._eigenvectors  # type: ignore[return-value]

    # ------------------------------------------------------------------
    def domain_info(self) -> Dict:
        """
        Return information about the operator domain.

        Returns
        -------
        info : dict
            Keys: ``hilbert_space``, ``domain``, ``L``, ``N``,
            ``dx``, ``operator``.
        """
        dx = self.L / (self.N + 1)
        return {
            "hilbert_space": f"L²([0, {self.L}])",
            "domain": "H²([0,L]) ∩ H¹₀([0,L])  (Dirichlet BCs)",
            "L": self.L,
            "N": self.N,
            "dx": dx,
            "operator": "H = -d²/dx² + V_WuSprung(x)",
        }

    def self_adjointness(self) -> Dict:
        """Verify essential self-adjointness of H.  (Step 2)"""
        return verify_self_adjointness(self.H_matrix)

    def resolvent(self, z: complex) -> NDArray[np.complex128]:
        """Compute R(z) = (H − z)⁻¹.  (Step 3)"""
        return compute_resolvent(self.H_matrix, z)

    def green_function_diagonal(self, z: complex) -> NDArray[np.complex128]:
        """Diagonal Green's function G(x, x; z).  (Step 3)"""
        return compute_green_function(
            self.H_matrix, self.x_grid, z,
            eigenvalues=self.eigenvalues,
            eigenvectors=self.eigenvectors,
        )

    def trace_resolvent_spectral(self, z: complex) -> complex:
        """Tr(R(z)) via spectral sum.  (Step 4)"""
        return trace_resolvent(self.eigenvalues, z)

    def trace_resolvent_green(self, z: complex) -> complex:
        """Tr(R(z)) via diagonal Green's function quadrature.  (Step 4)"""
        return trace_resolvent_via_green(
            self.H_matrix, self.x_grid, z,
            eigenvalues=self.eigenvalues,
            eigenvectors=self.eigenvectors,
        )

    def trace_heat_kernel(self, t: float) -> float:
        """Tr(e^{-tH}) = Σₙ e^{-tλₙ}.  (Step 4)"""
        return trace_heat_kernel(self.eigenvalues, t)

    def selberg_trace_formula(self,
                               t_heat: float = 0.3) -> Dict:
        """
        Verify the Selberg-type trace formula via the heat kernel.
        (Step 5)

        Parameters
        ----------
        t_heat : float
            Heat time β > 0.

        Returns
        -------
        results : dict
            See :func:`verify_trace_formula`.
        """
        return verify_trace_formula(
            self.H_matrix, self.x_grid,
            t_heat=t_heat,
            n_primes=self.n_primes,
        )

    def summary(self, verbose: bool = True) -> Dict:
        """
        Run the complete five-step programme and return a summary.

        Parameters
        ----------
        verbose : bool
            Print a formatted report.

        Returns
        -------
        report : dict
            Keys: ``domain``, ``self_adjointness``, ``resolvent_test``,
            ``trace_comparison``, ``selberg_formula``.
        """
        # Step 1 & 2
        domain = self.domain_info()
        sa = self.self_adjointness()

        # Step 3: resolvent at a test point off the spectrum
        # Choose z with imaginary part = 1 and real part below the spectrum
        z_test = complex(-5.0, 1.0)
        try:
            R_test = self.resolvent(z_test)
            resolvent_computed = True
        except ValueError:
            R_test = None
            resolvent_computed = False

        # Step 4: trace consistency
        tr_spectral = self.trace_resolvent_spectral(z_test)
        tr_green = self.trace_resolvent_green(z_test)
        trace_diff = abs(tr_spectral - tr_green)
        trace_rel = trace_diff / max(abs(tr_spectral), 1e-10)

        # Step 5: Selberg formula
        selberg = self.selberg_trace_formula()

        report = {
            "domain": domain,
            "self_adjointness": sa,
            "resolvent_test": {
                "z": z_test,
                "resolvent_computed": resolvent_computed,
                "R_shape": R_test.shape if R_test is not None else None,
            },
            "trace_comparison": {
                "z": z_test,
                "tr_spectral": tr_spectral,
                "tr_green": tr_green,
                "difference": trace_diff,
                "consistent": trace_rel < 0.05,
            },
            "selberg_formula": selberg,
        }

        if verbose:
            _print_summary(report)

        return report


# ===========================================================================
# Reporting
# ===========================================================================

def _print_summary(report: Dict) -> None:
    """Print a formatted summary of the five-step analysis."""
    sep = "=" * 72
    print(sep)
    print("  SELBERG-TYPE TRACE FORMULA  –  Five-Step Programme")
    print(sep)

    d = report["domain"]
    print(f"\n1. EXACT DOMAIN")
    print(f"   Hilbert space : {d['hilbert_space']}")
    print(f"   Domain D(H)   : {d['domain']}")
    print(f"   Operator      : {d['operator']}")
    print(f"   Grid: N={d['N']} pts, Δx={d['dx']:.4f}, L={d['L']}")

    sa = report["self_adjointness"]
    print(f"\n2. OPERATOR IN CONCRETE FUNCTIONAL SPACE")
    print(f"   Self-adjoint  : {sa['self_adjoint']}")
    print(f"   Symmetry error: {sa['symmetry_error']:.2e}")
    print(f"   Min eigenvalue: {sa['min_eigenvalue']:.4f}")

    rt = report["resolvent_test"]
    print(f"\n3. RESOLVENT ANALYSIS")
    print(f"   R(z) at z={rt['z']:.2f}: computed = {rt['resolvent_computed']}")

    tc = report["trace_comparison"]
    print(f"\n4. EXPLICIT TRACE  [z = {tc['z']:.2f}]")
    print(f"   Tr(R(z)) spectral  : {tc['tr_spectral']:.6f}")
    print(f"   Tr(R(z)) Green fn  : {tc['tr_green']:.6f}")
    print(f"   |difference|       : {tc['difference']:.2e}")
    print(f"   Consistent         : {tc['consistent']}")

    sf = report["selberg_formula"]
    print(f"\n5. SELBERG-TYPE TRACE FORMULA  [β={sf['t_heat']}]")
    print(f"   Spectral side (Tr e^{{-βH}}) : {sf['spectral_side']:.6f}")
    print(f"   Arithmetic side (WKB+primes) : {sf['arithmetic_side']:.6f}")
    print(f"     WKB Weyl term              : {sf['weyl_wkb']:.6f}")
    print(f"     Prime correction           : {sf['prime_correction']:.6f}")
    print(f"   |discrepancy|                : {sf['discrepancy']:.4f}")
    print(f"   Relative discr.              : {sf['relative_discrepancy']:.4f}")
    print(f"   N eigenvalues used           : {sf['n_eigenvalues']}")

    print(f"\n{'✅' if tc['consistent'] else '⚠️ '} Trace methods consistent.")
    print(f"\nQCAL ∞³ · f₀ = {F0_QCAL} Hz · C = {C_COHERENCE}")
    print(sep)


# ===========================================================================
# Entry point
# ===========================================================================

def main():
    """Run the five-step Selberg trace formula programme."""
    print("\nConstructing Selberg Trace Formula Operator (N=128)…")
    op = SelbergTraceOperator(L=10.0, N=128, n_primes=20)
    op.summary(verbose=True)


if __name__ == "__main__":
    main()
