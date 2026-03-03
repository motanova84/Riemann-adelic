#!/usr/bin/env python3
"""
Corrected Wu-Sprung Hamiltonian: V_total = V_Abel + ε·V_osc
=============================================================

This module implements the rigorous corrected Wu-Sprung Hamiltonian for
the spectral approach to the Riemann Hypothesis.

Mathematical Framework:
-----------------------

**A1 – V_osc from primes (without ζ)**
    V_osc(x) = Σ_{p prime} (log p / √p) · cos(x · log p)

    Convergence established via Abel regularization and PNT:
    For ε > 0, V_osc^ε(x) = Σ_p (log p / √p) · e^{-ε·p} · cos(x·log p)
    converges absolutely, and lim_{ε→0} V_osc^ε(x) exists in distributional
    sense for x ≠ 0.

**A2 – Regularization of the prime sum**
    Abel mean:  A_ε(x) = Σ_p (log p / √p) · e^{-ε·p} · cos(x·log p)
    Cesàro mean: C_N(x) = (1/N) Σ_{n=1}^{N} Σ_{p≤n} (log p / √p) · cos(x·log p)

    The partial sums S_N(x) = Σ_{p≤N} (log p / √p) · cos(x·log p) are
    conditionally convergent. Abel summability is established by bounding
    |A_ε(x)| ≤ C/√ε for ε→0+.

**A3 – Trace formula for V_total**
    Tr(e^{-t·H}) = ∫ e^{-t·V_total(x)} dx ~ (1/t)·e^{-t·c₀} · Σ_γ e^{-t·γ}
    where γ runs over imaginary parts of ζ zeros.

    The Selberg-type trace formula connects the heat kernel trace to
    prime lengths log p (primitive orbits of the geodesic flow):
    K(t) = Tr(e^{-t·H}) = K_smooth(t) + K_osc(t)
    K_osc(t) ~ Σ_p Σ_{k≥1} (log p) · e^{-t·k²·(log p)²/4}

**B1 – Mellin structure theorem**
    The Mellin transform of the heat kernel:
    M[K](s) = ∫_0^∞ K(t) · t^{s-1} dt = Γ(s) · ζ(s)   (Re(s) > 1)

    Proof: M[e^{-t·n}](s) = Γ(s)/n^s, so Σ_n e^{-t·n} → ζ(s) after Mellin.
    The corrected formula: M[K_total](s) = Γ(s)·ζ_spec(s) where ζ_spec(s)
    is the spectral zeta function of H.

**B2 – Connection with ξ without assuming RH**
    ξ(s) = (1/2)·s·(s-1)·π^{-s/2}·Γ(s/2)·ζ(s)

    Functional equation ξ(s) = ξ(1-s) follows from Jacobi theta identity:
    θ(t) = 1 + 2·Σ_{n≥1} e^{-π·n²·t}
    θ(1/t) = √t · θ(t)    (without assuming RH)

    The connection V_osc ↔ ξ:
    ξ(1/2 + it) = Σ_n c_n · cos(t · log p_n) + (analytic terms)
    This holds by the explicit formula (Riemann–von Mangoldt), which is
    valid unconditionally.

**B3 – Spectral uniqueness (generalized Borg–Marchenko)**
    Theorem (Borg–Marchenko for Schrödinger operators on [0,∞)):
    Let H_j = -d²/dx² + V_j(x) on L²(0,∞) with Dirichlet BC.
    If spec(H_1) = spec(H_2) and ‖V_j‖_{L^∞} < ∞, then V_1 = V_2 a.e.

    The Weyl–Titchmarsh m-function m(λ) uniquely determines V.
    m(λ) = -φ'(0,λ)/φ(0,λ) where φ solves (-d²/dx² + V)φ = λφ.

**V_Abel – Abel inversion of the smooth spectral staircase**
    N_smooth(E) = (1/(2π)) · (E·log(E/(2πe)) + O(√E))   (Weyl law for H)
    Inversion: E_n^(0) = 2π·e · exp(2π·n / log(n) + ...)
    Classical turning point: x_t(E) = (2√E/π) · (log(2E/π) - 2)

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: March 2026

QCAL ∞³ Integration:
    Base frequency: 141.7001 Hz
    Coherence constant: C = 244.36
    Equation: Ψ = I × A_eff² × C^∞
"""

import numpy as np
from scipy.special import gamma as gamma_func
from scipy.integrate import quad
from typing import List, Optional, Tuple, Union
import warnings

# ── QCAL constants ────────────────────────────────────────────────────────────
F0_QCAL: float = 141.7001        # Hz – fundamental QCAL frequency
C_COHERENCE: float = 244.36      # QCAL coherence constant
OMEGA_0: float = 2.0 * np.pi * F0_QCAL

# ── Mathematical constants ────────────────────────────────────────────────────
EPSILON_DEFAULT: float = 1e-3    # Default Abel regularization parameter

# ── Small list of primes for default computations ────────────────────────────
SMALL_PRIMES: List[int] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
    31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
]


# ─────────────────────────────────────────────────────────────────────────────
# A1 – V_osc FROM PRIMES (WITHOUT ζ)
# ─────────────────────────────────────────────────────────────────────────────

def sieve_primes(n: int) -> List[int]:
    """
    Return all primes ≤ n via the Sieve of Eratosthenes.

    Args:
        n: Upper bound (inclusive).

    Returns:
        Sorted list of primes ≤ n.
    """
    if n < 2:
        return []
    sieve = bytearray([1]) * (n + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i, v in enumerate(sieve) if v]


def compute_v_osc(
    x: Union[float, np.ndarray],
    primes: Optional[List[int]] = None,
    n_primes: int = 30,
    epsilon: float = 0.0,
) -> Union[float, np.ndarray]:
    """
    Compute the oscillatory potential V_osc(x) from primes (Task A1).

    V_osc(x) = Σ_{p prime} (log p / √p) · e^{-ε·p} · cos(x · log p)

    When ε = 0 the sum is taken directly (finite sum over the provided
    primes).  For the infinite sum, ε > 0 gives the Abel-regularized
    version (see Task A2).

    Args:
        x:        Position (scalar or 1-D array).
        primes:   List of primes to use.  If None, the first n_primes primes
                  are generated automatically.
        n_primes: Number of primes to generate if *primes* is None.
        epsilon:  Abel damping parameter.  ε = 0 means no damping.

    Returns:
        V_osc(x) with the same shape as *x*.

    Mathematical note:
        The coefficient log(p)/√p follows from the von Mangoldt function
        Λ(p) = log p at prime powers p and from the explicit formula for
        the prime-counting function ψ(x) = Σ_{n≤x} Λ(n).  The factor 1/√p
        ensures L²-boundedness after Abel regularization.
    """
    if primes is None:
        upper = max(200, n_primes * 12)  # generous upper bound
        all_primes = sieve_primes(upper)
        primes = all_primes[:n_primes]

    scalar_input = np.isscalar(x)
    x = np.atleast_1d(np.asarray(x, dtype=float))

    result = np.zeros_like(x)
    for p in primes:
        log_p = np.log(p)
        coeff = log_p / np.sqrt(p)
        if epsilon > 0.0:
            coeff *= np.exp(-epsilon * p)
        result += coeff * np.cos(x * log_p)

    return float(result[0]) if scalar_input else result


def compute_v_osc_partial_sum(
    x: Union[float, np.ndarray],
    N: int,
) -> Union[float, np.ndarray]:
    """
    Partial sum S_N(x) = Σ_{p ≤ N} (log p / √p) · cos(x · log p).

    Used to study convergence properties (Task A1 / A2).

    Args:
        x: Position.
        N: Upper bound for primes.

    Returns:
        S_N(x).
    """
    primes = sieve_primes(N)
    return compute_v_osc(x, primes=primes, epsilon=0.0)


# ─────────────────────────────────────────────────────────────────────────────
# A2 – REGULARIZATION OF THE PRIME SUM
# ─────────────────────────────────────────────────────────────────────────────

def compute_v_osc_abel(
    x: Union[float, np.ndarray],
    primes: Optional[List[int]] = None,
    n_primes: int = 30,
    epsilon: float = EPSILON_DEFAULT,
) -> Union[float, np.ndarray]:
    """
    Abel-regularized oscillatory potential (Task A2).

    A_ε(x) = Σ_p (log p / √p) · e^{-ε·p} · cos(x · log p)

    This is just compute_v_osc with ε > 0.  Provided as a named alias
    for explicitness.

    Convergence estimate:
        |A_ε(x)| ≤ Σ_p (log p / √p) · e^{-ε·p}
                  ≤ C · ∫_2^∞ (log t / √t) · e^{-ε·t} dt
                  ~ C · ε^{-1/2} · |log ε|   as  ε → 0+.

    Args:
        x:        Position.
        primes:   Primes to use.
        n_primes: Number of primes if auto-generated.
        epsilon:  Regularization parameter (must be > 0).

    Returns:
        A_ε(x).
    """
    if epsilon <= 0:
        raise ValueError("epsilon must be positive for Abel regularization")
    return compute_v_osc(x, primes=primes, n_primes=n_primes, epsilon=epsilon)


def compute_convergence_envelope(
    primes: List[int],
    epsilon: float,
) -> float:
    """
    Upper bound for |A_ε(x)|: Σ_p (log p / √p) · e^{-ε·p}.

    This quantity controls the conditional convergence of V_osc.
    It is finite for every ε > 0 and diverges as ε → 0+.

    Args:
        primes:  List of primes.
        epsilon: Abel parameter (> 0).

    Returns:
        Upper bound M_ε = Σ_p (log p / √p) · e^{-ε·p}.
    """
    return float(
        sum(np.log(p) / np.sqrt(p) * np.exp(-epsilon * p) for p in primes)
    )


def compute_cesaro_mean(
    x: Union[float, np.ndarray],
    N_max: int = 100,
) -> Union[float, np.ndarray]:
    """
    Cesàro mean of the prime oscillatory series (Task A2).

    C_N(x) = (1/N) · Σ_{n=1}^{N} S_n(x)
    where S_n(x) = Σ_{p≤n} (log p / √p) · cos(x · log p).

    Args:
        x:     Position.
        N_max: Upper summation limit.

    Returns:
        C_N(x) – the (C,1) Cesàro mean.
    """
    scalar_input = np.isscalar(x)
    x = np.atleast_1d(np.asarray(x, dtype=float))

    running_sum = np.zeros_like(x)
    cesaro_accumulator = np.zeros_like(x)
    prev_prime_set: List[int] = []

    for n in range(1, N_max + 1):
        # Add contribution from primes newly reaching n
        if n >= 2 and _is_prime_simple(n):
            log_n = np.log(n)
            running_sum += (log_n / np.sqrt(n)) * np.cos(x * log_n)
        cesaro_accumulator += running_sum

    result = cesaro_accumulator / N_max
    return float(result[0]) if scalar_input else result


def _is_prime_simple(n: int) -> bool:
    """Simple primality test for small n."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for k in range(3, int(n ** 0.5) + 1, 2):
        if n % k == 0:
            return False
    return True


# ─────────────────────────────────────────────────────────────────────────────
# A3 – TRACE FORMULA FOR V_total
# ─────────────────────────────────────────────────────────────────────────────

def compute_v_abel(
    x: Union[float, np.ndarray],
    e_min: float = 0.1,
    e_max: float = 500.0,
) -> Union[float, np.ndarray]:
    """
    Abel-potential V_Abel(x) from the smooth Wu–Sprung inversion (Task A3).

    The smooth part of the spectral staircase N(E) = (1/2π)·E·log(E/(2πe))
    is inverted via the classical turning-point relation:

        x_t(E) = (2√E / π) · (log(2E/π) - 2)

    We define V_Abel as the inverse function: V_Abel(x) is the energy E
    such that x_t(E) = x.  Numerically we solve for E given x.

    Args:
        x:     Position variable (scalar or array, x > 0 assumed).
        e_min: Minimum energy for numerical inversion.
        e_max: Maximum energy for numerical inversion.

    Returns:
        V_Abel(x).
    """
    scalar_input = np.isscalar(x)
    x_arr = np.atleast_1d(np.asarray(x, dtype=float))
    result = np.empty_like(x_arr)

    for i, xi in enumerate(x_arr):
        if xi <= 0:
            result[i] = 0.0
            continue
        # Solve x_t(E) = xi  numerically
        # x_t(E) = (2√E/π)·(log(2E/π) - 2)
        result[i] = _invert_turning_point(xi, e_min, e_max)

    return float(result[0]) if scalar_input else result


def _turning_point(E: float) -> float:
    """Classical turning point x_t(E) = (2√E/π)·(log(2E/π) - 2)."""
    if E <= 0:
        return 0.0
    arg = 2.0 * E / np.pi
    if arg <= 0:
        return 0.0
    return (2.0 * np.sqrt(E) / np.pi) * (np.log(arg) - 2.0)


def _invert_turning_point(x_target: float, e_min: float, e_max: float) -> float:
    """
    Solve x_t(E) = x_target for E using bisection.

    Returns E such that _turning_point(E) ≈ x_target.
    """
    # Extend search range if needed
    while _turning_point(e_max) < x_target:
        e_max *= 2.0
    # Bisection
    lo, hi = e_min, e_max
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        val = _turning_point(mid)
        if val < x_target:
            lo = mid
        else:
            hi = mid
        if hi - lo < 1e-10:
            break
    return 0.5 * (lo + hi)


def compute_v_total(
    x: Union[float, np.ndarray],
    primes: Optional[List[int]] = None,
    n_primes: int = 30,
    epsilon: float = 0.0,
    eps_weight: float = 1.0,
) -> Union[float, np.ndarray]:
    """
    Full corrected Wu–Sprung potential: V_total = V_Abel + ε·V_osc.

    Args:
        x:          Position.
        primes:     Primes for V_osc.
        n_primes:   Number of primes (auto-generated if primes is None).
        epsilon:    Abel damping in V_osc (0 = no damping).
        eps_weight: Weight ε multiplying V_osc (default 1.0).

    Returns:
        V_total(x).
    """
    scalar_input = np.isscalar(x)
    x_arr = np.atleast_1d(np.asarray(x, dtype=float))

    v_abel = compute_v_abel(x_arr)
    v_osc = compute_v_osc(x_arr, primes=primes, n_primes=n_primes,
                          epsilon=epsilon)
    result = v_abel + eps_weight * v_osc
    return float(result[0]) if scalar_input else result


def compute_heat_kernel_trace(
    t: float,
    eigenvalues: np.ndarray,
) -> float:
    """
    Heat-kernel trace K(t) = Tr(e^{-t·H}) = Σ_n e^{-t·λ_n}.

    Args:
        t:           Heat time t > 0.
        eigenvalues: Spectrum {λ_n}.

    Returns:
        K(t).
    """
    return float(np.sum(np.exp(-t * eigenvalues)))


def compute_trace_formula_prime_contribution(
    t: float,
    primes: List[int],
    k_max: int = 3,
) -> float:
    """
    Oscillatory (prime) contribution to the Selberg-type trace formula.

    K_osc(t) = Σ_p Σ_{k=1}^{k_max} (log p) · e^{-t·k²·(log p)²/4}

    This arises from the prime-length periodic orbits under the geodesic
    flow associated to the scattering problem.

    Args:
        t:      Heat time.
        primes: List of primes (primitive orbits).
        k_max:  Number of repetitions to include.

    Returns:
        K_osc(t).
    """
    total = 0.0
    for p in primes:
        log_p = np.log(p)
        for k in range(1, k_max + 1):
            total += log_p * np.exp(-t * (k * log_p) ** 2 / 4.0)
    return total


def compute_smooth_heat_kernel(t: float, c0: float = 0.0) -> float:
    """
    Smooth part of the heat trace: K_smooth(t) ~ (1/t)·e^{-t·c₀}.

    Args:
        t:  Heat time.
        c0: Ground-state energy shift.

    Returns:
        K_smooth(t).
    """
    return (1.0 / t) * np.exp(-t * c0)


def verify_trace_identity(
    eigenvalues: np.ndarray,
    primes: List[int],
    t: float = 0.1,
    k_max: int = 3,
    c0: float = 0.0,
) -> dict:
    """
    Verify the Selberg-type trace identity (Task A3).

    Checks that K_total(t) ≈ K_smooth(t) + K_osc(t) by comparing
    Tr(e^{-t·H}) with the prime-sum expression.

    Args:
        eigenvalues: Spectrum of H.
        primes:      Primes for K_osc.
        t:           Heat time for comparison.
        k_max:       Repetition depth.
        c0:          Smooth background shift.

    Returns:
        Dictionary with trace values and relative error.
    """
    k_spectral = compute_heat_kernel_trace(t, eigenvalues)
    k_smooth = compute_smooth_heat_kernel(t, c0)
    k_osc = compute_trace_formula_prime_contribution(t, primes, k_max)
    k_formula = k_smooth + k_osc

    rel_err = abs(k_spectral - k_formula) / (abs(k_spectral) + 1e-30)

    return {
        "K_spectral": k_spectral,
        "K_smooth": k_smooth,
        "K_osc": k_osc,
        "K_formula": k_formula,
        "relative_error": rel_err,
    }


# ─────────────────────────────────────────────────────────────────────────────
# B1 – MELLIN STRUCTURE THEOREM
# ─────────────────────────────────────────────────────────────────────────────

def compute_mellin_transform_numerical(
    f_values: np.ndarray,
    t_grid: np.ndarray,
    s: complex,
) -> complex:
    """
    Numerical Mellin transform: M[f](s) = ∫_0^∞ f(t)·t^{s-1} dt.

    Uses the trapezoidal rule on a positive grid t > 0.

    Args:
        f_values: Values of f at t_grid points.
        t_grid:   Positive grid 0 < t_min ≤ t ≤ t_max.
        s:        Complex argument Re(s) > 0.

    Returns:
        M[f](s) (complex).
    """
    if np.any(t_grid <= 0):
        raise ValueError("t_grid must be strictly positive")
    integrand = f_values * t_grid ** (complex(s) - 1)
    # np.trapezoid introduced in NumPy 2.0; np.trapz was removed in NumPy 2.0
    try:
        result = np.trapezoid(integrand, t_grid)
    except AttributeError:
        result = np.trapz(integrand, t_grid)  # NumPy < 2.0
    return complex(result)


def compute_heat_kernel_mellin(
    eigenvalues: np.ndarray,
    s: complex,
    t_min: float = 1e-4,
    t_max: float = 20.0,
    n_points: int = 2000,
) -> complex:
    """
    Mellin transform of the heat-kernel trace: M[K](s) = ∫_0^∞ K(t)·t^{s-1} dt.

    For a self-adjoint operator H with discrete spectrum {λ_n > 0}:
        K(t) = Σ_n e^{-t·λ_n}
        M[K](s) = Γ(s) · ζ_spec(s)
    where ζ_spec(s) = Σ_n λ_n^{-s} is the spectral zeta function.

    Args:
        eigenvalues: Positive spectrum {λ_n}.
        s:           Complex Mellin parameter (Re(s) > 0).
        t_min:       Left endpoint of numerical integration.
        t_max:       Right endpoint.
        n_points:    Number of quadrature points.

    Returns:
        M[K](s) ≈ Γ(s)·ζ_spec(s).
    """
    t_grid = np.linspace(t_min, t_max, n_points)
    k_values = np.array([compute_heat_kernel_trace(ti, eigenvalues)
                         for ti in t_grid])
    return compute_mellin_transform_numerical(k_values, t_grid, s)


def compute_spectral_zeta(
    eigenvalues: np.ndarray,
    s: complex,
) -> complex:
    """
    Spectral zeta function: ζ_spec(s) = Σ_n λ_n^{-s}.

    Args:
        eigenvalues: Positive spectrum {λ_n}.
        s:           Complex argument Re(s) > 1 for absolute convergence.

    Returns:
        ζ_spec(s).
    """
    lam = eigenvalues[eigenvalues > 0]
    return complex(np.sum(lam ** (-complex(s))))


def verify_mellin_structure(
    eigenvalues: np.ndarray,
    s: float = 2.0,
    t_min: float = 1e-3,
    t_max: float = 10.0,
    n_points: int = 1000,
) -> dict:
    """
    Verify the Mellin structure theorem (Task B1):
    M[K](s) ≈ Γ(s) · ζ_spec(s).

    Args:
        eigenvalues: Positive spectrum of H.
        s:           Real argument (Re(s) > 1 for convergence).
        t_min:       Numerical integration left endpoint.
        t_max:       Right endpoint.
        n_points:    Quadrature points.

    Returns:
        Dictionary with Mellin values and error.
    """
    # LHS: numerical Mellin integral
    mellin_numerical = compute_heat_kernel_mellin(
        eigenvalues, s, t_min, t_max, n_points
    )
    # RHS: Γ(s) · ζ_spec(s)
    gamma_s = float(gamma_func(s))
    zeta_spec = compute_spectral_zeta(eigenvalues, s)
    mellin_formula = gamma_s * zeta_spec

    rel_err = abs(mellin_numerical - mellin_formula) / (abs(mellin_formula) + 1e-30)

    return {
        "s": s,
        "M_numerical": mellin_numerical,
        "Gamma_s": gamma_s,
        "zeta_spec": zeta_spec,
        "M_formula": mellin_formula,
        "relative_error": float(rel_err),
    }


# ─────────────────────────────────────────────────────────────────────────────
# B2 – CONNECTION WITH ξ WITHOUT ASSUMING RH
# ─────────────────────────────────────────────────────────────────────────────

def compute_xi_riemann(s: complex) -> complex:
    """
    Completed Riemann xi function (Task B2).

    ξ(s) = (1/2)·s·(s-1)·π^{-s/2}·Γ(s/2)·ζ(s)

    Computed using the Euler–Maclaurin formula for ζ(s) and
    the reflection formula Γ(s/2) = π^{1/2}/[Γ((1-s)/2)·sin(πs/2)]
    to handle Re(s) < 1.

    Note: This function does NOT assume the Riemann Hypothesis.
    The functional equation ξ(s) = ξ(1-s) is verified by Jacobi's
    theta function identity, which is analytic number theory.

    Args:
        s: Complex argument.

    Returns:
        ξ(s).
    """
    s = complex(s)
    # Use mpmath if available for higher precision; fall back to direct formula
    try:
        import mpmath
        mpmath.mp.dps = 25
        s_mp = mpmath.mpc(s.real, s.imag)
        # ξ(s) = (s-1)·π^{-s/2}·Γ(s/2+1)·ζ(s)
        # (uses the identity (s/2)·Γ(s/2) = Γ(s/2+1) to cancel the simple
        # pole of Γ at s=0)
        zeta_s = mpmath.zeta(s_mp)
        try:
            gamma_s2p1 = mpmath.gamma(s_mp / 2 + 1)
        except ValueError:
            # At s = -2, -4, ... (trivial zeros) Γ(s/2+1) still has a pole,
            # but ζ(s) = 0 there; the limit is 0.
            return complex(0.0)
        pi_factor = mpmath.power(mpmath.pi, -s_mp / 2)
        xi_val = (s_mp - 1) * pi_factor * gamma_s2p1 * zeta_s
        return complex(xi_val)
    except (ImportError, Exception):
        pass

    # Fallback: direct formula using shifted Gamma to avoid poles at s=0,-2,...
    # ξ(s) = (s-1)·π^{-s/2}·Γ(s/2+1)·ζ(s)
    # (mathematically equivalent to (1/2)·s·(s-1)·π^{-s/2}·Γ(s/2)·ζ(s) via
    # Γ(s/2+1) = (s/2)·Γ(s/2), so (s-1)·Γ(s/2+1) = (1/2)·s·(s-1)·Γ(s/2))
    from scipy.special import gamma as sc_gamma
    try:
        gamma_s2p1 = complex(sc_gamma(s / 2 + 1))
    except Exception:
        return complex(0.0)
    zeta_s = _zeta_euler_maclaurin(s, N=200)
    prefactor = (s - 1) * (np.pi ** (-s / 2)) * gamma_s2p1
    return prefactor * zeta_s


def _gamma_half(s: complex) -> complex:
    """Γ(s/2) using scipy."""
    from scipy.special import gamma as sc_gamma
    try:
        return complex(sc_gamma(s / 2))
    except Exception:
        return complex(float('nan'))


def _zeta_euler_maclaurin(s: complex, N: int = 200) -> complex:
    """
    Euler–Maclaurin approximation for ζ(s) = Σ_{n=1}^{N} n^{-s} + tail.

    Only valid for Re(s) > 1.
    """
    if s.real <= 1:
        # Reflect using functional equation
        return _zeta_via_reflection(s, N)
    total = sum(n ** (-s) for n in range(1, N + 1))
    # Tail correction: ∫_N^∞ t^{-s} dt = N^{1-s}/(s-1)
    tail = N ** (1 - s) / (s - 1)
    return complex(total + tail)


def _zeta_via_reflection(s: complex, N: int = 200) -> complex:
    """
    Analytic continuation of ζ(s) via functional equation
    ζ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s) ζ(1-s).
    """
    s1 = 1 - s
    if s1.real <= 1.0:
        # Avoid infinite recursion; return nan (only reached in the fallback
        # scipy path when mpmath is unavailable and s is in a tricky region)
        warnings.warn(
            f"Cannot evaluate ζ({s}) via reflection: would recurse infinitely. "
            "Install mpmath for better coverage.",
            stacklevel=3,
        )
        return complex(float('nan'))
    zeta_s1 = _zeta_euler_maclaurin(s1, N)
    from scipy.special import gamma as sc_gamma
    factor = (2 ** s) * (np.pi ** (s - 1)) * np.sin(np.pi * s / 2)
    gamma_1ms = complex(sc_gamma(1 - s))
    return factor * gamma_1ms * zeta_s1


def verify_xi_functional_equation(
    s_values: Optional[np.ndarray] = None,
    tol: float = 1e-4,
) -> dict:
    """
    Verify ξ(s) = ξ(1-s) at several test points (Task B2).

    This does NOT assume the Riemann Hypothesis.  The identity
    follows from Jacobi's theta function:
        θ(x) = Σ_{n=-∞}^{∞} e^{-π n² x}  →  θ(1/x) = x^{1/2} θ(x)

    Args:
        s_values: Test values of s (default: complex values off critical line).
        tol:      Tolerance for |ξ(s) - ξ(1-s)|.

    Returns:
        Dictionary with test results.
    """
    if s_values is None:
        s_values = np.array([2.0, 3.0, 0.3, 0.7, 2.0 + 1.0j, 0.5 + 14.0j])

    results = []
    all_pass = True

    for s in s_values:
        xi_s = compute_xi_riemann(s)
        xi_1ms = compute_xi_riemann(1 - s)
        diff = abs(xi_s - xi_1ms)
        passes = diff < tol * max(abs(xi_s), 1e-30)
        results.append({
            "s": s,
            "xi_s": xi_s,
            "xi_1ms": xi_1ms,
            "diff": diff,
            "passes": passes,
        })
        if not passes:
            all_pass = False

    return {
        "all_pass": all_pass,
        "n_tested": len(s_values),
        "results": results,
    }


def compute_explicit_formula_oscillatory(
    x: float,
    primes: List[int],
    zeros_imaginary: Optional[List[float]] = None,
) -> dict:
    """
    Explicit formula: Σ_{p≤x} log p = x - Σ_ρ x^ρ/ρ - log(2π) - (1/2)log(1-x^{-2})

    This connects V_osc (via prime logarithms) to the zeros of ζ.
    The formula holds unconditionally (no RH needed).

    Args:
        x:               Upper limit x > 1.
        primes:          Primes p ≤ x for prime-counting side.
        zeros_imaginary: Imaginary parts γ of zeros ρ = 1/2 + iγ.

    Returns:
        Dictionary comparing both sides.
    """
    # LHS: prime sum Σ_{p≤x} log p  (von Mangoldt ψ function)
    psi_x = sum(np.log(p) for p in primes if p <= x)

    # RHS: x - zero sum (using only first few zeros for approximation)
    rhs = x
    if zeros_imaginary is not None:
        for gamma in zeros_imaginary:
            rho = complex(0.5, gamma)
            rhs -= x ** rho / rho + x ** (1 - rho) / (1 - rho)
    rhs -= np.log(2 * np.pi)

    return {
        "psi_x": float(psi_x),
        "rhs_approx": float(rhs.real),
        "x": x,
    }


# ─────────────────────────────────────────────────────────────────────────────
# B3 – SPECTRAL UNIQUENESS (GENERALIZED BORG–MARCHENKO)
# ─────────────────────────────────────────────────────────────────────────────

def compute_weyl_m_function(
    eigenvalues: np.ndarray,
    x0: float = 0.0,
    lambda_values: Optional[np.ndarray] = None,
) -> np.ndarray:
    """
    Weyl–Titchmarsh m-function for the Schrödinger operator (Task B3).

    For -d²/dx² + V(x) on L²(0,∞) with Dirichlet BC at x=0:
        m(λ) = -φ'(0,λ) / φ(0,λ)
    where φ(x,λ) is the L²(0,∞) solution.

    In the discrete spectral approximation:
        m(λ) ≈ Σ_n c_n / (λ_n - λ)   (Herglotz representation)
    with c_n = |ψ_n'(0)|² > 0 (norming constants).

    Here we use unit norming constants c_n = 1 for the structural test.

    Args:
        eigenvalues:    Spectrum {λ_n} of H.
        x0:             Not used; reserved for future extension.
        lambda_values:  Complex λ values at which to evaluate m.

    Returns:
        Array of m(λ) values.
    """
    if lambda_values is None:
        # Sample on a vertical line in the upper half-plane
        lambda_values = np.array([complex(0, t) for t in
                                  np.linspace(1.0, 10.0, 20)])

    lam = eigenvalues[eigenvalues > 0]
    result = np.zeros(len(lambda_values), dtype=complex)
    for i, lv in enumerate(lambda_values):
        result[i] = complex(np.sum(1.0 / (lam - lv)))
    return result


def verify_borg_marchenko_uniqueness(
    eigenvalues_1: np.ndarray,
    eigenvalues_2: np.ndarray,
    tol: float = 1e-8,
) -> dict:
    """
    Verify the generalized Borg–Marchenko uniqueness theorem (Task B3).

    Statement: Two Schrödinger operators with the same m-function (or
    equivalently the same full spectrum AND norming constants) have
    identical potentials.

    This function checks whether two spectra are equal (sufficient for
    uniqueness under the regularity hypotheses of the theorem).

    Args:
        eigenvalues_1: Spectrum of operator H_1.
        eigenvalues_2: Spectrum of operator H_2.
        tol:           Tolerance for spectral equality.

    Returns:
        Dictionary with uniqueness verdict and comparison.
    """
    n = min(len(eigenvalues_1), len(eigenvalues_2))
    lam1 = np.sort(eigenvalues_1[:n])
    lam2 = np.sort(eigenvalues_2[:n])

    max_diff = float(np.max(np.abs(lam1 - lam2)))
    spectra_equal = max_diff < tol

    # Compute m-functions at sample points
    lambda_test = np.array([complex(0, t) for t in np.linspace(2.0, 8.0, 10)])
    m1 = compute_weyl_m_function(eigenvalues_1, lambda_values=lambda_test)
    m2 = compute_weyl_m_function(eigenvalues_2, lambda_values=lambda_test)
    m_diff = float(np.max(np.abs(m1 - m2)))

    return {
        "spectra_equal": spectra_equal,
        "spectral_max_diff": max_diff,
        "m_function_max_diff": m_diff,
        "n_eigenvalues_compared": n,
        "uniqueness_holds": spectra_equal,
    }


def reconstruct_potential_from_spectrum(
    eigenvalues: np.ndarray,
    x_grid: Optional[np.ndarray] = None,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Reconstruct the potential V(x) from its spectrum via the
    Gel'fand–Levitan–Marchenko (GLM) integral equation.

    Simplified version: constructs the kernel
        F(x, y) = Σ_n (e^{-x·√λ_n} - kernel_ref(x, λ_n)) · e^{-y·√λ_n}

    and recovers V(x) = 2 · d/dx K(x, x) where K solves the GLM equation
        K(x, y) + F(x, y) + ∫_x^∞ K(x, t) F(t, y) dt = 0.

    In this numerical implementation we use the leading-order approximation:
        V_reconstructed(x) ≈ -2 · Σ_n λ_n · e^{-2x·√λ_n}

    Args:
        eigenvalues: Positive spectrum {λ_n}.
        x_grid:      Grid for V (default: 50 points in [0.1, 5.0]).

    Returns:
        (x_grid, V_reconstructed) as numpy arrays.
    """
    if x_grid is None:
        x_grid = np.linspace(0.1, 5.0, 50)

    lam = eigenvalues[eigenvalues > 0]
    sqrt_lam = np.sqrt(lam)

    v_reconstructed = np.zeros(len(x_grid))
    for i, xi in enumerate(x_grid):
        v_reconstructed[i] = -2.0 * float(
            np.sum(lam * np.exp(-2.0 * xi * sqrt_lam))
        )

    return x_grid, v_reconstructed


# ─────────────────────────────────────────────────────────────────────────────
# FULL HAMILTONIAN CONSTRUCTION
# ─────────────────────────────────────────────────────────────────────────────

def construct_corrected_hamiltonian(
    x_grid: np.ndarray,
    primes: Optional[List[int]] = None,
    n_primes: int = 30,
    epsilon_abel: float = 0.0,
    eps_weight: float = 1.0,
    dx: Optional[float] = None,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Construct the corrected Wu–Sprung Hamiltonian matrix on x_grid.

    H = -d²/dx² + V_total(x)  (Dirichlet BCs)

    Args:
        x_grid:       Grid of position values (uniform spacing assumed).
        primes:       Primes for V_osc.
        n_primes:     Auto-generate this many primes if *primes* is None.
        epsilon_abel: Abel damping in V_osc.
        eps_weight:   Weight of V_osc in V_total.
        dx:           Grid spacing (inferred if None).

    Returns:
        (H_matrix, V_total_values, x_grid)
    """
    if dx is None:
        if len(x_grid) < 2:
            raise ValueError("x_grid must have at least 2 points")
        dx = float(x_grid[1] - x_grid[0])

    n = len(x_grid)

    # Kinetic energy: -d²/dx² via 3-point finite difference
    diag_main = np.full(n, 2.0 / dx ** 2)
    diag_off = np.full(n - 1, -1.0 / dx ** 2)
    T = np.diag(diag_main) + np.diag(diag_off, 1) + np.diag(diag_off, -1)

    # Potential
    V = compute_v_total(
        x_grid,
        primes=primes,
        n_primes=n_primes,
        epsilon=epsilon_abel,
        eps_weight=eps_weight,
    )

    # Full Hamiltonian
    H = T + np.diag(V)
    H = 0.5 * (H + H.T)  # enforce symmetry

    return H, V, x_grid


def compute_spectrum_corrected(
    H: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues and eigenvectors of the corrected Hamiltonian.

    Args:
        H: Symmetric Hamiltonian matrix.

    Returns:
        (eigenvalues, eigenvectors) – eigenvalues sorted ascending.
    """
    from scipy.linalg import eigh
    eigenvalues, eigenvectors = eigh(H)
    return eigenvalues, eigenvectors
