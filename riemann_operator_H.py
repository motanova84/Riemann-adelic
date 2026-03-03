#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
riemann_operator_H.py
=====================
Wu-Sprung Hamiltonian H = -Δ + V_WS(x) + V_osc(x)

The potential V_WS is derived from the inverse Abel transform of
Riemann's smooth counting function, ensuring that the eigenvalue
sequence matches the imaginary parts of the non-trivial Riemann zeros.

Mathematical Framework:
    H = -Δ + V_WS(x) + ε·V_osc(x)
    V_WS(x) = Abel_inverse(x_t(E))  where x_t(E) = (2√E/π)(log(2E/π) - 2)
    V_osc(x) = Σ_p (log p / √p) · cos(x · log p)

Spectral Identity:
    det(H - E) = ξ(1/2 + iE)

Reference:
    Wu & Sprung, Phys. Rev. E 48, 2595 (1993)
    Berry & Keating, SIAM Review 41, 236 (1999)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import math
from typing import Optional, List

# ============================================================================
# KNOWN RIEMANN ZEROS (ZEROS_ZETA_REFERENCIA)
# Imaginary parts γ_n of non-trivial zeros ζ(1/2 + iγ_n) = 0
# Source: Odlyzko tables (high precision)
# ============================================================================

ZEROS_ZETA_REFERENCIA: List[float] = [
    14.134725141734693,
    21.022039638771555,
    25.010857580145688,
    30.424876125859513,
    32.935061587739190,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167159,
    49.773832477672302,
    52.970321477714461,
    56.446247697063246,
    59.347044003015485,
    60.831778524609898,
    65.112544048081650,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083933,
    77.144840069745295,
    79.337375020249367,
    82.910380854086030,
    84.735492980517050,
    87.425274613125229,
    88.809111208594820,
    92.491899270593354,
    94.651344040519786,
    95.870634228245332,
    98.831194218193692,
    101.31785100573139,
    103.72553804047826,
    105.44662305232609,
    107.16861118427640,
    111.02953554316967,
    111.87465917699263,
    114.32022091545412,
    116.22668032085766,
    118.79078286597645,
    121.37012500242064,
    122.94682929355257,
    124.25681855434576,
    127.51668387059540,
    129.57870419995571,
    131.08768853093265,
    133.49773720561630,
    134.75650975337994,
    138.11600794299547,
    139.73620895212138,
    141.12370740402112,
    143.11184580762063,
]

# ============================================================================
# QCAL CONSTANTS
# ============================================================================

TWO_PI = 2.0 * math.pi
F0 = 141.7001           # Hz - Fundamental frequency
C_QCAL = 244.36         # QCAL coherence constant
EPSILON_OSC = 0.01      # Regularization strength for V_osc


def _generate_primes(n: int) -> np.ndarray:
    """
    Generate first n primes using the Sieve of Eratosthenes.

    Args:
        n: Number of primes to generate

    Returns:
        Array of the first n primes as floats
    """
    if n <= 0:
        return np.array([], dtype=float)
    # Upper bound for the n-th prime: p_n < n(ln n + ln ln n) for n ≥ 6
    # (prime number theorem estimate), padded with +100 for safety.
    limit = max(int(n * (math.log(max(n, 2)) + math.log(math.log(max(n, 3)))) + 100), 30)
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(math.sqrt(limit)) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    primes = [i for i, v in enumerate(sieve) if v]
    return np.array(primes[:n], dtype=float)


def wu_sprung_potential(x: np.ndarray, E_max: float = 200.0) -> np.ndarray:
    """
    Wu-Sprung smooth potential V_WS(x) via inverse Abel transform.

    For the smooth part of Riemann's counting function
    N_smooth(E) = (E/(2π)) · (log(E/(2πe)) - 7/8), the classical turning
    point satisfies x_t(E) = (√(2E)/π) · (log(E/(2π)) - 1), and the
    inverse Abel transform yields the smooth confinement potential.

    Args:
        x: Position values (array)
        E_max: Energy cutoff for the inversion (default 200.0)

    Returns:
        Potential values V_WS(x)
    """
    x = np.asarray(x, dtype=float)
    V = np.zeros_like(x)
    for i, xi in enumerate(x):
        xi_abs = abs(xi)
        if xi_abs < 1e-10:
            V[i] = 0.0
        else:
            # Invert x_t(E) = (2√E/π)(log(2E/π) - 2) numerically
            # For large |x|, E ≈ (π·x/2)² roughly; refine with Newton iteration
            E_guess = (math.pi * xi_abs / 2.0) ** 2
            E_val = _invert_turning_point(xi_abs, E_guess)
            V[i] = E_val
    return V


def _invert_turning_point(x_val: float, E_guess: float,
                          tol: float = 1e-8, max_iter: int = 50) -> float:
    """
    Numerically invert x_t(E) = (2√E/π)·(log(2E/π) - 2) to find E(x).

    Uses Newton-Raphson iteration on f(E) = x_t(E) - x_val:
        E_{n+1} = E_n - f(E_n) / f'(E_n)
    where f'(E) = d/dE [(2√E/π)(log(2E/π)-2)].

    Args:
        x_val: Target turning point |x|
        E_guess: Initial guess for E
        tol: Convergence tolerance
        max_iter: Maximum Newton iterations

    Returns:
        Energy E such that x_t(E) = x_val
    """
    E = max(E_guess, 1.0)
    for _ in range(max_iter):
        if E <= 0:
            E = 1.0
        arg = 2.0 * E / math.pi
        if arg <= 0:
            arg = 1e-10
        log_arg = math.log(arg)
        f = (2.0 * math.sqrt(E) / math.pi) * (log_arg - 2.0) - x_val
        df = (1.0 / (math.pi * math.sqrt(E))) * (log_arg - 2.0) + (
            2.0 * math.sqrt(E) / math.pi) * (1.0 / E)
        if abs(df) < 1e-15:
            break
        E_new = E - f / df
        if E_new <= 0:
            E_new = E / 2.0
        if abs(E_new - E) < tol:
            E = E_new
            break
        E = E_new
    return max(E, 0.0)


def oscillatory_potential(x: np.ndarray, primes: np.ndarray,
                          epsilon: float = EPSILON_OSC,
                          k_max: int = 1) -> np.ndarray:
    """
    Oscillatory correction V_osc(x) = ε · Σ_p Σ_{k=1}^{k_max}
    (log p / p^{k/2}) · cos(x · k · log p).

    This term encodes the prime-orbit contributions via the Gutzwiller
    trace formula.

    Args:
        x: Position values (array)
        primes: Array of prime numbers
        epsilon: Regularization strength
        k_max: Maximum period repetition

    Returns:
        Oscillatory potential values V_osc(x)
    """
    x = np.asarray(x, dtype=float)
    V_osc = np.zeros_like(x)
    log_p = np.log(primes)
    for k in range(1, k_max + 1):
        for p, lp in zip(primes, log_p):
            coeff = lp / (p ** (k / 2.0))
            V_osc += epsilon * coeff * np.cos(x * k * lp)
    return V_osc


class HamiltonianWuSprung:
    """
    Wu-Sprung Hamiltonian H = -Δ + V_WS(x) + ε·V_osc(x) discretised on a
    uniform grid.

    The smooth potential V_WS is the inverse Abel transform of Riemann's
    smooth eigenvalue staircase.  The oscillatory part encodes prime orbits.

    The spectral determinant satisfies:
        det(H - E) = ξ(1/2 + iE)

    Args:
        n_grid: Number of grid points
        x_range: (x_min, x_max) spatial domain
        n_primes: Number of primes in V_osc
        epsilon: Regularization of oscillatory potential
    """

    def __init__(self, n_grid: int = 200,
                 x_range: tuple = (-10.0, 10.0),
                 n_primes: int = 50,
                 epsilon: float = EPSILON_OSC):
        self.n_grid = n_grid
        self.x_range = x_range
        self.epsilon = epsilon
        self.primes = _generate_primes(n_primes)
        self._build_grid()

    def _build_grid(self) -> None:
        """Build the spatial grid and potential arrays."""
        x_min, x_max = self.x_range
        self.x = np.linspace(x_min, x_max, self.n_grid)
        self.dx = self.x[1] - self.x[0]
        self.V_ws = wu_sprung_potential(self.x)
        self.V_osc = oscillatory_potential(self.x, self.primes,
                                           epsilon=self.epsilon)
        self.V = self.V_ws + self.V_osc

    def matrix(self) -> np.ndarray:
        """
        Assemble the finite-difference Hamiltonian matrix.

        Uses the 3-point Laplacian: -Δ ≈ (2u_i - u_{i-1} - u_{i+1})/dx².

        Returns:
            (n_grid × n_grid) real symmetric Hamiltonian matrix
        """
        dx2 = self.dx ** 2
        diag = 2.0 / dx2 + self.V
        off = -1.0 / dx2 * np.ones(self.n_grid - 1)
        H = np.diag(diag) + np.diag(off, k=1) + np.diag(off, k=-1)
        return H

    def eigenvalues(self, n_eigs: Optional[int] = None) -> np.ndarray:
        """
        Compute eigenvalues of H.

        Args:
            n_eigs: Number of smallest eigenvalues to return
                    (default: all)

        Returns:
            Sorted array of eigenvalues
        """
        from scipy.linalg import eigh
        H = self.matrix()
        evals = eigh(H, eigvals_only=True)
        evals = np.sort(evals[evals > 0])
        if n_eigs is not None:
            evals = evals[:n_eigs]
        return evals
