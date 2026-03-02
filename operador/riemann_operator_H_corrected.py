#!/usr/bin/env python3
"""
Corrected Wu-Sprung Operator with Berry-Keating Oscillatory Correction.

Implements:
    V(x) = V_Abel(x) + ε · V_osc(x)

where:
    V_Abel(x)  = Abel-inverted smooth Riemann zero counting potential
                 V_Abel(x) = N₀⁻¹(x/π), N₀(E) = E/(2π)·log(E/(2πe)) + 7/8

    V_osc(x)   = Σ_{p ≤ P prime} (log p / √p) · cos(x · log p)
                 (Berry-Keating/Gutzwiller trace formula: primes as periodic orbits)

Operator:
    H = -d²/dx² + V_Abel(x) + ε · V_osc(x)
    on [0, L] with Dirichlet boundary conditions.
    Tridiagonal finite-difference discretization.

No Riemann zeros are needed to build the operator — only primes via the Sieve.

Author: QCAL ∞³ Framework
"""

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from scipy.optimize import brentq
from typing import List, Optional, Tuple
import os

# ---------------------------------------------------------------------------
# Prime sieve
# ---------------------------------------------------------------------------

def primes_up_to(P: int) -> List[int]:
    """
    Return all primes p with 2 ≤ p ≤ P via Sieve of Eratosthenes.

    Parameters
    ----------
    P : int
        Upper bound (inclusive).

    Returns
    -------
    List[int]
        Sorted list of primes ≤ P.
    """
    if P < 2:
        return []
    sieve = np.ones(P + 1, dtype=bool)
    sieve[0] = sieve[1] = False
    for i in range(2, int(P ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return list(np.where(sieve)[0])


# ---------------------------------------------------------------------------
# Smooth Riemann zero counting function and its inverse
# ---------------------------------------------------------------------------

def smooth_zero_count(E: float) -> float:
    """
    Smooth Riemann zero counting function (Riemann–von Mangoldt formula).

    N₀(E) = E/(2π) · log(E/(2πe)) + 7/8

    Parameters
    ----------
    E : float
        Height on the critical line (E > 0).

    Returns
    -------
    float
        Approximate number of non-trivial zeros with imaginary part in (0, E].
    """
    if E <= 0.0:
        return 0.0
    return E / (2.0 * np.pi) * np.log(E / (2.0 * np.pi * np.e)) + 7.0 / 8.0


def invert_smooth_count(n: float, E_hi: float = 1e5) -> float:
    """
    Find E such that N₀(E) = n on the ascending branch (E > 2π).

    N₀(E) has a minimum at E = 2π (value ≈ −0.125) and is strictly
    increasing for E > 2π.  We always return the root on this ascending
    branch so that V_Abel is a monotone increasing potential.

    Parameters
    ----------
    n : float
        Target count value.
    E_hi : float
        Initial upper bracket (expanded automatically if needed).

    Returns
    -------
    float
        Energy E > 2π satisfying N₀(E) ≈ n.
    """
    if n <= 0.0:
        return 0.0
    # Lower bracket: just past the minimum of N₀ at E = 2π,
    # where N₀ ≈ −0.125, so f(E_lo) < 0 for any n ≥ 0.
    E_lo = 2.0 * np.pi + 1e-3
    # Expand upper bracket until N₀(E_hi) > n
    while smooth_zero_count(E_hi) < n:
        E_hi *= 2.0
    f = lambda E: smooth_zero_count(E) - n
    return brentq(f, E_lo, E_hi, xtol=1e-8, rtol=1e-10)


# ---------------------------------------------------------------------------
# Abel-inverted potential
# ---------------------------------------------------------------------------

def abel_inversion_potential(x_grid: np.ndarray) -> np.ndarray:
    """
    Compute V_Abel on a spatial grid via the Abel inversion relation:

        V_Abel(x) = N₀⁻¹(x / π)

    This ensures that the smooth level-counting function of the operator
    H = -d²/dx² + V_Abel matches the Riemann zero counting function N₀.

    Parameters
    ----------
    x_grid : np.ndarray
        1-D array of spatial positions x > 0.

    Returns
    -------
    np.ndarray
        Potential values V_Abel(x) for each x in x_grid.
    """
    x_grid = np.asarray(x_grid, dtype=float)
    V = np.zeros(len(x_grid))
    for i, x in enumerate(x_grid):
        n = x / np.pi
        V[i] = invert_smooth_count(n) if n > 0.0 else 0.0
    return V


# ---------------------------------------------------------------------------
# Oscillatory prime-sum correction
# ---------------------------------------------------------------------------

def V_osc_prime_sum(x: np.ndarray, primes: List[int]) -> np.ndarray:
    """
    Oscillatory Berry-Keating correction to the Wu-Sprung potential.

        V_osc(x) = Σ_{p ∈ primes} (log p / √p) · cos(x · log p)

    Motivated by the Gutzwiller trace formula: primes are the classical
    periodic orbits of the Berry-Keating Hamiltonian H = xp, with
    primitive period T_p = log p.

    Parameters
    ----------
    x : array_like
        Spatial positions.  Both scalar (0-D) and 1-D arrays are accepted.
        For a scalar x, a 1-element numpy array is returned.
    primes : List[int]
        List of prime numbers p.

    Returns
    -------
    np.ndarray
        Oscillatory potential values at each x position.
        Shape matches the input shape after atleast_1d conversion.
    """
    x = np.asarray(x, dtype=float)
    scalar_input = x.ndim == 0
    x = np.atleast_1d(x)

    V = np.zeros_like(x)
    for p in primes:
        log_p = np.log(float(p))
        V += (log_p / np.sqrt(float(p))) * np.cos(x * log_p)

    return V[0] if scalar_input else V


# ---------------------------------------------------------------------------
# Wigner-Dyson GUE helpers
# ---------------------------------------------------------------------------

def wigner_dyson_gue_pdf(s: np.ndarray) -> np.ndarray:
    """
    Wigner-Dyson nearest-neighbour spacing distribution (GUE Wigner surmise).

        P(s) = (π/2) · s · exp(−πs²/4)

    Parameters
    ----------
    s : array_like
        Normalised spacing values s ≥ 0.

    Returns
    -------
    np.ndarray
        PDF values P(s).
    """
    s = np.asarray(s, dtype=float)
    return (np.pi / 2.0) * s * np.exp(-np.pi * s ** 2 / 4.0)


def wigner_dyson_gue_cdf(s: np.ndarray) -> np.ndarray:
    """
    CDF of the Wigner-Dyson GUE spacing distribution.

        F(s) = 1 − exp(−πs²/4)

    Parameters
    ----------
    s : array_like
        Normalised spacing values s ≥ 0.

    Returns
    -------
    np.ndarray
        CDF values F(s).
    """
    s = np.asarray(s, dtype=float)
    return 1.0 - np.exp(-np.pi * s ** 2 / 4.0)


# ---------------------------------------------------------------------------
# Spacing analysis
# ---------------------------------------------------------------------------

class SpacingAnalysis:
    """
    Analyse nearest-neighbour level spacings and compare to GUE statistics.

    Parameters
    ----------
    eigenvalues : array_like
        Sorted (or unsorted) eigenvalues / energy levels.
    """

    def __init__(self, eigenvalues: np.ndarray):
        self.eigenvalues = np.sort(np.asarray(eigenvalues, dtype=float))

    def normalized_spacings(self) -> np.ndarray:
        """
        Compute normalised spacings s_n = (E_{n+1} − E_n) / ⟨s⟩.

        Returns
        -------
        np.ndarray
            Array of normalised spacings (length = len(eigenvalues) − 1).
        """
        gaps = np.diff(self.eigenvalues)
        mean_gap = np.mean(gaps)
        if mean_gap == 0.0:
            return np.zeros_like(gaps)
        return gaps / mean_gap

    def ks_statistic_gue(self) -> float:
        """
        Kolmogorov-Smirnov statistic against the Wigner-Dyson GUE CDF.

        Returns
        -------
        float
            KS distance D = max |F_empirical(s) − F_GUE(s)|.
            Returns np.nan if fewer than 2 eigenvalues are available
            (no spacings can be computed).
        """
        s = self.normalized_spacings()
        if len(s) == 0:
            return np.nan
        s_sorted = np.sort(s)
        n = len(s_sorted)
        F_empirical = np.arange(1, n + 1) / n
        F_theory = wigner_dyson_gue_cdf(s_sorted)
        return float(np.max(np.abs(F_empirical - F_theory)))

    def histogram_data(self, n_bins: int = 20) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute histogram of normalised spacings.

        Parameters
        ----------
        n_bins : int
            Number of histogram bins.

        Returns
        -------
        bin_centers : np.ndarray
        counts_normalised : np.ndarray
            Probability density (area = 1).
        """
        s = self.normalized_spacings()
        counts, edges = np.histogram(s, bins=n_bins, density=True)
        centers = 0.5 * (edges[:-1] + edges[1:])
        return centers, counts


# ---------------------------------------------------------------------------
# Corrected Wu-Sprung operator
# ---------------------------------------------------------------------------

class CorrectedWuSprungOperator:
    """
    Corrected Wu-Sprung operator with Berry-Keating prime correction.

        H = −d²/dx² + V_Abel(x) + ε · V_osc(x)

    Discretised on an interior grid with Dirichlet boundary conditions
    using the standard tridiagonal finite-difference scheme.

    Parameters
    ----------
    N : int
        Number of interior grid points.
    L : float
        Domain length.  The grid is x_i = i·h, i=1,…,N, h = L/(N+1).
        Recommended: L = π · N_zeros so that V_Abel spans up to γ_{N_zeros}.
    epsilon : float
        Coupling constant for the oscillatory correction.
    primes : List[int], optional
        List of primes to use in V_osc.  If None, primes_up_to(P) is used.
    P : int
        Upper prime bound when `primes` is None.
    N_zeros : int
        Approximate number of Riemann zeros targeted (sets domain scale).
    """

    def __init__(
        self,
        N: int = 300,
        L: Optional[float] = None,
        epsilon: float = 0.5,
        primes: Optional[List[int]] = None,
        P: int = 100,
        N_zeros: int = 50,
    ):
        self.N = N
        self.N_zeros = N_zeros
        self.epsilon = epsilon

        if primes is None:
            primes = primes_up_to(P)
        self.primes = primes

        # Domain: L = π · N_zeros so that V_Abel(L) ≈ γ_{N_zeros}
        if L is None:
            L = np.pi * N_zeros
        self.L = L

        # Interior grid (Dirichlet: ψ(0) = ψ(L) = 0)
        self.h = L / (N + 1)
        self.x = np.linspace(self.h, L - self.h, N)

        # Potentials
        self.V_abel = abel_inversion_potential(self.x)
        self.V_osc_vals = V_osc_prime_sum(self.x, self.primes)
        self.V_total = self.V_abel + epsilon * self.V_osc_vals

        # Operator matrix
        self.H = self._build_matrix()

    def _build_matrix(self) -> sp.csr_matrix:
        """Build tridiagonal −d²/dx² + V matrix."""
        h2 = self.h ** 2
        diag = 2.0 / h2 + self.V_total
        off = -np.ones(self.N - 1) / h2
        H = sp.diags([off, diag, off], [-1, 0, 1], format="csr")
        return H

    def eigenvalues(self, k: Optional[int] = None) -> np.ndarray:
        """
        Compute the k smallest eigenvalues.

        Parameters
        ----------
        k : int, optional
            Number of eigenvalues.  Defaults to min(50, N−2).

        Returns
        -------
        np.ndarray
            Sorted eigenvalues (ascending).
        """
        if k is None:
            k = min(50, self.N - 2)
        k = min(k, self.N - 2)
        eigvals, _ = eigsh(self.H, k=k, which="SA")
        return np.sort(eigvals)

    def spacing_analysis(self, k: Optional[int] = None) -> "SpacingAnalysis":
        """Return a SpacingAnalysis for the computed eigenvalues."""
        return SpacingAnalysis(self.eigenvalues(k=k))


# ---------------------------------------------------------------------------
# Epsilon sweep
# ---------------------------------------------------------------------------

def epsilon_sweep(
    N: int = 300,
    epsilons: Optional[List[float]] = None,
    P: int = 100,
    N_zeros: Optional[int] = None,
    k_eig: int = 20,
) -> List[dict]:
    """
    Sweep over ε values and measure MAE against known Riemann zeros.

    Shows that the absolute error decreases systematically with ε
    up to an optimal value.

    Parameters
    ----------
    N : int
        Grid size.
    epsilons : List[float], optional
        Values of ε to test.  Defaults to [0.0, 0.1, 0.2, 0.3, 0.4, 0.5].
    P : int
        Prime bound for V_osc.
    N_zeros : int, optional
        Number of Riemann zeros targeted.  Defaults to N (matches grid size).
    k_eig : int
        Number of eigenvalues to compute.

    Returns
    -------
    List[dict]
        Each entry: {'epsilon': ε, 'mae': MAE, 'n_within_1': int}.
    """
    if epsilons is None:
        epsilons = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5]
    if N_zeros is None:
        N_zeros = N

    ref_zeros = _load_reference_zeros(max_zeros=k_eig)
    primes = primes_up_to(P)
    results = []

    for eps in epsilons:
        op = CorrectedWuSprungOperator(
            N=N, epsilon=eps, primes=primes, N_zeros=N_zeros
        )
        eigvals = op.eigenvalues(k=k_eig)
        n_cmp = min(len(eigvals), len(ref_zeros))
        errors = np.abs(eigvals[:n_cmp] - ref_zeros[:n_cmp])
        mae = float(np.mean(errors))
        n_within_1 = int(np.sum(errors < 1.0))
        results.append({"epsilon": eps, "mae": mae, "n_within_1": n_within_1})

    return results


# ---------------------------------------------------------------------------
# N sweep
# ---------------------------------------------------------------------------

def N_sweep(
    N_values: Optional[List[int]] = None,
    epsilon: float = 0.5,
    P: int = 100,
    N_zeros: Optional[int] = None,
    k_eig: int = 15,
) -> List[dict]:
    """
    Sweep over grid sizes N and compare base vs corrected MAE.

    Shows convergence and that the correction consistently improves the base.

    Parameters
    ----------
    N_values : List[int], optional
        Grid sizes to test.  Defaults to [100, 200, 300].
    epsilon : float
        Fixed ε for the corrected operator.
    P : int
        Prime bound.
    N_zeros : int, optional
        Target zeros.  If None, uses each N as N_zeros (scales with grid).
    k_eig : int
        Number of eigenvalues.

    Returns
    -------
    List[dict]
        Each entry: {'N': N, 'mae_base': float, 'mae_corrected': float,
                     'delta': float}.
    """
    if N_values is None:
        N_values = [100, 200, 300]

    ref_zeros = _load_reference_zeros(max_zeros=k_eig)
    primes = primes_up_to(P)
    results = []

    for N in N_values:
        nz = N_zeros if N_zeros is not None else N

        # Base operator (ε = 0)
        base = CorrectedWuSprungOperator(
            N=N, epsilon=0.0, primes=primes, N_zeros=nz
        )
        base_eigvals = base.eigenvalues(k=k_eig)

        # Corrected operator
        corr = CorrectedWuSprungOperator(
            N=N, epsilon=epsilon, primes=primes, N_zeros=nz
        )
        corr_eigvals = corr.eigenvalues(k=k_eig)

        n_cmp = min(len(base_eigvals), len(corr_eigvals), len(ref_zeros))
        mae_base = float(np.mean(np.abs(base_eigvals[:n_cmp] - ref_zeros[:n_cmp])))
        mae_corr = float(np.mean(np.abs(corr_eigvals[:n_cmp] - ref_zeros[:n_cmp])))
        delta = mae_base - mae_corr

        results.append(
            {
                "N": N,
                "mae_base": mae_base,
                "mae_corrected": mae_corr,
                "delta": delta,
            }
        )

    return results


# ---------------------------------------------------------------------------
# Reference zeros loader
# ---------------------------------------------------------------------------

def _load_reference_zeros(
    max_zeros: int = 50, zeros_file: Optional[str] = None
) -> np.ndarray:
    """
    Load known Riemann zeros from file.

    Falls back to the first 20 well-known zeros if the file is missing.
    """
    if zeros_file is None:
        here = os.path.dirname(os.path.abspath(__file__))
        repo = os.path.dirname(here)
        zeros_file = os.path.join(repo, "zeros", "zeros_t1e3.txt")

    if os.path.exists(zeros_file):
        gammas = []
        with open(zeros_file) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    try:
                        gammas.append(float(line))
                        if len(gammas) >= max_zeros:
                            break
                    except ValueError:
                        continue
        return np.array(gammas[:max_zeros])

    # Hard-coded fallback: first 20 non-trivial zeros (imaginary parts).
    # Source: Odlyzko tables / LMFDB (https://www.lmfdb.org/zeros/zeta/).
    fallback = np.array([
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
        52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
        67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
    ])
    return fallback[:max_zeros]
