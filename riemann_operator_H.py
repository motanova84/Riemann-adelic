"""
Riemann Operator H: Wu-Sprung Hamiltonian and Spectral Analysis
================================================================

Implements the Wu-Sprung Hamiltonian H = -d²/dx² + V_WS(x) whose
eigenvalues approximate the imaginary parts of non-trivial Riemann zeros.

Also provides the corrected GUE spacing analysis using the proper
N_smooth unfolding procedure:
    N_smooth(E) = E/(2π) · log(E/(2π)) − E/(2π) + 7/8

Standard unfolding procedure:
    1. Compute ξ_n = N_smooth(E_n) for each eigenvalue E_n
    2. Spacings s_n = ξ_{n+1} − ξ_n have mean ≈ 1 if eigenvalues track zeros

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import math
import numpy as np
from scipy import linalg, optimize
from typing import Optional

# ─── Reference Riemann zeros (imaginary parts γ_n, first 20) ───────────────

ZEROS_ZETA_REFERENCIA = [
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
    56.446247697063246,
    59.347044002602351,
    60.831778524609809,
    65.112544048081651,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083933,
    77.144840068874807,
]


# ─── Smooth counting function ────────────────────────────────────────────────

def N_smooth(E: float) -> float:
    """
    Smooth counting function for Riemann zeros (Riemann-von Mangoldt formula).

    N_smooth(E) = (E/2π) · log(E/2π) − E/2π + 7/8

    This approximates the number of zeros with imaginary part in (0, E].
    When used to unfold eigenvalues, the resulting spacings have mean ≈ 1
    if the eigenvalues accurately track the Riemann zeros.

    Args:
        E: Energy value (imaginary part of zero / eigenvalue).

    Returns:
        Approximate count of zeros up to height E.
    """
    if E <= 1e-12:
        return 0.0
    val = (E / (2.0 * math.pi)) * math.log(E / (2.0 * math.pi)) - E / (2.0 * math.pi) + 7.0 / 8.0
    return max(0.0, val)


def unfold_via_N_smooth(eigenvalues: np.ndarray) -> np.ndarray:
    """
    Unfold eigenvalues using N_smooth and return normalised spacings.

    Maps E_n → ξ_n = N_smooth(E_n), then computes s_n = ξ_{n+1} − ξ_n.
    The spacings have mean ≈ 1 when the eigenvalues track Riemann zeros.

    Args:
        eigenvalues: Array of positive eigenvalues (sorted ascending).

    Returns:
        Array of unfolded spacings of length len(eigenvalues) − 1.
    """
    evals = np.sort(eigenvalues)
    xi = np.array([N_smooth(float(e)) for e in evals])
    return np.diff(xi)


# ─── Wu-Sprung Hamiltonian ───────────────────────────────────────────────────

class WuSprungOperator:
    """
    Wu-Sprung Hamiltonian H = −d²/dx² + V_WS(x) on (0, x_max) with
    Dirichlet boundary conditions.

    The Wu-Sprung potential V_WS is defined via the inverse of the smooth
    counting function: V_WS(x) = N_smooth⁻¹(x) on the increasing branch
    (E ≳ 9.5), so that the classical turning point x_c(E) = N_smooth(E)
    and the smooth zero density is reproduced via the WKB quantisation
    condition.

    Attributes:
        N (int): Number of interior grid points.
        x_max (float): Right boundary of the interval.
        h (float): Grid spacing h = x_max / (N + 1).
        x_grid (np.ndarray): Interior grid points of length N.
    """

    def __init__(self, N: int = 1000, x_max: float = 13.0) -> None:
        """
        Initialise Wu-Sprung operator.

        Args:
            N: Number of interior grid points (default: 1000).
            x_max: Right boundary (default: 13.0).
        """
        self.N = N
        self.x_max = float(x_max)
        self.h = self.x_max / (N + 1)
        self.x_grid = np.linspace(self.h, self.x_max - self.h, N)

    def V_WS(self, x_array: np.ndarray) -> np.ndarray:
        """
        Evaluate the Wu-Sprung potential at each point in x_array.

        V_WS(x) = N_smooth⁻¹(x), i.e. the energy E (on the monotonically
        increasing branch E ≳ 9.5) such that N_smooth(E) = x.

        The classical turning point for energy E is at x_c(E) = N_smooth(E),
        so that the smooth level-counting function approximately reproduces
        the Riemann zero density via the WKB quantisation condition.

        Args:
            x_array: Array of position values.

        Returns:
            Array of potential values with the same shape as x_array.
        """
        # Smallest E on the strictly-increasing branch of N_smooth
        _E_INC_LOW = 9.5

        V = np.zeros(len(x_array), dtype=float)
        for i, x in enumerate(x_array):
            target = float(x)
            if target <= 0.0:
                V[i] = _E_INC_LOW
                continue
            # Bracket the root N_smooth(E) = target on the increasing branch
            E_low = _E_INC_LOW       # N_smooth(_E_INC_LOW) ≈ 0 here
            E_high = max(10.0, target * 2.0 * math.pi * 3.0)
            while N_smooth(E_high) < target:
                E_high *= 2.0
            try:
                V[i] = optimize.brentq(
                    lambda E: N_smooth(E) - target,
                    E_low,
                    E_high,
                    xtol=1e-8,
                )
            except ValueError:
                V[i] = E_high
        return V

    def build_hamiltonian(self) -> np.ndarray:
        """
        Construct the finite-difference matrix for H = −d²/dx² + V_WS.

        Returns:
            Dense (N × N) real symmetric Hamiltonian matrix.
        """
        xg = self.x_grid
        h_sq = self.h ** 2
        Va = self.V_WS(xg)
        diag = 2.0 / h_sq + Va
        off = -np.ones(self.N - 1) / h_sq
        H = np.diag(diag) + np.diag(off, 1) + np.diag(off, -1)
        return H

    def positive_eigenvalues(self, n_max: int = 30) -> np.ndarray:
        """
        Compute the lowest positive eigenvalues of the Wu-Sprung Hamiltonian.

        Args:
            n_max: Maximum number of positive eigenvalues to return.

        Returns:
            Sorted array of positive eigenvalues of length ≤ n_max.
        """
        H = self.build_hamiltonian()
        evals = np.sort(linalg.eigvalsh(H))
        pos = evals[evals > 0]
        return pos[:n_max]


# ─── KS test helper ─────────────────────────────────────────────────────────

def _gue_cdf(s: np.ndarray) -> np.ndarray:
    """
    GUE (GOE Wigner surmise) cumulative distribution function.

    P(s) = (π/2) s exp(−πs²/4)  →  CDF = 1 − exp(−πs²/4)

    Args:
        s: Array of spacing values.

    Returns:
        CDF values at each s.
    """
    return 1.0 - np.exp(-math.pi * s ** 2 / 4.0)


def ks_distance_gue(spacings: np.ndarray) -> float:
    """
    Kolmogorov-Smirnov distance between empirical spacing CDF and GUE.

    Args:
        spacings: Array of unfolded spacings.

    Returns:
        KS distance (lower is better; 0 = perfect GUE).
    """
    mean = float(np.mean(spacings))
    if mean <= 0:
        return 1.0
    s_sorted = np.sort(spacings / mean)
    n = len(s_sorted)
    ecdf = np.arange(1, n + 1) / n
    tcdf = _gue_cdf(s_sorted)
    return float(np.max(np.abs(ecdf - tcdf)))


# ─── Convenience runner ─────────────────────────────────────────────────────

if __name__ == "__main__":
    print("Wu-Sprung operator — N_smooth unfolding demo")
    print("=" * 55)

    # Reference zeros
    zeros_ref = np.array(ZEROS_ZETA_REFERENCIA)
    s_zeros = unfold_via_N_smooth(zeros_ref)
    print(f"Zeros (N_smooth): mean={np.mean(s_zeros):.4f}, std={np.std(s_zeros):.4f}")
    print(f"  KS vs GUE: {ks_distance_gue(s_zeros):.4f}")

    # Wu-Sprung eigenvalues
    print("\nBuilding Wu-Sprung operator (N=500, x_max=10.0) ...")
    ws = WuSprungOperator(N=500, x_max=10.0)
    evals = ws.positive_eigenvalues(n_max=15)
    s_ws = unfold_via_N_smooth(evals)
    print(f"Wu-Sprung: mean={np.mean(s_ws):.4f}, std={np.std(s_ws):.4f}")
    print(f"  KS vs GUE: {ks_distance_gue(s_ws):.4f}")

    # Mean absolute error vs reference zeros
    n_cmp = min(len(evals), len(zeros_ref))
    mae = np.mean(np.abs(evals[:n_cmp] - zeros_ref[:n_cmp]))
    print(f"  MAE vs reference zeros: {mae:.4f}")

    print("\n∴ 𓂀 Ω ∞³")
