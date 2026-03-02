"""
Wu-Sprung Operator: H = -d^2/dx^2 + V_WS(x)

Implements the Wu-Sprung Hamiltonian whose eigenvalues approximate the
imaginary parts of the non-trivial zeros of the Riemann zeta function.

The potential V_WS is constructed by inverting the smooth counting function
N_smooth(E) = (E/2pi) * log(E/2pi) - E/2pi + 7/8
via an Abel inversion (WKB approximation), without using zeta(s) or its
functional equation.

Five Pillars connection:
    Pilar I:  |E_n^{(N,L)} - gamma_n| converges to 0 as N, L -> inf
    Pilar V:  V_WS constructed purely from N_smooth (no functional equation)

Author: Jose Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuantica (ICQ)
Date: March 2026
"""

import math
import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import brentq
from typing import Optional, List, Tuple

_TWO_PI = 2.0 * math.pi


def N_smooth(E: float) -> float:
    """
    Smooth counting function N_smooth(E) from Stirling approximation.

    Counts the expected number of Riemann zeros with imaginary part in (0, E].
    Constructed without using zeta(s) or its functional equation.

    Formula: N_smooth(E) = (E/2pi) * log(E/2pi) - E/2pi + 7/8

    Args:
        E: Energy / imaginary part of zero (E > 0)

    Returns:
        Smooth count of zeros up to E
    """
    if E <= 0:
        return 0.0
    x = E / _TWO_PI
    return x * math.log(x) - x + 7.0 / 8.0


def _x_of_V(V: float) -> float:
    """
    Abel inversion: classical turning point x as a function of potential V.

    From the WKB approximation and the smooth counting function:
        x(V) = (2*sqrt(V)/pi) * (log(V/(2*pi)) + C)
        where C = 1 - 2*log(2)  (integration constant)

    Args:
        V: Potential value (V > 0)

    Returns:
        Classical turning point x(V)
    """
    if V <= 0:
        return 0.0
    sqrt_V = math.sqrt(V)
    # C = 1 - 2*log(2) (integration constant from Abel inversion)
    C = 1.0 - 2.0 * math.log(2.0)
    return (2.0 * sqrt_V / math.pi) * (math.log(V / _TWO_PI) + C)


def V_WS(x: float, V_min: float = 1.0, V_max: float = 1e6) -> float:
    """
    Wu-Sprung potential V_WS(x) at position x.

    Computed as the inverse of x(V) via bisection (brentq).
    The potential is constructed purely from N_smooth (Abel inversion),
    without using zeta(s) or its functional equation.

    Args:
        x: Position (x > 0)
        V_min: Minimum value for root search bracket
        V_max: Maximum value for root search bracket

    Returns:
        V_WS(x): potential value at x
    """
    if x <= 0:
        return V_min
    # Find V such that x_of_V(V) = x
    try:
        return brentq(lambda V: _x_of_V(V) - x, V_min, V_max, xtol=1e-10)
    except ValueError:
        # Extend bracket if needed
        while _x_of_V(V_max) < x:
            V_max *= 10.0
        return brentq(lambda V: _x_of_V(V) - x, V_min, V_max, xtol=1e-10)


class WuSprungOperator:
    """
    Discretized Wu-Sprung Hamiltonian H = -d^2/dx^2 + V_WS(x) on [0, L].

    Uses Dirichlet boundary conditions: psi(0) = psi(L) = 0.
    Discretized with N interior grid points using second-order finite
    differences.

    The eigenvalues E_n^{(N,L)} approximate the Riemann zeros gamma_n
    with error O((L/N)^2 * exp(kappa * lambda_n)).

    Attributes:
        N: Number of interior grid points
        x_max: Right boundary L
        dx: Grid spacing L / (N + 1)
        x: Grid points array (interior only)
        V: Potential values at grid points
    """

    def __init__(self, N: int = 500, x_max: float = 13.0):
        """
        Initialize the Wu-Sprung operator on [0, x_max] with N interior points.

        Args:
            N: Number of interior discretization points (default: 500)
            x_max: Right boundary L (default: 13.0)
        """
        self.N = N
        self.x_max = x_max
        self.dx = x_max / (N + 1)

        # Interior grid points (Dirichlet BCs: psi(0) = psi(x_max) = 0)
        self.x = np.linspace(self.dx, x_max - self.dx, N)

        # Compute potential on grid
        self.V = np.array([V_WS(xi) for xi in self.x])

    def _build_diagonal(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Build diagonal and off-diagonal for the tridiagonal Hamiltonian matrix.

        H = -d^2/dx^2 + V(x) discretized with second-order finite differences:
            H_{i,i}   = 2/dx^2 + V_i
            H_{i,i+1} = H_{i+1,i} = -1/dx^2

        Returns:
            Tuple (d, e) where d is the main diagonal and e is the off-diagonal
        """
        inv_dx2 = 1.0 / self.dx ** 2
        d = 2.0 * inv_dx2 * np.ones(self.N) + self.V
        e = -inv_dx2 * np.ones(self.N - 1)
        return d, e

    def eigenvalues(self, n_max: Optional[int] = None) -> np.ndarray:
        """
        Compute eigenvalues of H_{N,L}.

        Uses scipy.linalg.eigh_tridiagonal for efficient symmetric
        tridiagonal eigenvalue computation.

        Args:
            n_max: Number of lowest eigenvalues to return (default: all)

        Returns:
            Array of eigenvalues in ascending order
        """
        d, e = self._build_diagonal()
        evals = eigh_tridiagonal(d, e, eigvals_only=True)
        if n_max is not None:
            return evals[:n_max]
        return evals

    def positive_eigenvalues(self, n_max: int = 15) -> np.ndarray:
        """
        Return the n_max smallest positive eigenvalues.

        These approximate the imaginary parts of the first n_max Riemann zeros
        gamma_n when compared against ZEROS_ZETA.

        Args:
            n_max: Number of positive eigenvalues to return (default: 15)

        Returns:
            Array of the n_max smallest positive eigenvalues
        """
        d, e = self._build_diagonal()
        evals = eigh_tridiagonal(d, e, eigvals_only=True)
        # Keep only positive eigenvalues and return directly (not sqrt)
        pos = evals[evals > 0]
        return pos[:n_max] if len(pos) >= n_max else pos


def load_riemann_zeros(n: int = 20) -> np.ndarray:
    """
    Load the first n imaginary parts of Riemann zeros.

    Tries to load from the data file, falling back to known values.
    Only returns values from a monotonically increasing sequence where
    consecutive gaps are consistent with the Riemann zero spacing.

    Args:
        n: Number of zeros to load

    Returns:
        Array of the first n Riemann zeros (imaginary parts)
    """
    # Well-known first 20 Riemann zeros (imaginary parts of non-trivial zeros)
    known_zeros = [
        14.134725141735, 21.022039638772, 25.010857580146, 30.424876125860,
        32.935061587739, 37.586178158826, 40.918719012148, 43.327073280914,
        48.005150881167, 49.773832477672, 52.970321477715, 56.446247696636,
        59.347044002817, 60.831778524609, 65.112544048082, 67.079810529494,
        69.546401711174, 72.067157674481, 75.704690699083, 77.144840068874,
    ]
    if n <= len(known_zeros):
        return np.array(known_zeros[:n])

    # Try loading from file for more zeros
    import os
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    zeros_file = os.path.join(repo_root, 'zeros', 'zeros_t1e3.txt')

    zeros = list(known_zeros)
    try:
        prev = known_zeros[-1]
        max_gap = 20.0  # Maximum expected gap between consecutive zeros
        with open(zeros_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    try:
                        val = float(line)
                        gap = val - prev
                        if 0 < gap < max_gap:
                            zeros.append(val)
                            prev = val
                        elif val in known_zeros:
                            continue  # Skip already known
                    except ValueError:
                        pass
                    if len(zeros) >= n:
                        break
    except (FileNotFoundError, IOError):
        pass

    return np.array(zeros[:n])


# Standard first 20 Riemann zeros (imaginary parts)
ZEROS_ZETA = load_riemann_zeros(20)


def convergence_rate(N_values: np.ndarray, L_fixed: float = 13.0,
                     n_max: int = 15) -> float:
    """
    Estimate the O(1/N^2) convergence constant for eigenvalue approximation.

    For each N in N_values, builds a WuSprungOperator and computes the mean
    absolute error between the n_max lowest positive eigenvalues and the
    corresponding Riemann zeros:

        error(N) = mean(|E_n^{(N,L)} - gamma_n|)

    Then fits error(N) ~ C / N^2 and returns the constant C.

    Args:
        N_values: Array of N values (grid sizes) to evaluate
        L_fixed: Fixed box size L for all runs (default: 13.0)
        n_max: Number of eigenvalues to compare (default: 15)

    Returns:
        C: Convergence constant (coefficient of 1/N^2 fit)
    """
    errors: List[float] = []
    zeros_ref = ZEROS_ZETA[:n_max]

    for N in N_values:
        ws = WuSprungOperator(N=int(N), x_max=L_fixed)
        evals = ws.positive_eigenvalues(n_max=n_max)
        k = min(len(evals), len(zeros_ref))
        if k == 0:
            errors.append(float('nan'))
            continue
        error = float(np.mean(np.abs(evals[:k] - zeros_ref[:k])))
        errors.append(error)

    errors_arr = np.array(errors, dtype=float)
    N_arr = np.array(N_values, dtype=float)

    # Fit error ~ C / N^2 (i.e., error = C * (1/N^2) + intercept)
    valid = np.isfinite(errors_arr)
    if np.sum(valid) < 2:
        return float('nan')

    coeffs = np.polyfit(1.0 / N_arr[valid] ** 2, errors_arr[valid], 1)
    return float(coeffs[0])
