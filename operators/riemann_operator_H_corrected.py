#!/usr/bin/env python3
"""
Corrected Wu-Sprung Hamiltonian: H = -d²/dx² + V_Abel(x) + ε·V_osc(x)

This module implements the corrected Wu-Sprung Hamiltonian derived from first
principles through the following mathematical chain:

1. **WKB condition** (classical physics):
   ∫₀^{x_t(E)} √(E - V(x)) dx = (n - 1/4)π

2. **Density of states** (quantum mechanics):
   ρ(E) = dN/dE  where N(E) is the spectral counting function

3. **Smooth + oscillatory decomposition** (analysis):
   N(E) = N_smooth(E) + N_osc(E)
   N_smooth(E) ≈ E/(2π) · log(E/(2πe))  (Weyl law)

4. **Trace formula identification** (chaotic systems):
   N_osc(E) = -1/π · Σ_p Σ_k (log p)/p^{k/2} · sin(k·E·log p)

5. **Inverse Abel transform** (integral geometry):
   x_t(E) = (2√E/π)(log(2E/π) - 2)  (from N_smooth inversion)

6. **Oscillatory potential** (number theory):
   V_osc(x) = Σ_p (log p / √p) · cos(x·log p + φ_p)

This potential is NOT an artificial construction. It is the imprint of primes
on the potential, emerging naturally from the geometry of phase space through
quantum mechanics and Fourier analysis.

The final equation:
    V_osc(x) = Σ_p (log p / √p) · cos(x·log p + φ_p)

Mathematical Framework:
----------------------
Full Hamiltonian:
    H = -d²/dx² + V(x)
    V(x) = V_Abel(x) + ε · V_osc(x)

where:
    V_Abel(x): smooth potential from Abel inversion of N_smooth
    V_osc(x):  oscillatory prime-encoded potential from trace formula
    ε:         coupling constant (controls oscillatory strength)

References:
-----------
- Wu, H. & Sprung, D.W.L. (1993). Riemann zeros and a fractal potential.
  Phys. Rev. E, 48(4), 2595.
- Berry, M.V. & Keating, J.P. (1999). The Riemann zeros and eigenvalue
  asymptotics. SIAM Review, 41(2), 236-266.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import numpy as np
from typing import List, Optional, Tuple
from scipy.interpolate import interp1d
from scipy.linalg import eigh
from scipy.optimize import brentq

# QCAL Constants
F0 = 141.7001       # Fundamental frequency (Hz)
C_QCAL = 244.36     # QCAL coherence constant
DOI = "10.5281/zenodo.17379721"

# Mathematical constants
TWO_PI = 2.0 * np.pi
PI = np.pi


def sieve_primes(n_max: int) -> List[int]:
    """
    Generate all primes up to n_max using the Sieve of Eratosthenes.

    Args:
        n_max: Upper bound for prime sieve.

    Returns:
        List of primes p ≤ n_max.
    """
    if n_max < 2:
        return []
    is_prime = np.ones(n_max + 1, dtype=bool)
    is_prime[0] = False
    is_prime[1] = False
    for i in range(2, int(np.sqrt(n_max)) + 1):
        if is_prime[i]:
            is_prime[i * i :: i] = False
    return list(np.where(is_prime)[0])


def abel_turning_point(E: float) -> float:
    """
    Compute the classical turning point x_t(E) via the Abel inversion formula.

    Derived from the Weyl smooth counting function N_smooth(E):
        N_smooth(E) ≈ E/(2π) · log(E/(2πe))

    The inverse Abel transform yields:
        x_t(E) = (2√E/π)(log(2E/π) - 2)

    This relation encodes how the smooth part of the Riemann zero counting
    function translates into the turning-point function of the semiclassical
    potential.

    Args:
        E: Energy (must be positive).

    Returns:
        Classical turning point x_t(E) ≥ 0.

    Raises:
        ValueError: If E ≤ 0.
    """
    if E <= 0:
        raise ValueError(f"Energy E must be positive, got E={E}")
    return (2.0 * np.sqrt(E) / PI) * (np.log(2.0 * E / PI) - 2.0)


def abel_turning_point_array(E_array: np.ndarray) -> np.ndarray:
    """
    Vectorized computation of classical turning point x_t(E).

    Args:
        E_array: Array of energy values (all must be positive).

    Returns:
        Array of turning points x_t(E).
    """
    E_arr = np.asarray(E_array, dtype=float)
    return (2.0 * np.sqrt(E_arr) / PI) * (np.log(2.0 * E_arr / PI) - 2.0)


def v_abel_from_turning_point(
    x: np.ndarray,
    E_min: float = 1.0,
    E_max: float = 1000.0,
    n_grid: int = 10000,
) -> np.ndarray:
    """
    Compute smooth Abel potential V_Abel(x) by inverting x_t(E).

    For each spatial point x, solves x_t(E) = x numerically to find
    V_Abel(x) = E. Uses dense energy grid and interpolation.

    The turning-point function x_t(E) = (2√E/π)(log(2E/π) - 2) is
    monotone increasing for E > π/2·e² ≈ 10.04, so the inversion is
    well-defined in that regime.

    Args:
        x: Array of spatial positions (must be positive for physical domain).
        E_min: Minimum energy for inversion grid.
        E_max: Maximum energy for inversion grid.
        n_grid: Number of grid points for E → x_t(E) tabulation.

    Returns:
        V_Abel(x): Smooth potential values at each x.
    """
    # Build dense E → x_t(E) table
    E_grid = np.linspace(E_min, E_max, n_grid)
    x_t_grid = abel_turning_point_array(E_grid)

    # Only keep monotone increasing region for invertibility
    mono_mask = np.diff(x_t_grid) > 0
    # Include first point
    keep = np.concatenate(([True], mono_mask))
    E_mono = E_grid[keep]
    x_t_mono = x_t_grid[keep]

    # Build interpolator E(x_t) -- inverse of x_t(E)
    E_of_x = interp1d(
        x_t_mono,
        E_mono,
        kind="linear",
        bounds_error=False,
        fill_value=(E_mono[0], E_mono[-1]),
    )

    x_arr = np.asarray(x, dtype=float)
    return E_of_x(x_arr)


def v_osc(
    x: np.ndarray,
    primes: List[int],
    phases: Optional[np.ndarray] = None,
    p_max: int = 100,
) -> np.ndarray:
    """
    Compute oscillatory prime-encoded potential V_osc(x).

    Derived from the trace formula applied to chaotic quantum billiards:

        V_osc(x) = Σ_p (log p / √p) · cos(x·log p + φ_p)

    where the sum runs over primes p ≤ p_max.

    This is NOT artificial: V_osc(x) is the imprint of primes on the
    potential, emerging from the geometry of phase space through the
    Gutzwiller trace formula and inverse Abel transform.

    Mathematical derivation:
        Step 4 (Trace formula): N_osc(E) = -(1/π) Σ_p (log p/√p) sin(E·log p)
        Step 5 (Abel inversion): V_osc at x encodes the same prime oscillations
        Step 6 (Prime potential): V_osc(x) = Σ_p (log p/√p) cos(x·log p + φ_p)

    Args:
        x: Array of spatial positions.
        primes: List of prime numbers to include in the sum.
        phases: Phase shifts φ_p per prime (default: all zeros).
        p_max: Maximum prime to include (filters primes list).

    Returns:
        V_osc(x): Oscillatory potential at each x.
    """
    x_arr = np.asarray(x, dtype=float)
    filtered = [p for p in primes if p <= p_max]

    if phases is None:
        phi = np.zeros(len(filtered))
    else:
        phi = np.asarray(phases, dtype=float)
        if len(phi) != len(filtered):
            raise ValueError(
                f"phases length {len(phi)} must match number of primes {len(filtered)}"
            )

    result = np.zeros_like(x_arr)
    for i, p in enumerate(filtered):
        log_p = np.log(float(p))
        result += (log_p / np.sqrt(float(p))) * np.cos(x_arr * log_p + phi[i])

    return result


def v_wusprung(
    x: np.ndarray,
    primes: List[int],
    epsilon: float = 1.0,
    phases: Optional[np.ndarray] = None,
    p_max: int = 100,
    E_min: float = 1.0,
    E_max: float = 1000.0,
    n_grid: int = 10000,
) -> np.ndarray:
    """
    Compute full corrected Wu-Sprung potential.

        V(x) = V_Abel(x) + ε · V_osc(x)

    Combines:
    - V_Abel: smooth confining potential from Abel inversion of Weyl law
    - V_osc:  oscillatory prime correction from trace formula

    Args:
        x: Array of spatial positions (positive values recommended).
        primes: List of prime numbers for oscillatory term.
        epsilon: Coupling constant ε (strength of oscillatory correction).
        phases: Phase shifts φ_p per prime (default: all zeros).
        p_max: Maximum prime for oscillatory sum.
        E_min: Minimum energy for Abel inversion.
        E_max: Maximum energy for Abel inversion.
        n_grid: Grid size for Abel inversion.

    Returns:
        V(x) = V_Abel(x) + ε·V_osc(x) at each spatial point x.
    """
    V_smooth = v_abel_from_turning_point(x, E_min=E_min, E_max=E_max, n_grid=n_grid)
    V_oscillatory = v_osc(x, primes, phases=phases, p_max=p_max)
    return V_smooth + epsilon * V_oscillatory


def construct_hamiltonian(
    x: np.ndarray,
    primes: List[int],
    epsilon: float = 1.0,
    phases: Optional[np.ndarray] = None,
    p_max: int = 100,
    E_min: float = 1.0,
    E_max: float = 1000.0,
    n_grid: int = 10000,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Construct the corrected Wu-Sprung Hamiltonian matrix.

        H = -d²/dx² + V_Abel(x) + ε · V_osc(x)

    Uses finite-difference discretization on the provided grid x.
    Implements Dirichlet boundary conditions (ψ = 0 at boundaries).

    The kinetic term -d²/dx² is discretized as:
        (-d²/dx²)_{ij} = (2δ_{i,j} - δ_{i,j-1} - δ_{i,j+1}) / dx²

    Args:
        x: Uniform spatial grid (array of positions).
        primes: Primes for oscillatory potential.
        epsilon: Coupling constant ε.
        phases: Phase shifts per prime.
        p_max: Maximum prime for V_osc sum.
        E_min: Lower energy bound for Abel inversion.
        E_max: Upper energy bound for Abel inversion.
        n_grid: Grid size for Abel inversion.

    Returns:
        H: Hamiltonian matrix (n × n), symmetric.
        V: Potential array V(x) used in construction.
    """
    n = len(x)
    dx = x[1] - x[0]

    # Kinetic energy: -d²/dx² (finite difference, Dirichlet BC)
    diag_main = 2.0 * np.ones(n) / dx**2
    diag_off = -1.0 * np.ones(n - 1) / dx**2
    T = np.diag(diag_main) + np.diag(diag_off, 1) + np.diag(diag_off, -1)

    # Potential energy
    V = v_wusprung(
        x,
        primes,
        epsilon=epsilon,
        phases=phases,
        p_max=p_max,
        E_min=E_min,
        E_max=E_max,
        n_grid=n_grid,
    )
    V_matrix = np.diag(V)

    H = T + V_matrix
    # Enforce exact symmetry
    H = 0.5 * (H + H.T)

    return H, V


def compute_spectrum(
    H: np.ndarray,
    n_eigenvalues: Optional[int] = None,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues and eigenvectors of the Hamiltonian.

    Args:
        H: Symmetric Hamiltonian matrix.
        n_eigenvalues: Number of lowest eigenvalues to return.
            If None, returns all.

    Returns:
        eigenvalues: Sorted eigenvalues (ascending).
        eigenvectors: Corresponding normalized eigenvectors (columns).
    """
    eigenvalues, eigenvectors = eigh(H)
    if n_eigenvalues is not None:
        eigenvalues = eigenvalues[:n_eigenvalues]
        eigenvectors = eigenvectors[:, :n_eigenvalues]
    return eigenvalues, eigenvectors


class WuSprungHamiltonian:
    """
    Corrected Wu-Sprung Hamiltonian implementing H = -d²/dx² + V_Abel + ε·V_osc.

    Encapsulates the full derivation chain:
      WKB → density of states → smooth+oscillatory → trace formula
      → inverse Abel → prime potential V_osc → full Hamiltonian H.

    The oscillatory potential V_osc(x) = Σ_p (log p/√p)·cos(x·log p + φ_p)
    encodes the prime numbers directly into the quantum mechanical potential.

    Attributes:
        x: Spatial grid.
        primes: List of primes used in V_osc.
        epsilon: Oscillatory coupling constant.
        H: Hamiltonian matrix.
        V: Full potential array.
        V_abel: Smooth Abel potential.
        V_oscillatory: Oscillatory prime potential.
    """

    def __init__(
        self,
        x_min: float = 0.1,
        x_max: float = 30.0,
        n_points: int = 500,
        p_max: int = 100,
        epsilon: float = 1.0,
        phases: Optional[np.ndarray] = None,
        E_min: float = 1.0,
        E_max: float = 2000.0,
        n_grid: int = 20000,
    ) -> None:
        """
        Initialize and construct the corrected Wu-Sprung Hamiltonian.

        Args:
            x_min: Left boundary of spatial domain (must be > 0).
            x_max: Right boundary of spatial domain.
            n_points: Number of grid points.
            p_max: Maximum prime for V_osc sum.
            epsilon: Coupling constant ε for oscillatory term.
            phases: Phase shifts φ_p per prime (default: all zeros).
            E_min: Minimum energy for Abel inversion grid.
            E_max: Maximum energy for Abel inversion grid.
            n_grid: Grid density for Abel inversion.
        """
        if x_min <= 0:
            raise ValueError(f"x_min must be > 0, got {x_min}")
        if x_max <= x_min:
            raise ValueError(f"x_max must be > x_min, got x_max={x_max}, x_min={x_min}")

        self.x_min = x_min
        self.x_max = x_max
        self.n_points = n_points
        self.p_max = p_max
        self.epsilon = epsilon
        self.E_min = E_min
        self.E_max = E_max
        self.n_grid = n_grid

        # Generate primes
        self.primes = sieve_primes(p_max)

        # Set phases
        self.phases = phases

        # Build spatial grid
        self.x = np.linspace(x_min, x_max, n_points)

        # Compute potential components
        self.V_abel = v_abel_from_turning_point(
            self.x, E_min=E_min, E_max=E_max, n_grid=n_grid
        )
        self.V_oscillatory = v_osc(self.x, self.primes, phases=phases, p_max=p_max)
        self.V = self.V_abel + epsilon * self.V_oscillatory

        # Construct Hamiltonian
        self.H, _ = construct_hamiltonian(
            self.x,
            self.primes,
            epsilon=epsilon,
            phases=phases,
            p_max=p_max,
            E_min=E_min,
            E_max=E_max,
            n_grid=n_grid,
        )

        # Cache for spectrum
        self._eigenvalues: Optional[np.ndarray] = None
        self._eigenvectors: Optional[np.ndarray] = None

    def compute_spectrum(
        self, n_eigenvalues: int = 20
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute the lowest eigenvalues and eigenvectors.

        Args:
            n_eigenvalues: Number of lowest eigenvalues to compute.

        Returns:
            eigenvalues: Sorted real eigenvalues.
            eigenvectors: Corresponding normalized eigenvectors (columns).
        """
        self._eigenvalues, self._eigenvectors = compute_spectrum(
            self.H, n_eigenvalues=n_eigenvalues
        )
        return self._eigenvalues, self._eigenvectors

    def v_abel(self, x: np.ndarray) -> np.ndarray:
        """
        Evaluate smooth Abel potential at arbitrary points.

        Args:
            x: Spatial positions.

        Returns:
            V_Abel(x).
        """
        return v_abel_from_turning_point(
            x, E_min=self.E_min, E_max=self.E_max, n_grid=self.n_grid
        )

    def v_prime(self, x: np.ndarray) -> np.ndarray:
        """
        Evaluate oscillatory prime potential V_osc at arbitrary points.

        Args:
            x: Spatial positions.

        Returns:
            V_osc(x) = Σ_p (log p/√p)·cos(x·log p + φ_p).
        """
        return v_osc(x, self.primes, phases=self.phases, p_max=self.p_max)

    def potential(self, x: np.ndarray) -> np.ndarray:
        """
        Evaluate full potential V = V_Abel + ε·V_osc at arbitrary points.

        Args:
            x: Spatial positions.

        Returns:
            V(x) = V_Abel(x) + ε·V_osc(x).
        """
        return self.v_abel(x) + self.epsilon * self.v_prime(x)

    @property
    def n_primes(self) -> int:
        """Number of primes used in V_osc sum."""
        return len(self.primes)

    def __repr__(self) -> str:
        return (
            f"WuSprungHamiltonian("
            f"x=[{self.x_min}, {self.x_max}], "
            f"n={self.n_points}, "
            f"p_max={self.p_max}, "
            f"ε={self.epsilon}, "
            f"n_primes={self.n_primes})"
        )
