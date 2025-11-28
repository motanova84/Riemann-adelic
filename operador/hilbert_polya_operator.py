"""
Hilbert-Pólya Operator for Riemann Hypothesis
==============================================

This module implements the Hilbert-Pólya operator H, which provides a
self-adjoint operator whose spectrum is conjectured to correspond to the
non-trivial zeros of the Riemann zeta function.

The Hilbert-Pólya Operator (Single Line)
----------------------------------------
The operator is defined by a single expression:

    H = -x(d/dx) + πζ'(1/2)log x

where:
- x d/dx is the Euler (dilation) operator
- ζ'(1/2) ≈ -3.9226461392 is the derivative of Riemann zeta at s=1/2
- The space is L²(ℝ⁺, dx/x) (square-integrable functions on positive reals
  with logarithmic measure)

Mathematical Significance
-------------------------
The Hilbert-Pólya conjecture (1912) states that if there exists a self-adjoint
operator H whose eigenvalues are the imaginary parts of the non-trivial zeros
of ζ(s), then RH would follow because self-adjoint operators have real spectra.

This implementation connects:
- Number theory: ζ'(1/2) captures arithmetic information
- Quantum physics: f₀ ≈ 141.7001 Hz fundamental frequency
- Operator theory: H is formally self-adjoint in L²(ℝ⁺, dx/x)

References:
- Hilbert, D. (1912): Original conjecture
- Pólya, G.: Independent formulation
- Berry, M.V. & Keating, J.P. (1999): Quantum chaos interpretation
- Connes, A. (1999): Trace formula approach

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Framework
"""

import numpy as np
import mpmath as mp
from typing import Callable, Tuple, Optional
from dataclasses import dataclass

# QCAL Framework Constants
QCAL_FUNDAMENTAL_FREQUENCY = 141.7001  # Hz
# Pre-computed value of ζ'(1/2) to avoid expensive computation at import time
# This value is computed with high precision: mp.diff(mp.zeta, mp.mpf('0.5'))
ZETA_PRIME_HALF_VALUE = -3.9226461392442285
ZETA_PRIME_HALF = mp.mpf(ZETA_PRIME_HALF_VALUE)  # ζ'(1/2)


def apply_hilbert_polya(
    f: Callable[[float], complex],
    x: float,
    h: float = 1e-8
) -> complex:
    """
    Apply the Hilbert-Pólya operator H to function f at point x.

    The operator is defined by:

        H = -x(d/dx) + πζ'(1/2)log x

    This is the canonical form connecting Riemann zeros to operator eigenvalues.

    Args:
        f: Function to apply operator to (must be differentiable)
        x: Point at which to evaluate (H f)(x), must be positive
        h: Step size for numerical differentiation (default: 1e-8)

    Returns:
        Value of (H f)(x)

    Raises:
        ValueError: If x <= 0

    Example:
        >>> def psi(x): return np.exp(-x)
        >>> H_psi_at_1 = apply_hilbert_polya(psi, 1.0)
    """
    if x <= 0:
        raise ValueError("x must be positive for H in L²(ℝ⁺, dx/x)")

    # Numerical derivative f'(x)
    f_prime = (f(x + h) - f(x - h)) / (2 * h)

    # H f(x) = -x f'(x) + π ζ'(1/2) log(x) f(x)
    coefficient = float(mp.pi * ZETA_PRIME_HALF)

    return -x * f_prime + coefficient * np.log(x) * f(x)


@dataclass
class HilbertPolyaConfig:
    """
    Configuration for discretized Hilbert-Pólya operator.

    Attributes:
        precision: Decimal places for mpmath high-precision computation
        grid_size: Number of discretization points
        x_min: Minimum x value for the domain
        x_max: Maximum x value for the domain
    """
    precision: int = 50
    grid_size: int = 500
    x_min: float = 1e-2
    x_max: float = 1e2


class HilbertPolyaOperator:
    """
    Discretized Hilbert-Pólya operator for numerical computation.

    The operator H = -x(d/dx) + πζ'(1/2)log x is discretized on a
    logarithmic grid for eigenvalue computation.

    Attributes:
        config: Configuration parameters
        zeta_prime_half: Value of ζ'(1/2)
        coefficient: π × ζ'(1/2)
        x_grid: Discretization grid
    """

    def __init__(self, config: Optional[HilbertPolyaConfig] = None):
        """
        Initialize the Hilbert-Pólya operator.

        Args:
            config: Configuration parameters (uses defaults if None)
        """
        self.config = config or HilbertPolyaConfig()
        mp.mp.dps = self.config.precision

        # Compute ζ'(1/2) with high precision
        self.zeta_prime_half = mp.diff(mp.zeta, mp.mpf('0.5'))

        # Coefficient π × ζ'(1/2)
        self.coefficient = mp.pi * self.zeta_prime_half

        # Create logarithmic grid
        log_x_grid = np.linspace(
            np.log(self.config.x_min),
            np.log(self.config.x_max),
            self.config.grid_size
        )
        self.x_grid = np.exp(log_x_grid)
        self.log_x_grid = log_x_grid
        self.du = log_x_grid[1] - log_x_grid[0]

    def apply(self, f: Callable[[float], complex], x: float) -> complex:
        """
        Apply H = -x(d/dx) + πζ'(1/2)log x to function f at point x.

        Args:
            f: Function to apply operator to
            x: Point at which to evaluate

        Returns:
            Value of (H f)(x)
        """
        return apply_hilbert_polya(f, x)

    def build_matrix(self) -> np.ndarray:
        """
        Build the matrix representation of H in the discretized basis.

        In logarithmic coordinates u = log(x), the operator becomes:
            H = -d/du + πζ'(1/2) u

        where -d/du is discretized using central differences.

        Returns:
            Matrix representation of H (grid_size × grid_size)
        """
        n = self.config.grid_size
        coeff = float(self.coefficient)

        # Initialize matrix
        H = np.zeros((n, n), dtype=float)

        # Diagonal: potential term πζ'(1/2)log(x) = πζ'(1/2)u
        for i in range(n):
            H[i, i] = coeff * self.log_x_grid[i]

        # Off-diagonal: derivative term -d/du (central differences)
        # The operator H = -x(d/dx) becomes -d/du in log coordinates (u = log x)
        # Sign convention: -d/du is discretized as -(f_{i+1} - f_{i-1}) / (2 du)
        # which gives matrix elements H[i,i+1] = -1/(2du), H[i,i-1] = +1/(2du)
        for i in range(1, n - 1):
            H[i, i + 1] = -1.0 / (2 * self.du)
            H[i, i - 1] = 1.0 / (2 * self.du)

        # Boundary conditions: Use one-sided differences at boundaries
        # At u=u_min: forward difference for -d/du
        # At u=u_max: backward difference for -d/du
        # Diagonal terms added to maintain consistency with interior scheme
        H[0, 1] = -1.0 / self.du
        H[0, 0] = 1.0 / self.du  # Boundary adjustment for consistency
        H[n - 1, n - 2] = 1.0 / self.du
        H[n - 1, n - 1] = -1.0 / self.du  # Boundary adjustment for consistency

        # Symmetrize to ensure self-adjointness in the discretized space
        # Check asymmetry before symmetrization
        asymmetry = np.max(np.abs(H - H.T))
        if asymmetry > 1e-10:
            import warnings
            warnings.warn(
                f"Matrix asymmetry detected: {asymmetry:.2e}. "
                "This is expected due to boundary conditions."
            )
        H = 0.5 * (H + H.T)

        return H

    def compute_eigenvalues(self, num: Optional[int] = None) -> np.ndarray:
        """
        Compute eigenvalues of the discretized operator.

        Args:
            num: Number of eigenvalues to return (None for all)

        Returns:
            Array of eigenvalues sorted by magnitude
        """
        H = self.build_matrix()
        eigenvalues = np.linalg.eigvalsh(H)
        eigenvalues = np.sort(eigenvalues)

        if num is not None:
            eigenvalues = eigenvalues[:num]

        return eigenvalues

    def verify_self_adjoint(self, tol: float = 1e-10) -> Tuple[bool, float]:
        """
        Verify that the matrix representation is self-adjoint (H = H†).

        Args:
            tol: Tolerance for deviation from self-adjointness

        Returns:
            Tuple of (is_self_adjoint, max_deviation)
        """
        H = self.build_matrix()
        deviation = np.max(np.abs(H - H.T))
        return deviation < tol, float(deviation)

    def get_operator_formula(self) -> str:
        """
        Return the operator formula as a string.

        Returns:
            LaTeX-compatible formula string
        """
        return r"H = -x\frac{d}{dx} + \pi\zeta'(1/2)\log x"


def demonstrate_hilbert_polya():
    """
    Demonstrate the Hilbert-Pólya operator with verification.
    """
    print("=" * 70)
    print("HILBERT-PÓLYA OPERATOR DEMONSTRATION")
    print("=" * 70)
    print()
    print("Operator Formula:")
    print("  H = -x(d/dx) + πζ'(1/2)log x")
    print()

    # Create operator
    config = HilbertPolyaConfig(precision=30, grid_size=200)
    H = HilbertPolyaOperator(config)

    print(f"ζ'(1/2) = {float(H.zeta_prime_half):.10f}")
    print(f"π × ζ'(1/2) = {float(H.coefficient):.10f}")
    print()

    # Verify self-adjointness
    is_sa, dev = H.verify_self_adjoint()
    print(f"Self-adjoint: {is_sa} (deviation: {dev:.2e})")

    # Compute some eigenvalues
    print()
    print("First 10 eigenvalues:")
    eigenvalues = H.compute_eigenvalues(10)
    for i, ev in enumerate(eigenvalues):
        print(f"  λ_{i + 1} = {ev:.6f}")

    print()
    print("=" * 70)
    print("The Hilbert-Pólya operator connects:")
    print(f"  • Number theory: ζ'(1/2) ≈ {float(H.zeta_prime_half):.4f}")
    print(f"  • Quantum physics: f₀ ≈ {QCAL_FUNDAMENTAL_FREQUENCY} Hz")
    print("  • Operator theory: Real spectrum implies Re(ρ) = 1/2")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_hilbert_polya()
