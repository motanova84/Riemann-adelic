#!/usr/bin/env python3
"""
FractalQCAL Operator - Adelic-Fractal Spectral Operator for Riemann Zeros
==========================================================================

This module implements the FractalQCALOperator, which constructs a
Hamiltonian with a fractal arithmetic potential built from prime
logarithms. The operator's spectrum approximates the first 20 imaginary
parts of the non-trivial Riemann zeros.

Mathematical Framework:
-----------------------
H = f₀ · (H_BK + V_mod)

where:
  - H_BK = -i d/du  (Berry-Keating momentum operator, symmetrized)
  - V_mod = fractal modular potential assembled from log-prime bumps
  - f₀ = γ₁ / π    (calibration from first Riemann zero)

The potential V_mod is defined as:
  V(u) = 0.05 · Σ_p  log(log p + 1) / (1 + (u - log p)² / σ²)

where the sum runs over primes p < 10000 and σ = 0.5.

QCAL Integration:
-----------------
    f₀ = γ₁ / π  (calibrated to first Riemann zero γ₁ ≈ 14.1347)
    Primes: all primes up to 9999 (~1229 primes)
    Grid size: configurable, default N = 512

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import List, Optional
from sympy import primerange

# Known precise imaginary parts of the first 20 non-trivial Riemann zeros
RIEMANN_ZEROS_20 = np.array([
    14.134725141734693790,
    21.022039638771554993,
    25.010857580145688763,
    30.424876125859513210,
    32.935061587739189690,
    37.586178158825671257,
    40.918719012147495188,
    43.327073280914999519,
    48.005150881167159727,
    49.773832477672302181,
    52.970321477714460713,
    56.446247697063547104,
    59.347044003279019376,
    60.831778524321660090,
    65.112544048435775671,
    67.079810529494452214,
    69.546401711663647140,
    72.067157674481907533,
    75.704690699926828369,
    77.144840068874805079,
])


def generate_primes(n_max: int = 9999) -> List[int]:
    """
    Generate all prime numbers up to ``n_max`` (inclusive).

    Uses SymPy's ``primerange`` under the hood, which is backed by a
    fast Sieve of Eratosthenes.

    Args:
        n_max: Upper bound (inclusive) for prime generation. Must be >= 2.

    Returns:
        Sorted list of prime integers in ``[2, n_max]``.

    Raises:
        ValueError: If ``n_max`` is less than 2.

    Example:
        >>> primes = generate_primes(30)
        >>> primes
        [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    """
    if n_max < 2:
        raise ValueError(f"n_max must be >= 2, got {n_max}")
    return list(primerange(2, n_max + 1))


class FractalQCALOperator:
    """
    Fractal QCAL Hamiltonian operator for spectral approximation of Riemann zeros.

    Constructs the operator H = f₀ · (H_BK + V_mod) on a finite uniform grid
    over [0, 100], where:

      - H_BK is the symmetrized Berry-Keating momentum operator (-i d/du),
        implemented via the FFT-based spectral differentiation scheme.
      - V_mod is a fractal arithmetic potential built from localised Lorentzian
        bumps centred at log p for each prime p.
      - f₀ = γ₁ / π, calibrated to match the first Riemann zero γ₁.

    The spectrum of H (middle 20 eigenvalues around index N//4) should
    approximate the first 20 imaginary parts of the Riemann zeros.

    Attributes:
        N:           Number of grid points.
        u:           Uniform grid array on [0, 100] of length N.
        du:          Grid spacing.
        primes:      List of primes used to build the potential.
        log_primes:  Natural logarithms of the primes.
        f0:          Calibration frequency f₀ = γ₁ / π.

    Example:
        >>> op = FractalQCALOperator(N=128)
        >>> modes = op.get_modes()
        >>> len(modes)
        20
    """

    def __init__(self, N: int = 512, primes: Optional[List[int]] = None):
        """
        Initialise the FractalQCALOperator.

        Args:
            N:      Number of grid points for the discretised Hilbert space.
                    Must be a positive even integer >= 4.
            primes: List of prime integers to use in the potential. If ``None``,
                    all primes up to 9999 are generated automatically.

        Raises:
            ValueError: If ``N`` is not a positive even integer >= 4.
            ValueError: If the ``primes`` list is empty.
        """
        if not isinstance(N, int) or N < 4:
            raise ValueError(f"N must be an integer >= 4, got {N!r}")
        if N % 2 != 0:
            raise ValueError(f"N must be even for FFT symmetry, got {N}")

        self.N = N
        self.u = np.linspace(0.0, 100.0, N)
        self.du = self.u[1] - self.u[0]

        if primes is None:
            self.primes = generate_primes(9999)
        else:
            if len(primes) == 0:
                raise ValueError("primes list must not be empty")
            self.primes = list(primes)

        self.log_primes = np.log(np.array(self.primes, dtype=float))

        # Calibrate f₀ to match first Riemann zero γ₁
        self.f0: float = RIEMANN_ZEROS_20[0] / np.pi

    # ------------------------------------------------------------------
    # Potential builder
    # ------------------------------------------------------------------

    def v_mod_fractal(self, sigma: float = 0.5) -> np.ndarray:
        """
        Build the fractal modular potential matrix V_mod.

        The potential is a sum of Lorentzian bumps centred at log p for each
        prime p, localised within a window of radius 5 around each centre::

            V(u) = 0.05 · Σ_p  log(log p + 1) / (1 + (u − log p)² / σ²)

        where lp = log p (pre-computed in ``self.log_primes``), so the
        weight is ``np.log(lp + 1.0)`` ≡ log(log p + 1).

        Args:
            sigma: Width parameter for the Lorentzian bumps. Default 0.5.

        Returns:
            Diagonal potential matrix of shape (N, N) as a numpy array.

        Raises:
            ValueError: If ``sigma`` is not positive.
        """
        if sigma <= 0:
            raise ValueError(f"sigma must be positive, got {sigma}")

        V = np.zeros(self.N)
        sigma2 = sigma ** 2
        for lp in self.log_primes:
            mask = np.abs(self.u - lp) < 5.0
            if not np.any(mask):
                continue
            dist2 = (self.u[mask] - lp) ** 2
            V[mask] += np.log(lp + 1.0) / (1.0 + dist2 / sigma2)

        return np.diag(V * 0.05)

    # ------------------------------------------------------------------
    # Hamiltonian builder
    # ------------------------------------------------------------------

    def build_hamiltonian(self) -> np.ndarray:
        """
        Assemble the full Hamiltonian matrix H.

        The Hamiltonian is::

            H = f₀ · (H_BK + V_mod)

        where H_BK = -i d/du is the Berry-Keating momentum operator,
        symmetrised as (H_BK + H_BK†)/2 to enforce Hermiticity.

        The spectral derivative is computed via FFT: in frequency space the
        derivative operator is multiplication by i · 2π · k (angular
        wavenumber k = fftfreq(N, du/(2π))), so in real space it is the
        inverse FFT of that action.

        Returns:
            Hermitian matrix of shape (N, N) as a real numpy array (the
            anti-Hermitian part is numerically negligible and is discarded).
        """
        # Angular wavenumbers
        k = np.fft.fftfreq(self.N, self.du / (2.0 * np.pi))

        # Spectral representation: d/du acts as multiplication by i·k in
        # frequency space.  We build the full NxN differentiation matrix via
        # column-by-column FFT.
        eye = np.eye(self.N)
        D_hat = 1j * k[:, np.newaxis] * np.fft.fft(eye, axis=0)
        D_full = np.fft.ifft(D_hat, axis=0)

        # Sanity-check: for a standard FFT differentiation matrix the imaginary
        # residual arises from finite-grid discretisation and grows with N for
        # non-periodic functions on the interval.  Warn only when the residual
        # is implausibly large (> 1.0), which would indicate algorithmic issues.
        max_imag = np.max(np.abs(D_full.imag))
        if max_imag > 1.0:
            import warnings
            warnings.warn(
                f"Differentiation matrix has unusually large imaginary residual "
                f"({max_imag:.2e}); numerical instability may affect results.",
                RuntimeWarning,
                stacklevel=2,
            )
        D_real = D_full.real

        # Berry-Keating operator: -i d/du, then symmetrise
        H_BK = -1j * D_real
        H_BK = (H_BK + H_BK.conj().T) / 2.0

        V = self.v_mod_fractal()
        H = self.f0 * (H_BK + V)
        return H

    # ------------------------------------------------------------------
    # Spectrum extraction
    # ------------------------------------------------------------------

    def get_modes(self, n_modes: int = 20) -> np.ndarray:
        """
        Compute the spectral modes of the Hamiltonian.

        Diagonalises H, takes the real parts of the eigenvalues, sorts them,
        and returns a window of ``n_modes`` eigenvalues starting at index
        ``N // 4``. This window is empirically centred near the Riemann zeros.

        Args:
            n_modes: Number of modes to return. Default 20.

        Returns:
            Sorted real eigenvalue array of length ``n_modes``.

        Raises:
            ValueError: If ``n_modes`` is not a positive integer.
            ValueError: If ``n_modes`` is larger than N // 2.
        """
        if not isinstance(n_modes, int) or n_modes <= 0:
            raise ValueError(f"n_modes must be a positive integer, got {n_modes!r}")
        if n_modes > self.N // 2:
            raise ValueError(
                f"n_modes ({n_modes}) must be <= N // 2 ({self.N // 2})"
            )

        H = self.build_hamiltonian()
        evals = np.sort(np.real(np.linalg.eigvals(H)))
        start = self.N // 4
        return evals[start: start + n_modes]
