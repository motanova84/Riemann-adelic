"""Numerical helpers for discretizing the dilation operator and prime potential.

These routines provide concrete implementations for the helper functions used in
``Coronación V5``'s numerical validation snippet.  They assemble finite-difference
matrices that approximate the symmetric dilation operator

    H_0 = 1/2 (X P + P X)

on a logarithmic grid together with the diagonal prime potential discussed in the
text.  The resulting matrices are Hermitian and are designed to be fed directly to
``scipy.linalg.eigh``.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import numpy as np


@dataclass
class PrimePotentialConfig:
    """Configuration parameters controlling the prime potential discretisation."""

    max_prime: int = 1000
    max_power: int = 8
    tolerance: float = 1e-12


def _validate_grid(x: np.ndarray) -> np.ndarray:
    """Return a validated copy of the logarithmic grid used for discretisation."""

    grid = np.asarray(x, dtype=float)
    if grid.ndim != 1:
        raise ValueError("x must be a one-dimensional array of sample points")
    if np.any(grid <= 0):
        raise ValueError("x must contain strictly positive sampling points")
    if grid.size < 2:
        raise ValueError("x must contain at least two sampling points")
    if not np.all(np.diff(grid) > 0):
        raise ValueError("x must be strictly increasing")
    return grid


def build_dilation_operator(x: Iterable[float]) -> np.ndarray:
    """Construct a finite-difference discretisation of ``(XP + PX)/2``.

    Parameters
    ----------
    x:
        Monotonically increasing grid of positive sampling points.  A logarithmic
        grid (as produced by ``np.logspace``) gives the cleanest approximation.

    Returns
    -------
    numpy.ndarray
        Complex Hermitian matrix approximating the symmetric dilation operator on
        the supplied grid.
    """

    grid = _validate_grid(np.asarray(x, dtype=float))
    log_grid = np.log(grid)
    step = np.diff(log_grid)
    if not np.allclose(step, step[0]):
        # fall back to the average spacing when the grid is not perfectly uniform
        delta = np.mean(step)
    else:
        delta = step[0]

    n = grid.size
    derivative = np.zeros((n, n), dtype=float)
    coeff = 1.0 / (2.0 * delta)
    for i in range(n - 1):
        derivative[i, i + 1] = coeff
        derivative[i + 1, i] = -coeff

    # Force exact skew-symmetry to guarantee Hermiticity after the similarity
    derivative = 0.5 * (derivative - derivative.T)

    diag_log = np.diag(log_grid)
    generator = -0.5j * (diag_log @ derivative + derivative @ diag_log)

    # The measure on L^2(dx/x) introduces a 1/2 shift that we capture explicitly.
    shift = -0.5j * derivative
    return generator + shift


def _prime_sieve(limit: int) -> list[int]:
    """Return all primes up to and including ``limit`` using a simple sieve."""

    if limit < 2:
        return []
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = False
    return np.nonzero(sieve)[0].tolist()


def build_prime_potential(
    x: Iterable[float],
    *,
    config: PrimePotentialConfig | None = None,
) -> np.ndarray:
    """Assemble the diagonal matrix for ``V_prime`` on the supplied grid.

    Parameters
    ----------
    x:
        Sampling grid matching the one used for ``build_dilation_operator``.
    config:
        Optional :class:`PrimePotentialConfig` with convergence controls.

    Returns
    -------
    numpy.ndarray
        Real diagonal matrix encoding the discretised prime potential.
    """

    grid = _validate_grid(np.asarray(x, dtype=float))
    settings = config or PrimePotentialConfig()
    primes = _prime_sieve(settings.max_prime)

    if not primes:
        return np.zeros((grid.size, grid.size), dtype=float)

    log_grid = np.log(grid)
    potential_values = np.zeros_like(log_grid)

    for p in primes:
        log_p = float(np.log(p))
        mangoldt = log_p  # Λ(p^k) = log p
        for k in range(1, settings.max_power + 1):
            amplitude = mangoldt / (p ** (0.5 * k))
            if abs(amplitude) < settings.tolerance:
                break
            potential_values += amplitude * np.cos(k * log_p * log_grid)

    return np.diag(potential_values)


__all__ = [
    "PrimePotentialConfig",
    "build_dilation_operator",
    "build_prime_potential",
]
