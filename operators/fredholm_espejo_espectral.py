#!/usr/bin/env python3
"""
Fredholm Espejo Espectral — Hilbert-Pólya Mirror Comparison
============================================================

Implements the spectral mirror comparison between the approximate Fredholm
log-determinant (built from operator eigenvalues) and the Riemann Xi function.
This is the culmination of the Hilbert-Pólya program: if the two curves coincide,
the operator eigenvalues encode the Riemann zeros on the critical line.

Mathematical Framework
----------------------

**Free Term (Weyl Law)**

The mean density of zeros up to height T follows the Weyl/Berry-Keating law:

    N(T) ≈ (T / 2π) log(T / (2πe)) + 7/8

Its continuous antiderivative (the smooth baseline for log|ξ|) is:

    free_term(t) = (t / 2) · log(t / (2π·e))

This term removes the secular drift from the spectral log-determinant so that
only the oscillatory (zero-driven) part remains.

**Fredholm Log-Determinant Approximation**

Given eigenvalues {λ_i} of the Hilbert-Pólya operator, the approximate
log-|det(t − H)| is:

    fredholm_logdet_approx(t, evals, cutoff) =
        Σ_{i=1}^{cutoff} log|t − λ_i| − free_term(t)

After subtracting the free term this should oscillate in phase with
Re log ξ(1/2 + it).

**Ritual del Espejo**

Computes both curves over a range of t values and returns them for
comparison.  Coincidence of oscillations is the numerical signature of
the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-ESPEJO-ESPECTRAL v1.0
Date: March 2026
DOI: 10.5281/zenodo.17379721

QCAL ∞³ · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

from typing import Tuple

import mpmath as mp
import numpy as np

# QCAL Constants
F0_QCAL = 141.7001  # Hz - fundamental frequency
C_COHERENCE = 244.36  # Coherence constant

# Set mpmath precision for Riemann Xi evaluations
mp.mp.dps = 25


def _riemann_xi(s: complex) -> mp.mpc:
    """
    Compute the Riemann Xi function ξ(s) using mpmath primitives.

    Definition (avoiding the pole of Γ at s=0):

        ξ(s) = (s − 1) · π^{−s/2} · Γ(s/2) · ζ(s)

    This is equivalent to the standard symmetric form
    ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s) up to the constant factor ½s,
    but avoids division-by-zero issues and is consistent with the
    implementation used throughout this repository.

    Args:
        s: Complex argument as a Python complex or mp.mpc.

    Returns:
        mp.mpc value of ξ(s).
    """
    s_mp = mp.mpc(s)
    return (s_mp - 1) * mp.power(mp.pi, -s_mp / 2) * mp.gamma(s_mp / 2) * mp.zeta(s_mp)


def free_term(t: float) -> float:
    """
    Weyl law smooth baseline for the log-|xi| function.

    Provides the secular (non-oscillatory) trend that must be subtracted
    from the spectral log-sum so that only the oscillatory content driven
    by the Riemann zeros remains.

    Based on the Berry-Keating / Weyl law for the zero-counting function:

        N(T) ≈ (T / 2π) log(T / (2πe)) + 7/8

    The derivative of the smooth part of log|ξ(1/2+it)| is approximately
    (1/2) log(t / (2π)), so its primitive is used here as the baseline:

        free_term(t) = (t / 2) · log(t / (2π·e))

    Args:
        t: Real parameter t > 0 (imaginary part of s = 1/2 + it).

    Returns:
        Smooth Weyl baseline value at t.

    Raises:
        ValueError: If t is not positive.
    """
    if t <= 0:
        raise ValueError(f"free_term requires t > 0, got t={t}")
    return (t / 2.0) * np.log(t / (2.0 * np.pi * np.e))


def fredholm_logdet_approx(
    t: float,
    evals: np.ndarray,
    cutoff: int = 500,
) -> float:
    """
    Approximate Fredholm log-determinant minus the Weyl free term.

    Computes the spectral sum

        Σ_{i=1}^{min(cutoff, len(evals))} log|t − λ_i| − free_term(t)

    which, when the eigenvalues {λ_i} are the imaginary parts of the
    Riemann zeros, should reproduce the oscillations of Re log ξ(1/2+it).

    A small regularisation ε = 1e-12 prevents log(0) when t ≈ λ_i.

    Args:
        t: Real evaluation point (imaginary part of s = 1/2 + it).
        evals: Array of operator eigenvalues λ_i (real).
        cutoff: Maximum number of eigenvalues to include in the sum.
            Defaults to 500 (as suggested by the problem statement).

    Returns:
        Float value of the regularised log-determinant minus free term.

    Raises:
        ValueError: If evals is empty or cutoff < 1.
    """
    if len(evals) == 0:
        raise ValueError("evals must be a non-empty array of eigenvalues.")
    if cutoff < 1:
        raise ValueError(f"cutoff must be >= 1, got {cutoff}.")

    selected = evals[: min(cutoff, len(evals))]
    epsilon_reg = 1e-12
    log_sum = np.sum(np.log(np.abs(t - selected) + epsilon_reg))
    return float(log_sum - free_term(t))


def ritual_del_espejo(
    t_range: np.ndarray,
    evals: np.ndarray,
    cutoff: int = 500,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compare the Fredholm spectral log-det with Re log|ξ(1/2 + it)|.

    For each t in t_range this function evaluates:
      • det_approx[i]  = fredholm_logdet_approx(t_range[i], evals, cutoff)
      • xi_real[i]     = Re log|ξ(1/2 + i·t_range[i])| via mpmath

    Coincidence of oscillatory features between the two curves provides
    numerical evidence for the Hilbert-Pólya interpretation of the
    Riemann Hypothesis.

    Args:
        t_range: 1-D array of positive real t values to evaluate.
        evals: Array of operator eigenvalues λ_i (real).
        cutoff: Maximum eigenvalues used in the spectral sum (default 500).

    Returns:
        Tuple (det_approx, xi_real) where both are 1-D float arrays of the
        same length as t_range.

    Raises:
        ValueError: If t_range contains non-positive values, or if evals is
            empty.
    """
    if len(evals) == 0:
        raise ValueError("evals must be a non-empty array of eigenvalues.")
    if np.any(t_range <= 0):
        raise ValueError("All values in t_range must be positive (t > 0).")

    print("∴𓂀Ω∞³Φ - SISTEMA: COMPARANDO REALIDADES")

    det_approx = np.empty(len(t_range), dtype=float)
    xi_real = np.empty(len(t_range), dtype=float)

    for idx, t in enumerate(t_range):
        s = 0.5 + 1j * float(t)

        # Fredholm spectral log-det (Weyl-subtracted)
        det_approx[idx] = fredholm_logdet_approx(float(t), evals, cutoff=cutoff)

        # Ground truth: Re log|ξ(1/2 + it)| via mpmath
        xi_val = float(mp.log(mp.fabs(_riemann_xi(mp.mpc(s.real, s.imag)))))
        xi_real[idx] = xi_val

    return det_approx, xi_real
