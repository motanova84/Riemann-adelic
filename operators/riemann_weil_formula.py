#!/usr/bin/env python3
"""
Guinand-Weil Explicit Formula — Connection between Riemann Zeros and Prime Powers
==================================================================================

Mathematical Framework:
----------------------

This module implements the rigorous Guinand-Weil explicit formula that connects
the Riemann zeros with prime powers:

    Σ_n Φ(t_n) = ∫ Φ(r) μ(r) dr - Σ_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]

where:
- t_n are the imaginary parts of non-trivial Riemann zeta zeros
- Φ is a suitable test function (e.g., Gaussian)
- μ(r) = (1/2π)·ln(r/2π) is the Weyl measure (smooth zero density)
- Φ̂(ξ) is the Fourier transform with normalization Φ̂(ξ) = (1/2π)∫Φ(r)e^{-iξr}dr
- p runs over primes, k over positive integers

Historical Context:
------------------
- Riemann (1859): Explicit formula relating zeros and primes
- Guinand (1948): Refined Fourier-theoretic version
- Weil (1952): General formulation for L-functions

This implementation provides:
1. Weyl density μ(r) — smooth approximation to zero counting function
2. Normalized Fourier transforms for test functions
3. Prime power sum — oscillatory contribution from primes
4. Smooth integral — contribution from Weyl measure
5. Full oscillatory counting correction N_osc_full(E)
6. Oscillatory density d_osc(E)
7. Complete verification framework
8. N_smooth(E) — Backlund smooth counting function N_smooth = E/(2π)·ln(E/(2πe)) + 7/8
9. gue_level_spacing_stats — Level spacing moments ⟨s⟩, ⟨s²⟩ and KS-test vs GUE

The formula demonstrates the deep arithmetic-spectral duality at the heart of
the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import math
import numpy as np
from typing import Callable, Dict, List, Tuple, Optional
from numpy.typing import NDArray
from dataclasses import dataclass
import warnings

try:
    from scipy import stats as _scipy_stats
    HAS_SCIPY_STATS = True
    # scipy.stats provides the KS p-value; without it only the KS statistic is available.
except ImportError:
    HAS_SCIPY_STATS = False

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available, using scipy approximations")

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz - fundamental frequency
C_PRIMARY = 629.83           # Primary spectral constant
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ
KAPPA_PI = 2.5773            # Critical curvature

# First few non-trivial Riemann zeros (imaginary parts)
ZEROS_ZETA_REFERENCE = [
    14.134725141734695,
    21.022039638771556,
    25.01085758014569,
    30.424876125859512,
    32.93506158773919,
    37.58617815882569,
    40.91871901214149,
    43.32707328091499,
    48.00515088116715,
    49.77383247767230
]


def weyl_density(r: float) -> float:
    """
    Compute the Weyl measure μ(r) = (1/2π)·ln(r/2π).
    
    This is the smooth approximation to the zero counting function N(T),
    representing the average density of zeros. It's derived from N_smooth(T)
    which counts zeros up to height T.
    
    Mathematical Derivation:
        N_smooth(T) = (T/2π)·ln(T/2π) - T/2π + O(ln T)
        dN_smooth/dT = μ(T) = (1/2π)·ln(T/2π) + (1/2π) - 1/2π
                            ≈ (1/2π)·ln(T/2π)  (leading term)
    
    Args:
        r: Height parameter (typically imaginary part of zero)
        
    Returns:
        Weyl density μ(r)
        
    Raises:
        ValueError: If r ≤ 0
    """
    if r <= 0:
        raise ValueError(f"Height parameter r must be positive, got r={r}")
    
    # Weyl measure: (1/2π)·ln(r/2π)
    return (1.0 / (2.0 * math.pi)) * math.log(r / (2.0 * math.pi))


def fourier_gaussian_norm(
    xi: float, 
    sigma: float = 1.0, 
    center: float = 0.0
) -> float:
    """
    Normalized Fourier transform of Gaussian test function.
    
    For Φ(r) = exp(-0.5 * ((r - center)/sigma)^2), the normalized Fourier
    transform with convention Φ̂(ξ) = (1/2π)∫Φ(r)e^{-iξr}dr is:
    
        Φ̂(ξ) = (sigma/2π) · exp(-0.5 * sigma^2 * ξ^2) · exp(-i·ξ·center)
    
    For real ξ, we take the real part (cosine term):
        Re[Φ̂(ξ)] = (sigma/2π) · exp(-0.5 * sigma^2 * ξ^2) · cos(ξ·center)
    
    Args:
        xi: Frequency variable
        sigma: Width parameter of Gaussian (default: 1.0)
        center: Center position of Gaussian (default: 0.0)
        
    Returns:
        Real part of normalized Fourier transform
    """
    # Amplitude factor with normalization
    amplitude = sigma / (2.0 * math.pi)
    
    # Gaussian envelope in frequency space
    envelope = math.exp(-0.5 * sigma**2 * xi**2)
    
    # Phase factor (real part: cosine)
    phase = math.cos(xi * center)
    
    return amplitude * envelope * phase


def fourier_transform_norm(
    Phi: Callable[[float], float],
    xi: float,
    r_min: float = 0.1,
    r_max: float = 100.0,
    num_points: int = 1000
) -> float:
    """
    Compute normalized Fourier transform numerically.
    
    Φ̂(ξ) = (1/2π) ∫ Φ(r) e^{-iξr} dr
    
    For real test functions, we compute:
        Re[Φ̂(ξ)] = (1/2π) ∫ Φ(r) cos(ξr) dr
    
    Args:
        Phi: Test function Φ(r)
        xi: Frequency variable
        r_min: Lower integration limit (default: 0.1)
        r_max: Upper integration limit (default: 100.0)
        num_points: Number of quadrature points (default: 1000)
        
    Returns:
        Real part of Φ̂(ξ)
    """
    # Integration grid
    r_values = np.linspace(r_min, r_max, num_points)
    dr = (r_max - r_min) / (num_points - 1)
    
    # Integrand: Φ(r) · cos(ξr)
    integrand = np.array([Phi(r) * math.cos(xi * r) for r in r_values])
    
    # Trapezoidal integration
    integral = np.trapezoid(integrand, dx=dr)
    
    # Apply normalization factor (1/2π)
    return integral / (2.0 * math.pi)


def prime_power_sum(
    Phi_hat_norm: Callable[[float], float],
    primes_upto: int = 200,
    k_max: int = 6
) -> float:
    """
    Compute the prime power sum (oscillatory RHS).
    
    Mathematical Formula:
        -Σ_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
    
    This represents the oscillatory contribution from closed geodesics
    (prime powers) in the arithmetic-geometric correspondence.
    
    Args:
        Phi_hat_norm: Normalized Fourier transform Φ̂(ξ)
        primes_upto: Maximum prime to include (default: 200)
        k_max: Maximum power k (default: 6)
        
    Returns:
        Prime power sum contribution
    """
    # Generate primes up to limit
    primes = _sieve_primes(primes_upto)
    
    total_sum = 0.0
    
    for p in primes:
        ln_p = math.log(p)
        
        for k in range(1, k_max + 1):
            # Weight: (ln p) / p^{k/2}
            weight = ln_p / (p ** (k / 2.0))
            
            # Argument: ln(p^k) = k·ln(p)
            arg = k * ln_p
            
            # Fourier transform at ±arg
            phi_pos = Phi_hat_norm(arg)
            phi_neg = Phi_hat_norm(-arg)
            
            # Contribution (note negative sign in formula)
            total_sum -= weight * (phi_pos + phi_neg)
    
    return total_sum


def weil_smooth_integral(
    Phi: Callable[[float], float],
    r_min: float = 1.0,
    r_max: float = 100.0,
    num_points: int = 1000
) -> float:
    """
    Compute the Weyl smooth integral.
    
    Mathematical Formula:
        ∫ Φ(r) μ(r) dr
    
    where μ(r) = (1/2π)·ln(r/2π) is the Weyl measure.
    
    Args:
        Phi: Test function Φ(r)
        r_min: Lower integration limit (default: 1.0)
        r_max: Upper integration limit (default: 100.0)
        num_points: Number of quadrature points (default: 1000)
        
    Returns:
        Weyl integral contribution
    """
    # Integration grid
    r_values = np.linspace(r_min, r_max, num_points)
    dr = (r_max - r_min) / (num_points - 1)
    
    # Integrand: Φ(r) · μ(r)
    integrand = np.array([Phi(r) * weyl_density(r) for r in r_values])
    
    # Trapezoidal integration
    return np.trapezoid(integrand, dx=dr)


def N_osc_full(
    E: float,
    primes_upto: int = 200,
    k_max: int = 6
) -> float:
    """
    Oscillatory counting correction N_osc_full(E).
    
    This is the full oscillatory correction to the zero counting function,
    distinct from N_osc_explicit in riemann_trace_formula.py (which uses
    von Mangoldt form with k=1 only).
    
    Mathematical Formula:
        N_osc_full(E) = -(1/π) Σ_{p,k} sin(k·E·ln p) / (k·p^{k/2})
    
    This is the antiderivative of d_osc(E) with respect to E.
    
    Args:
        E: Energy/height parameter
        primes_upto: Maximum prime to include (default: 200)
        k_max: Maximum power k (default: 6)
        
    Returns:
        Oscillatory correction N_osc_full(E)
    """
    primes = _sieve_primes(primes_upto)
    
    total_sum = 0.0
    
    for p in primes:
        ln_p = math.log(p)
        
        for k in range(1, k_max + 1):
            # sin(k·E·ln p) / (k·p^{k/2})
            term = math.sin(k * E * ln_p) / (k * p ** (k / 2.0))
            total_sum += term
    
    # Apply factor -(1/π)
    return -(1.0 / math.pi) * total_sum


def d_osc(
    E: float,
    primes_upto: int = 200,
    k_max: int = 6
) -> float:
    """
    Oscillatory density d_osc(E).
    
    This is the derivative of N_osc_full(E) with respect to E.
    
    Mathematical Formula:
        d_osc(E) = -(1/π) Σ_{p,k} (ln p / p^{k/2}) cos(k·E·ln p)
    
    Args:
        E: Energy/height parameter
        primes_upto: Maximum prime to include (default: 200)
        k_max: Maximum power k (default: 6)
        
    Returns:
        Oscillatory density d_osc(E)
    """
    primes = _sieve_primes(primes_upto)
    
    total_sum = 0.0
    
    for p in primes:
        ln_p = math.log(p)
        
        for k in range(1, k_max + 1):
            # (ln p / p^{k/2}) cos(k·E·ln p)
            term = (ln_p / p ** (k / 2.0)) * math.cos(k * E * ln_p)
            total_sum += term
    
    # Apply factor -(1/π)
    return -(1.0 / math.pi) * total_sum


def _sieve_primes(n: int) -> List[int]:
    """
    Generate list of primes up to n using Sieve of Eratosthenes.
    
    Args:
        n: Upper bound for primes
        
    Returns:
        List of all primes ≤ n
    """
    if n < 2:
        return []
    
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    
    for i in range(2, int(math.sqrt(n)) + 1):
        if sieve[i]:
            for j in range(i*i, n + 1, i):
                sieve[j] = False
    
    return [i for i in range(2, n + 1) if sieve[i]]


def N_smooth(E: float) -> float:
    """
    Smooth (Backlund) zero counting function.

    The smooth part of the Riemann zero counting function, which counts
    the expected number of non-trivial zeros with imaginary part in (0, E]:

        N_smooth(E) = (E / 2π) · ln(E / (2π·e)) + 7/8

    This follows from the argument-principle formula:
        N(T) = (T/2π)·ln(T/2π) - T/2π + O(ln T)
    combined with the Backlund correction term 7/8.

    The total counting function decomposes as:
        N_total(E) = N_smooth(E) + N_osc(E)

    where N_osc captures the oscillatory corrections from prime powers.

    Args:
        E: Height parameter (imaginary part of zero; must be > 0).

    Returns:
        Smooth counting function N_smooth(E).
    """
    if E <= 0:
        return 0.0
    return (E / (2.0 * math.pi)) * math.log(E / (2.0 * math.pi * math.e)) + 7.0 / 8.0


def rho_smooth(E: float) -> float:
    """
    Smooth (Weyl) density of zeros: ρ_smooth(E) = dN_smooth/dE.

    This is identical to the Weyl density μ(r) (see :func:`weyl_density`),
    but provided under the conventional name used in spectral analysis:

        ρ_smooth(E) = (1/2π) · ln(E / 2π)

    Args:
        E: Height parameter (must be > 0).

    Returns:
        Smooth density ρ_smooth(E) = (1/2π)·ln(E/2π).
    """
    return weyl_density(E)


@dataclass
class GUESpacingStats:
    """
    Level spacing statistics and GUE comparison for a set of zeros.

    Attributes:
        mean_spacing: Mean nearest-neighbor spacing ⟨s⟩.
        mean_sq_spacing: Mean squared spacing ⟨s²⟩.
        variance_spacing: Variance of spacings Var(s) = ⟨s²⟩ - ⟨s⟩².
        gue_mean: Theoretical GUE mean ⟨s⟩_GUE = 1 (normalized).
        gue_mean_sq: Theoretical GUE ⟨s²⟩_GUE = 3π/8 ≈ 1.178.
        ks_statistic: Kolmogorov-Smirnov statistic vs Wigner surmise CDF.
        ks_pvalue: KS-test p-value (high = close to GUE).
        n_zeros: Number of zeros used.
        E_min: Lower energy bound.
        E_max: Upper energy bound.
        normalised_spacings: Array of normalised nearest-neighbour spacings (unit mean).
    """
    mean_spacing: float
    mean_sq_spacing: float
    variance_spacing: float
    gue_mean: float
    gue_mean_sq: float
    ks_statistic: float
    ks_pvalue: float
    n_zeros: int
    E_min: float
    E_max: float
    normalised_spacings: np.ndarray = None


def gue_level_spacing_stats(
    zeros: List[float],
    E_min: float = 15.0,
    E_max: float = 45.0,
) -> GUESpacingStats:
    """
    Compute level spacing moments and KS-test vs theoretical GUE.

    Selects Riemann zeros in [E_min, E_max], unfolds them using the
    smooth Weyl density, computes nearest-neighbour spacings, and
    compares the distribution with the GUE Wigner surmise:

        P_GUE(s) = (32/π²) · s² · exp(-4s²/π)

    The theoretical GUE moments are:
        ⟨s⟩_GUE   = 1          (by construction of unfolding)
        ⟨s²⟩_GUE  = 3π/8 ≈ 1.178

    The KS-test uses the Wigner surmise CDF F_GUE(s) = 1 - exp(-4s²/π).

    Args:
        zeros: List of imaginary parts of Riemann zeta zeros.
        E_min: Lower energy cutoff (default: 15.0).
        E_max: Upper energy cutoff (default: 45.0).

    Returns:
        GUESpacingStats dataclass with moments and KS-test results.

    Raises:
        ValueError: If fewer than 3 zeros lie in [E_min, E_max].
    """
    # Select zeros in range
    selected = sorted(z for z in zeros if E_min <= z <= E_max)
    n = len(selected)
    if n < 3:
        raise ValueError(
            f"Need at least 3 zeros in [{E_min}, {E_max}]; found {n}."
        )

    # Unfold: map zeros to uniform density via N_smooth
    unfolded = [N_smooth(z) for z in selected]

    # Nearest-neighbour spacings
    spacings = np.diff(unfolded)

    # Normalise to unit mean
    mean_s = float(np.mean(spacings))
    if mean_s > 0:
        spacings = spacings / mean_s
    else:
        raise ValueError("Mean spacing is zero; cannot normalise.")

    mean_spacing = float(np.mean(spacings))
    mean_sq = float(np.mean(spacings ** 2))
    var_s = float(np.var(spacings))

    # Theoretical GUE values
    gue_mean = 1.0
    gue_mean_sq = 3.0 * math.pi / 8.0  # ≈ 1.178

    # KS-test vs Wigner surmise CDF  F_GUE(s) = 1 - exp(-4s²/π)
    def wigner_cdf(s: np.ndarray) -> np.ndarray:
        return 1.0 - np.exp(-4.0 * s ** 2 / math.pi)

    if HAS_SCIPY_STATS:
        ks_stat, ks_pval = _scipy_stats.kstest(spacings, wigner_cdf)
        ks_stat = float(ks_stat)
        ks_pval = float(ks_pval)
    else:
        # Manual KS statistic without scipy
        s_sorted = np.sort(spacings)
        ecdf = np.arange(1, len(s_sorted) + 1) / len(s_sorted)
        theoretical = wigner_cdf(s_sorted)
        ks_stat = float(np.max(np.abs(ecdf - theoretical)))
        ks_pval = float("nan")

    return GUESpacingStats(
        mean_spacing=mean_spacing,
        mean_sq_spacing=mean_sq,
        variance_spacing=var_s,
        gue_mean=gue_mean,
        gue_mean_sq=gue_mean_sq,
        ks_statistic=ks_stat,
        ks_pvalue=ks_pval,
        n_zeros=n,
        E_min=E_min,
        E_max=E_max,
        normalised_spacings=spacings,
    )


@dataclass
class WeilFormulaResult:
    """
    Result of Weil explicit formula computation.
    
    Attributes:
        zero_sum: LHS sum over zeros Σ_n Φ(t_n)
        weil_integral: Smooth integral ∫Φ(r)μ(r)dr
        prime_sum: Prime power sum contribution
        arithmetic_side: RHS = weil_integral + prime_sum
        discrepancy_abs: |LHS - RHS|
        discrepancy_rel: |LHS - RHS| / |LHS|
        coherencia_Psi: Ψ = exp(-discrepancy_rel) ≈ 1 for good agreement
        num_zeros: Number of zeros used
        primes_upto: Maximum prime used
        k_max: Maximum prime power
    """
    zero_sum: float
    weil_integral: float
    prime_sum: float
    arithmetic_side: float
    discrepancy_abs: float
    discrepancy_rel: float
    coherencia_Psi: float
    num_zeros: int
    primes_upto: int
    k_max: int


class WeilExplicitFormula:
    """
    End-to-end implementation of the Guinand-Weil explicit formula.
    
    This class provides complete verification of the identity:
        Σ_n Φ(t_n) = ∫Φ(r)μ(r)dr - Σ_{p,k} (ln p)/p^{k/2}[Φ̂(ln p^k) + Φ̂(-ln p^k)]
    
    It demonstrates the deep arithmetic-spectral correspondence between
    Riemann zeros and prime powers.
    
    Attributes:
        Phi: Test function Φ(r)
        Phi_hat_norm: Normalized Fourier transform Φ̂(ξ)
        primes_upto: Maximum prime to include
        k_max: Maximum prime power
        zeros: List of Riemann zero imaginary parts
    """
    
    def __init__(
        self,
        Phi: Callable[[float], float],
        Phi_hat_norm: Callable[[float], float],
        primes_upto: int = 200,
        k_max: int = 6,
        zeros: Optional[List[float]] = None
    ):
        """
        Initialize Weil explicit formula verifier.
        
        Args:
            Phi: Test function Φ(r)
            Phi_hat_norm: Normalized Fourier transform Φ̂(ξ)
            primes_upto: Maximum prime to include (default: 200)
            k_max: Maximum prime power (default: 6)
            zeros: List of zero imaginary parts (default: use ZEROS_ZETA_REFERENCE)
        """
        self.Phi = Phi
        self.Phi_hat_norm = Phi_hat_norm
        self.primes_upto = primes_upto
        self.k_max = k_max
        
        if zeros is None:
            self.zeros = ZEROS_ZETA_REFERENCE
        else:
            self.zeros = zeros
    
    def compute_zero_sum(self) -> float:
        """
        Compute LHS: sum over zeros Σ_n Φ(t_n).
        
        Returns:
            Sum of test function over Riemann zeros
        """
        return sum(self.Phi(t_n) for t_n in self.zeros)
    
    def compute_weil_integral(
        self,
        r_min: float = 1.0,
        r_max: float = 100.0,
        num_points: int = 1000
    ) -> float:
        """
        Compute smooth integral ∫Φ(r)μ(r)dr.
        
        Args:
            r_min: Lower integration limit (default: 1.0)
            r_max: Upper integration limit (default: 100.0)
            num_points: Number of quadrature points (default: 1000)
            
        Returns:
            Weyl integral contribution
        """
        return weil_smooth_integral(self.Phi, r_min, r_max, num_points)
    
    def compute_prime_sum(self) -> float:
        """
        Compute prime power sum contribution.
        
        Returns:
            Prime power sum
        """
        return prime_power_sum(self.Phi_hat_norm, self.primes_upto, self.k_max)
    
    def discrepancy(
        self,
        r_min: float = 1.0,
        r_max: float = 100.0,
        num_points: int = 1000
    ) -> WeilFormulaResult:
        """
        Compute discrepancy between LHS and RHS of Weil formula.
        
        Args:
            r_min: Lower integration limit (default: 1.0)
            r_max: Upper integration limit (default: 100.0)
            num_points: Number of quadrature points (default: 1000)
            
        Returns:
            WeilFormulaResult with full computation details
        """
        # LHS: sum over zeros
        zero_sum = self.compute_zero_sum()
        
        # RHS components
        weil_integral = self.compute_weil_integral(r_min, r_max, num_points)
        prime_sum = self.compute_prime_sum()
        
        # Total arithmetic side
        arithmetic_side = weil_integral + prime_sum
        
        # Discrepancy
        disc_abs = abs(zero_sum - arithmetic_side)
        disc_rel = disc_abs / abs(zero_sum) if abs(zero_sum) > 1e-10 else float('inf')
        
        # Coherence measure: Ψ = exp(-disc_rel)
        coherencia_Psi = math.exp(-disc_rel) if disc_rel < 100 else 0.0
        
        return WeilFormulaResult(
            zero_sum=zero_sum,
            weil_integral=weil_integral,
            prime_sum=prime_sum,
            arithmetic_side=arithmetic_side,
            discrepancy_abs=disc_abs,
            discrepancy_rel=disc_rel,
            coherencia_Psi=coherencia_Psi,
            num_zeros=len(self.zeros),
            primes_upto=self.primes_upto,
            k_max=self.k_max
        )


def demonstrate_weil_formula(verbose: bool = True) -> Dict:
    """
    Demonstrate the Guinand-Weil explicit formula.
    
    This runs a complete verification using a Gaussian test function
    centered at the first Riemann zero.
    
    Args:
        verbose: If True, print detailed results
        
    Returns:
        Dictionary with demonstration results
    """
    # Test function: Gaussian centered at first zero
    T_center = ZEROS_ZETA_REFERENCE[0]
    sigma = 3.0
    
    def Phi(r):
        return math.exp(-0.5 * ((r - T_center) / sigma) ** 2)
    
    def Phi_hat_norm(xi):
        return fourier_gaussian_norm(xi, sigma=sigma, center=T_center)
    
    # Initialize Weil formula computer
    wf = WeilExplicitFormula(
        Phi=Phi,
        Phi_hat_norm=Phi_hat_norm,
        primes_upto=200,
        k_max=6
    )
    
    # Compute discrepancy
    result = wf.discrepancy()
    
    if verbose:
        print("=" * 80)
        print("GUINAND-WEIL EXPLICIT FORMULA DEMONSTRATION")
        print("=" * 80)
        print(f"\nTest function: Gaussian centered at T = {T_center:.4f}, σ = {sigma}")
        print(f"Number of zeros: {result.num_zeros}")
        print(f"Primes up to: {result.primes_upto}")
        print(f"Max prime power k: {result.k_max}")
        print()
        print("FORMULA COMPONENTS:")
        print(f"  LHS (zero sum):        {result.zero_sum:.8f}")
        print(f"  Weyl integral:         {result.weil_integral:.8f}")
        print(f"  Prime sum:             {result.prime_sum:.8f}")
        print(f"  RHS (arithmetic side): {result.arithmetic_side:.8f}")
        print()
        print("DISCREPANCY ANALYSIS:")
        print(f"  Absolute discrepancy:  {result.discrepancy_abs:.8e}")
        print(f"  Relative discrepancy:  {result.discrepancy_rel:.8e}")
        print(f"  Coherencia Ψ:          {result.coherencia_Psi:.8f}")
        print()
        
        if result.coherencia_Psi > 0.999:
            print("✅ EXCELLENT AGREEMENT — Formula verified with Ψ ≈ 0.9999")
        elif result.coherencia_Psi > 0.99:
            print("✅ GOOD AGREEMENT — Formula verified with Ψ > 0.99")
        elif result.coherencia_Psi > 0.95:
            print("⚠️  ACCEPTABLE AGREEMENT — Formula verified with Ψ > 0.95")
        else:
            print("❌ POOR AGREEMENT — Check parameters or implementation")
        
        print("=" * 80)
        print(f"\nFrequency: f₀ = {F0_QCAL} Hz")
        print(f"Coherence: C = {C_COHERENCE}")
        print("=" * 80)
    
    return {
        'result': result,
        'T_center': T_center,
        'sigma': sigma,
        'weil_formula': wf
    }


if __name__ == "__main__":
    # Run demonstration
    demo_result = demonstrate_weil_formula(verbose=True)
    
    print("\n" + "∴" * 40)
    print("QCAL ∞³ Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz")
    print("∴" * 40)
