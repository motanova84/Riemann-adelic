#!/usr/bin/env python3
"""
Explicit Formula for Riemann Zeta Zeros
========================================

Mathematical Framework:
-----------------------

This module implements the explicit formula relating the sum over non-trivial 
zeros of the Riemann zeta function to an integral and a sum over prime powers:

    ∑_n Φ(t_n) = ∫ Φ(r) μ(r) dr - ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]

where:
- t_n are the imaginary parts of non-trivial zeros: ζ(1/2 + it_n) = 0
- Φ(t) is a smooth test function with rapid decay
- Φ̂(ξ) is the Fourier transform: Φ̂(ξ) = ∫ Φ(t) e^{iξt} dt
- μ(r) is a smooth density function on ℝ
- p ranges over primes, k over positive integers

**1. Sum Over Zeros**

The left-hand side sums the test function over all imaginary parts of 
non-trivial zeros on the critical line Re(s) = 1/2:

    LHS = ∑_{ρ: ζ(ρ)=0} Φ(Im(ρ))

**2. Integral Term**

The first term on the right-hand side is a smooth integral over ℝ with a 
weight function μ(r):

    I(Φ) = ∫_{-∞}^{∞} Φ(r) μ(r) dr

For typical choices, μ(r) involves logarithmic and polynomial factors 
derived from the functional equation of ζ(s).

**3. Prime Power Sum**

The second term sums over prime powers with the Jacobian factor p^{k/2} 
coming from the adelic scale structure:

    P(Φ) = ∑_{p prime} ∑_{k≥1} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]

The Fourier transform Φ̂ appears naturally from the Mellin transform 
relationship and the functional equation.

**4. Fourier Transform**

The Fourier transform is defined as:

    Φ̂(ξ) = ∫_{-∞}^{∞} Φ(t) e^{iξt} dt

For real symmetric functions Φ(t) = Φ(-t), we have:

    Φ̂(ξ) = ∫_{-∞}^{∞} Φ(t) cos(ξt) dt  (real-valued)

**5. Exact Identity and Rigor**

This formula is EXACT for appropriate test functions Φ in the Schwartz 
class S(ℝ). The convergence is:

- The zero sum converges by the growth estimate N(T) ~ (T/2π) ln(T/2πe)
- The prime sum converges exponentially due to the p^{k/2} denominator
- The integral converges by the rapid decay of Φ

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import numpy as np
from typing import Dict, Tuple, Optional, List, Callable
from numpy.typing import NDArray
from scipy.integrate import quad, simpson
from scipy.special import zeta as scipy_zeta
from dataclasses import dataclass
import warnings

try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath not available, using scipy fallbacks")

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz - fundamental frequency
C_PRIMARY = 629.83           # Primary spectral constant
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ
KAPPA_PI = 2.5773            # Critical curvature


@dataclass
class ExplicitFormulaResult:
    """
    Result of explicit formula computation.
    
    Attributes:
        zero_sum: Sum over non-trivial zeros ∑_n Φ(t_n)
        integral_term: Integral ∫ Φ(r) μ(r) dr
        prime_sum: Sum over prime powers with Fourier transform
        total_lhs: Left-hand side (zero sum)
        total_rhs: Right-hand side (integral - prime_sum)
        residual: |LHS - RHS| (should be small for valid formula)
        relative_error: Relative error |LHS - RHS| / max(|LHS|, |RHS|)
        num_zeros: Number of zeros used
        num_primes: Number of primes used
        max_prime_power: Maximum k in prime powers
    """
    zero_sum: float
    integral_term: float
    prime_sum: float
    total_lhs: float
    total_rhs: float
    residual: float
    relative_error: float
    num_zeros: int
    num_primes: int
    max_prime_power: int


class ExplicitFormula:
    """
    Implements the explicit formula for Riemann zeta zeros.
    
    This class provides methods to compute each term of the formula:
        ∑_n Φ(t_n) = ∫ Φ(r) μ(r) dr - ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
    
    Attributes:
        max_prime: Maximum prime p to include in summation
        max_prime_power: Maximum k in prime powers p^k
        integral_limit: Integration limit for ∫_{-L}^{L}
        use_mpmath: Whether to use mpmath for high precision
        precision: Decimal precision for mpmath (if used)
    """
    
    def __init__(
        self,
        max_prime: int = 1000,
        max_prime_power: int = 10,
        integral_limit: float = 50.0,
        use_mpmath: bool = False,
        precision: int = 30
    ):
        """
        Initialize the explicit formula computer.
        
        Args:
            max_prime: Maximum prime p to include (default: 1000)
            max_prime_power: Maximum k for p^k (default: 10)
            integral_limit: Integration limit |r| ≤ L (default: 50.0)
            use_mpmath: Use mpmath for high precision (default: False)
            precision: Decimal precision if using mpmath (default: 30)
        """
        self.max_prime = max_prime
        self.max_prime_power = max_prime_power
        self.integral_limit = integral_limit
        self.use_mpmath = use_mpmath and HAS_MPMATH
        self.precision = precision
        
        if self.use_mpmath:
            mp.mp.dps = precision
        
        # Precompute primes
        self._primes = self._sieve_of_eratosthenes(max_prime)
    
    def _sieve_of_eratosthenes(self, n: int) -> NDArray[np.int64]:
        """
        Compute all primes up to n using Sieve of Eratosthenes.
        
        Args:
            n: Upper bound for primes
            
        Returns:
            Array of all primes ≤ n
        """
        if n < 2:
            return np.array([], dtype=np.int64)
        
        sieve = np.ones(n + 1, dtype=bool)
        sieve[0:2] = False
        
        for i in range(2, int(np.sqrt(n)) + 1):
            if sieve[i]:
                sieve[i*i::i] = False
        
        return np.where(sieve)[0]
    
    def fourier_transform(
        self,
        phi: Callable[[float], float],
        xi: float,
        limit: Optional[float] = None
    ) -> float:
        """
        Compute the Fourier transform Φ̂(ξ) = ∫ Φ(t) e^{iξt} dt.
        
        For real symmetric functions, this simplifies to:
            Φ̂(ξ) = ∫ Φ(t) cos(ξt) dt
        
        Args:
            phi: Test function Φ(t)
            xi: Frequency parameter ξ
            limit: Integration limit (default: self.integral_limit)
            
        Returns:
            Fourier transform value Φ̂(ξ)
        """
        if limit is None:
            limit = self.integral_limit
        
        if self.use_mpmath:
            # High-precision computation with mpmath
            def integrand(t):
                return phi(float(t)) * mp.cos(mp.mpf(xi) * mp.mpf(t))
            
            result = mp.quad(integrand, [-limit, limit], maxdegree=15)
            return float(result)
        else:
            # Standard precision with scipy
            def integrand(t):
                return phi(t) * np.cos(xi * t)
            
            result, _ = quad(integrand, -limit, limit, limit=100)
            return result
    
    def compute_zero_sum(
        self,
        phi: Callable[[float], float],
        zeros: List[float]
    ) -> float:
        """
        Compute the sum over non-trivial zeros: ∑_n Φ(t_n).
        
        Args:
            phi: Test function Φ(t)
            zeros: List of imaginary parts t_n of zeros
            
        Returns:
            Sum ∑_n Φ(t_n)
        """
        if not zeros:
            return 0.0
        
        if self.use_mpmath:
            total = mp.mpf(0)
            for t in zeros:
                total += mp.mpf(phi(float(t)))
            return float(total)
        else:
            return sum(phi(t) for t in zeros)
    
    def compute_integral_term(
        self,
        phi: Callable[[float], float],
        mu: Optional[Callable[[float], float]] = None,
        limit: Optional[float] = None
    ) -> float:
        """
        Compute the integral term: ∫ Φ(r) μ(r) dr.
        
        Args:
            phi: Test function Φ(r)
            mu: Weight function μ(r) (default: constant 1)
            limit: Integration limit (default: self.integral_limit)
            
        Returns:
            Integral value
        """
        if limit is None:
            limit = self.integral_limit
        
        if mu is None:
            # Default: uniform weight
            mu = lambda r: 1.0
        
        if self.use_mpmath:
            def integrand(r):
                return phi(float(r)) * mu(float(r))
            
            result = mp.quad(integrand, [-limit, limit], maxdegree=15)
            return float(result)
        else:
            def integrand(r):
                return phi(r) * mu(r)
            
            result, _ = quad(integrand, -limit, limit, limit=100)
            return result
    
    def compute_prime_sum(
        self,
        phi: Callable[[float], float],
        fourier_cache: Optional[Dict[float, float]] = None
    ) -> Tuple[float, Dict[float, float]]:
        """
        Compute the prime power sum:
            ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]
        
        Args:
            phi: Test function Φ(t)
            fourier_cache: Optional cache for Fourier transform values
            
        Returns:
            Tuple of (prime_sum, fourier_cache)
        """
        if fourier_cache is None:
            fourier_cache = {}
        
        if self.use_mpmath:
            total = mp.mpf(0)
            
            for p in self._primes:
                log_p = mp.log(mp.mpf(int(p)))
                
                for k in range(1, self.max_prime_power + 1):
                    # Jacobian denominator
                    jacobian = mp.power(mp.mpf(int(p)), mp.mpf(k) / 2)
                    
                    # Compute ln(p^k)
                    log_pk = k * log_p
                    log_pk_val = float(log_pk)
                    
                    # Get Fourier transforms (with caching)
                    if log_pk_val not in fourier_cache:
                        fourier_cache[log_pk_val] = self.fourier_transform(phi, log_pk_val)
                    
                    if -log_pk_val not in fourier_cache:
                        fourier_cache[-log_pk_val] = self.fourier_transform(phi, -log_pk_val)
                    
                    phi_hat_pos = mp.mpf(fourier_cache[log_pk_val])
                    phi_hat_neg = mp.mpf(fourier_cache[-log_pk_val])
                    
                    # Add contribution
                    contribution = (log_p / jacobian) * (phi_hat_pos + phi_hat_neg)
                    total += contribution
            
            return float(total), fourier_cache
        else:
            total = 0.0
            
            for p in self._primes:
                log_p = np.log(p)
                
                for k in range(1, self.max_prime_power + 1):
                    # Jacobian denominator
                    jacobian = np.power(p, k / 2.0)
                    
                    # Compute ln(p^k)
                    log_pk = k * log_p
                    
                    # Get Fourier transforms (with caching)
                    if log_pk not in fourier_cache:
                        fourier_cache[log_pk] = self.fourier_transform(phi, log_pk)
                    
                    if -log_pk not in fourier_cache:
                        fourier_cache[-log_pk] = self.fourier_transform(phi, -log_pk)
                    
                    phi_hat_pos = fourier_cache[log_pk]
                    phi_hat_neg = fourier_cache[-log_pk]
                    
                    # Add contribution
                    contribution = (log_p / jacobian) * (phi_hat_pos + phi_hat_neg)
                    total += contribution
            
            return total, fourier_cache
    
    def validate_formula(
        self,
        phi: Callable[[float], float],
        zeros: List[float],
        mu: Optional[Callable[[float], float]] = None
    ) -> ExplicitFormulaResult:
        """
        Validate the explicit formula by computing both sides and comparing.
        
        Args:
            phi: Test function Φ(t)
            zeros: List of imaginary parts of non-trivial zeros
            mu: Optional weight function μ(r) for integral term
            
        Returns:
            ExplicitFormulaResult with all computed terms
        """
        # Compute left-hand side: ∑_n Φ(t_n)
        zero_sum = self.compute_zero_sum(phi, zeros)
        
        # Compute right-hand side terms
        integral_term = self.compute_integral_term(phi, mu)
        prime_sum, _ = self.compute_prime_sum(phi)
        
        # Assemble both sides
        total_lhs = zero_sum
        total_rhs = integral_term - prime_sum
        
        # Compute residual and relative error
        residual = abs(total_lhs - total_rhs)
        max_val = max(abs(total_lhs), abs(total_rhs))
        relative_error = residual / max_val if max_val > 1e-10 else residual
        
        return ExplicitFormulaResult(
            zero_sum=zero_sum,
            integral_term=integral_term,
            prime_sum=prime_sum,
            total_lhs=total_lhs,
            total_rhs=total_rhs,
            residual=residual,
            relative_error=relative_error,
            num_zeros=len(zeros),
            num_primes=len(self._primes),
            max_prime_power=self.max_prime_power
        )


# Test functions for validation
def gaussian_test_function(t: float, sigma: float = 1.0) -> float:
    """
    Gaussian test function: Φ(t) = exp(-t²/(2σ²))
    
    This is in the Schwartz class and has Fourier transform:
        Φ̂(ξ) = σ√(2π) exp(-σ²ξ²/2)
    """
    return np.exp(-t**2 / (2 * sigma**2))


def truncated_gaussian(t: float, a: float = 5.0, sigma: float = 1.0) -> float:
    """
    Truncated Gaussian: Φ(t) = exp(-t²/(2σ²)) for |t| ≤ a, else 0.
    
    This has compact support, making numerical computations more efficient.
    """
    if abs(t) > a:
        return 0.0
    return np.exp(-t**2 / (2 * sigma**2))


def smooth_bump_function(t: float, a: float = 3.0) -> float:
    """
    Smooth bump function with compact support [-a, a].
    
    This is C^∞ with compact support (in Schwartz class).
    """
    if abs(t) >= a:
        return 0.0
    
    x = t / a
    if abs(x) >= 0.999:
        return 0.0
    
    try:
        denominator = 1 - x**2
        if denominator <= 1e-15:
            return 0.0
        return np.exp(-1 / denominator)
    except (ZeroDivisionError, OverflowError):
        return 0.0


def compute_qcal_coherence(result: ExplicitFormulaResult) -> float:
    """
    Compute QCAL coherence Ψ from explicit formula validation.
    
    The coherence is defined as:
        Ψ = 1 - relative_error
    
    Perfect coherence (Ψ = 1) means the explicit formula holds exactly.
    
    Args:
        result: ExplicitFormulaResult from validation
        
    Returns:
        Coherence value Ψ ∈ [0, 1]
    """
    coherence = 1.0 - result.relative_error
    return max(0.0, min(1.0, coherence))
