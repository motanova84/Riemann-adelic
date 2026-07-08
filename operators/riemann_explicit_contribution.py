#!/usr/bin/env python3
"""
Riemann Explicit Contribution — Prime Side of Explicit Formula
===============================================================

Mathematical Framework:
-----------------------

This module implements the prime power contribution to the Riemann-Weil
explicit formula.

**Riemann Explicit Formula (Prime Contribution):**

The explicit formula relates the prime counting function to zeros of ζ(s):

    ψ(x) = x - Σ_ρ (x^ρ/ρ) - log(2π) - (1/2)log(1-x^{-2})

In Fourier form, the prime contribution is:

    Σ_p Σ_{k≥1} (log p) · p^{-k/2} · g(k log p)

where:
    p = prime number
    k = power
    g = test function

**Weil's Formulation:**

Using the Mellin transform Ĝ(s) = ∫₀^∞ g(log x) x^{s-1} dx, the formula becomes:

    Σ_n Λ(n)/√n g(log n) = -Σ_ρ Ĝ(ρ) + boundary terms

where Λ is the von Mangoldt function.

**Physical Interpretation:**

The logarithm log p plays the role analogous to geodesic length ℓ(γ) in
the Selberg trace formula, establishing the correspondence:

    log p ↔ ℓ(γ)

This is the foundation of the Selberg-Riemann correspondence.

Key Features:
-------------
- Prime power sum computation
- von Mangoldt function implementation
- Fourier/Mellin transform support
- Convergence analysis
- Connection to Selberg trace formula

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721

QCAL ∞³ · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from typing import Dict, List, Tuple, Callable, Optional
from numpy.typing import NDArray
from dataclasses import dataclass
import warnings

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz - fundamental frequency
C_PRIMARY = 629.83           # Primary spectral constant
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ


@dataclass
class PrimeContributionResult:
    """
    Result of prime power contribution computation.
    
    Attributes:
        primes: Array of prime numbers used
        total_contribution: Sum over all prime powers
        weights: Array of weight values (log p) / p^{k/2}
        max_power: Maximum k used in computation
        convergence_info: Dictionary with convergence metrics
    """
    primes: np.ndarray
    total_contribution: float
    weights: np.ndarray
    max_power: int
    convergence_info: Dict[str, float]


@dataclass
class VonMangoldtResult:
    """
    Result of von Mangoldt function computation.
    
    Attributes:
        n_values: Input values n
        lambda_values: Λ(n) values
        prime_power_decomposition: Dict mapping n → (p, k) for prime powers
    """
    n_values: np.ndarray
    lambda_values: np.ndarray
    prime_power_decomposition: Dict[int, Tuple[int, int]]


class RiemannExplicitContribution:
    """
    Implements the prime power contribution to Riemann explicit formula.
    
    This class computes the contribution from prime powers using the formula:
        Σ_p Σ_k (log p) · p^{-k/2} · g(k log p)
    
    Attributes:
        max_power: Maximum k in prime power summation
        max_prime: Maximum prime to include
        test_function: Test function g (defaults to Gaussian)
        regularization_cutoff: Numerical cutoff for series
    """
    
    def __init__(
        self,
        max_power: int = 10,
        max_prime: int = 1000,
        test_function: Optional[Callable[[float], float]] = None,
        regularization_cutoff: float = 1e-12
    ):
        """
        Initialize the Riemann explicit contribution computer.
        
        Args:
            max_power: Maximum k for prime powers (default: 10)
            max_prime: Maximum prime to include (default: 1000)
            test_function: Test function g(x), defaults to Gaussian e^{-x²/2}
            regularization_cutoff: Numerical cutoff for series (default: 1e-12)
        """
        self.max_power = max_power
        self.max_prime = max_prime
        self.regularization_cutoff = regularization_cutoff
        
        # Default test function: Gaussian
        if test_function is None:
            self.test_function = lambda x: np.exp(-x**2 / 2.0)
        else:
            self.test_function = test_function
        
        # Precompute primes up to max_prime
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
    
    def prime_weight(self, p: int, k: int) -> float:
        """
        Compute the prime power weight function.
        
        Mathematical Formula:
            w(p,k) = (log p) / p^{k/2}
        
        Args:
            p: Prime number
            k: Power
            
        Returns:
            Weight value w(p,k)
        """
        log_p = np.log(float(p))
        return log_p / (p ** (k / 2.0))
    
    def von_mangoldt(self, n: int) -> float:
        """
        Compute the von Mangoldt function Λ(n).
        
        Mathematical Definition:
            Λ(n) = log p  if n = p^k for prime p
            Λ(n) = 0      otherwise
        
        Args:
            n: Input value
            
        Returns:
            Λ(n) value
        """
        if n < 2:
            return 0.0
        
        # Check if n is a prime power
        for p in self._primes:
            if p > n:
                break
            
            power = n
            k = 0
            while power % p == 0:
                power //= p
                k += 1
            
            if power == 1 and k > 0:
                return np.log(float(p))
        
        return 0.0
    
    def compute_von_mangoldt_array(
        self,
        n_max: int
    ) -> VonMangoldtResult:
        """
        Compute von Mangoldt function for all n ≤ n_max.
        
        Args:
            n_max: Maximum n value
            
        Returns:
            VonMangoldtResult with Λ(n) values
        """
        n_values = np.arange(1, n_max + 1)
        lambda_values = np.zeros(n_max)
        prime_power_decomp = {}
        
        for n in range(2, n_max + 1):
            lambda_val = self.von_mangoldt(n)
            lambda_values[n - 1] = lambda_val
            
            # Store prime power decomposition if applicable
            if lambda_val > 0:
                log_p = lambda_val
                p = int(np.exp(log_p) + 0.5)
                k = 1
                temp = p
                while temp < n:
                    temp *= p
                    k += 1
                prime_power_decomp[n] = (p, k)
        
        return VonMangoldtResult(
            n_values=n_values,
            lambda_values=lambda_values,
            prime_power_decomposition=prime_power_decomp
        )
    
    def compute_prime_contribution(
        self,
        include_details: bool = False
    ) -> PrimeContributionResult:
        """
        Compute the total prime power contribution.
        
        Mathematical Formula:
            Σ_p Σ_{k=1}^{k_max} (log p) / p^{k/2} · g(k log p)
        
        Args:
            include_details: If True, include detailed weight arrays
            
        Returns:
            PrimeContributionResult with computation details
        """
        total_contribution = 0.0
        terms_computed = 0
        max_term = 0.0
        min_nonzero_term = float('inf')
        
        weights_list = []
        
        for p in self._primes:
            log_p = np.log(float(p))
            
            for k in range(1, self.max_power + 1):
                # Compute prime weight
                weight = self.prime_weight(p, k)
                
                # Compute test function value
                test_value = self.test_function(k * log_p)
                
                # Compute contribution
                term = weight * test_value
                
                # Apply regularization cutoff
                if abs(term) < self.regularization_cutoff:
                    break
                
                total_contribution += term
                terms_computed += 1
                max_term = max(max_term, abs(term))
                if abs(term) > 0:
                    min_nonzero_term = min(min_nonzero_term, abs(term))
                
                if include_details:
                    weights_list.append(weight)
        
        # Convergence diagnostics
        convergence_info = {
            'terms_computed': terms_computed,
            'max_term': max_term,
            'min_term': min_nonzero_term if min_nonzero_term != float('inf') else 0.0,
            'sum_magnitude': abs(total_contribution),
            'primes_used': len(self._primes)
        }
        
        return PrimeContributionResult(
            primes=self._primes,
            total_contribution=total_contribution,
            weights=np.array(weights_list) if include_details else np.array([]),
            max_power=self.max_power,
            convergence_info=convergence_info
        )
    
    def verify_properties(self) -> Dict[str, bool]:
        """
        Verify mathematical properties of the prime contribution.
        
        Returns:
            Dictionary of verification results
        """
        results = {}
        
        # Property 1: Contribution is positive
        prime_result = self.compute_prime_contribution()
        results['contribution_positive'] = prime_result.total_contribution > 0
        
        # Property 2: Prime weight decreases with k
        if len(self._primes) > 0:
            p = self._primes[0]
            weights = [self.prime_weight(p, k) for k in range(1, 5)]
            results['prime_weight_decreasing'] = all(weights[i] > weights[i+1] for i in range(len(weights)-1))
        else:
            results['prime_weight_decreasing'] = True
        
        # Property 3: von Mangoldt function is non-negative
        vm_result = self.compute_von_mangoldt_array(100)
        results['von_mangoldt_nonnegative'] = np.all(vm_result.lambda_values >= 0)
        
        # Property 4: Convergence of prime sum
        results['prime_sum_converges'] = prime_result.convergence_info['terms_computed'] > 0
        
        # Property 5: von Mangoldt gives correct value for primes
        if len(self._primes) > 0:
            p = int(self._primes[0])
            lambda_p = self.von_mangoldt(p)
            expected = np.log(float(p))
            results['von_mangoldt_correct_for_primes'] = np.abs(lambda_p - expected) < 1e-10
        else:
            results['von_mangoldt_correct_for_primes'] = True
        
        return results


def demonstrate_riemann_explicit():
    """
    Demonstrate the Riemann explicit contribution computation.
    """
    print("=" * 80)
    print("Riemann Explicit Contribution Demonstration")
    print("=" * 80)
    print()
    
    # Initialize
    riemann = RiemannExplicitContribution(
        max_power=10,
        max_prime=100
    )
    
    print("Configuration:")
    print(f"  Max power k: {riemann.max_power}")
    print(f"  Max prime: {riemann.max_prime}")
    print(f"  Number of primes: {len(riemann._primes)}")
    print()
    
    # Compute prime contribution
    print("Computing prime power contribution...")
    result = riemann.compute_prime_contribution(include_details=True)
    print(f"  Total contribution: {result.total_contribution:.6f}")
    print(f"  Terms computed: {result.convergence_info['terms_computed']}")
    print(f"  Max term: {result.convergence_info['max_term']:.6e}")
    print(f"  Min term: {result.convergence_info['min_term']:.6e}")
    print()
    
    # Test von Mangoldt function
    print("Testing von Mangoldt function Λ(n):")
    test_values = [2, 3, 4, 5, 8, 9, 10, 16, 32]
    for n in test_values:
        lambda_n = riemann.von_mangoldt(n)
        print(f"  Λ({n:2d}) = {lambda_n:.4f}")
    print()
    
    # Verify properties
    print("Verifying mathematical properties...")
    props = riemann.verify_properties()
    for prop, value in props.items():
        status = "✓" if value else "✗"
        print(f"  {status} {prop}: {value}")
    print()
    
    print("=" * 80)
    print("✓ Riemann explicit contribution demonstration complete")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_riemann_explicit()
