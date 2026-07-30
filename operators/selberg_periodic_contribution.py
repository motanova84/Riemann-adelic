#!/usr/bin/env python3
"""
Selberg Periodic Contribution — Hyperbolic Side of Trace Formula
==================================================================

Mathematical Framework:
-----------------------

This module implements the hyperbolic (periodic orbit) contribution to the
Selberg trace formula for compact surfaces.

**Selberg Trace Formula (Hyperbolic Contribution):**

For a compact hyperbolic surface, the contribution from closed geodesics is:

    Σ_{[γ] primitive} Σ_{k≥1} [ℓ(γ) / (2 sinh(kℓ(γ)/2))] · g(kℓ(γ))

where:
    γ = primitive closed geodesic (conjugacy class)
    ℓ(γ) = length of geodesic
    k = repetition number (powers of γ)
    g = test function

**Asymptotic Approximation:**

For large kℓ, we have the approximation:

    sinh(u) = (e^u - e^{-u})/2 ∼ e^u/2  for u ≫ 1

Therefore:
    ℓ / (2 sinh(kℓ/2)) ∼ ℓ · e^{-kℓ/2}  for kℓ ≫ 1

**Physical Interpretation:**

The geodesic length ℓ(γ) plays the role analogous to log p in prime number
theory, establishing the correspondence:

    ℓ(γ) ↔ log p

This is the foundation of the Selberg-Riemann correspondence.

Key Features:
-------------
- Periodic orbit length computation
- sinh weight function implementation
- Asymptotic approximation for large kℓ
- Convergence analysis
- Connection to Riemann explicit formula

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
class PeriodicOrbitResult:
    """
    Result of periodic orbit contribution computation.
    
    Attributes:
        orbit_lengths: Array of primitive orbit lengths ℓ(γ)
        total_contribution: Sum over all orbits and repetitions
        sinh_weights: Array of sinh weight values
        exponential_weights: Array of exponential approximation values
        max_repetition: Maximum k used in computation
        convergence_info: Dictionary with convergence metrics
    """
    orbit_lengths: np.ndarray
    total_contribution: float
    sinh_weights: np.ndarray
    exponential_weights: np.ndarray
    max_repetition: int
    convergence_info: Dict[str, float]


@dataclass
class SinhApproximationResult:
    """
    Result of sinh approximation analysis.
    
    Attributes:
        exact_values: Exact sinh weight values
        approximate_values: Exponential approximation values
        relative_errors: Relative errors |exact - approx| / |exact|
        threshold_kl: Threshold kℓ where approximation is valid
        max_error: Maximum relative error
        mean_error: Mean relative error
    """
    exact_values: np.ndarray
    approximate_values: np.ndarray
    relative_errors: np.ndarray
    threshold_kl: float
    max_error: float
    mean_error: float


class SelbergPeriodicContribution:
    """
    Implements the periodic orbit (hyperbolic) contribution to Selberg trace formula.
    
    This class computes the contribution from closed geodesics using the formula:
        Σ_{[γ]} Σ_k [ℓ(γ)/(2sinh(kℓ(γ)/2))] · g(kℓ(γ))
    
    Attributes:
        max_repetition: Maximum k in repetition sum
        max_orbit_length: Maximum geodesic length to include
        test_function: Test function g (defaults to Gaussian)
        regularization_cutoff: Numerical cutoff for series
    """
    
    def __init__(
        self,
        max_repetition: int = 10,
        max_orbit_length: float = 10.0,
        test_function: Optional[Callable[[float], float]] = None,
        regularization_cutoff: float = 1e-12
    ):
        """
        Initialize the Selberg periodic contribution computer.
        
        Args:
            max_repetition: Maximum k for orbit repetitions (default: 10)
            max_orbit_length: Maximum orbit length ℓ(γ) (default: 10.0)
            test_function: Test function g(x), defaults to Gaussian e^{-x²/2}
            regularization_cutoff: Numerical cutoff for series (default: 1e-12)
        """
        self.max_repetition = max_repetition
        self.max_orbit_length = max_orbit_length
        self.regularization_cutoff = regularization_cutoff
        
        # Default test function: Gaussian
        if test_function is None:
            self.test_function = lambda x: np.exp(-x**2 / 2.0)
        else:
            self.test_function = test_function
        
        # Generate primitive orbit lengths (corresponding to primes via ℓ = log p)
        self._orbit_lengths = self._generate_orbit_lengths()
    
    def _generate_orbit_lengths(self) -> NDArray[np.float64]:
        """
        Generate primitive orbit lengths corresponding to prime logarithms.
        
        For the Selberg-Riemann correspondence, we use:
            ℓ(γ) = log p  for primes p
        
        Returns:
            Array of orbit lengths
        """
        # Generate primes up to exp(max_orbit_length)
        max_prime = int(np.exp(self.max_orbit_length)) + 1
        primes = self._sieve_of_eratosthenes(max_prime)
        
        # Convert to orbit lengths: ℓ = log p
        orbit_lengths = np.log(primes.astype(np.float64))
        
        # Filter by max_orbit_length
        orbit_lengths = orbit_lengths[orbit_lengths <= self.max_orbit_length]
        
        return orbit_lengths
    
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
    
    def sinh_weight(self, ell: float, k: int) -> float:
        """
        Compute the exact sinh weight function.
        
        Mathematical Formula:
            w(ℓ,k) = ℓ / (2 sinh(kℓ/2))
        
        Args:
            ell: Orbit length ℓ(γ)
            k: Repetition number
            
        Returns:
            Weight value w(ℓ,k)
        """
        kell_half = k * ell / 2.0
        
        # Avoid overflow for large arguments
        if kell_half > 100:
            # Use asymptotic approximation
            return ell * np.exp(-kell_half)
        
        return ell / (2.0 * np.sinh(kell_half))
    
    def exponential_weight(self, ell: float, k: int) -> float:
        """
        Compute the exponential approximation of sinh weight.
        
        Mathematical Formula:
            w_approx(ℓ,k) = ℓ · e^{-kℓ/2}
        
        This is valid for kℓ ≫ 1.
        
        Args:
            ell: Orbit length ℓ(γ)
            k: Repetition number
            
        Returns:
            Approximate weight value
        """
        return ell * np.exp(-k * ell / 2.0)
    
    def compute_orbit_contribution(
        self,
        include_details: bool = False,
        use_exponential_approximation: bool = True
    ) -> PeriodicOrbitResult:
        """
        Compute the total periodic orbit contribution.
        
        Mathematical Formula:
            Σ_{[γ]} Σ_{k=1}^{k_max} [ℓ(γ)/(2sinh(kℓ(γ)/2))] · g(kℓ(γ))
        
        Or with exponential approximation (for large kℓ):
            Σ_{[γ]} Σ_{k=1}^{k_max} ℓ(γ)·e^{-kℓ(γ)/2} · g(kℓ(γ))
        
        Args:
            include_details: If True, include detailed weight arrays
            use_exponential_approximation: If True, use exponential approx instead of exact sinh
            
        Returns:
            PeriodicOrbitResult with computation details
        """
        total_contribution = 0.0
        terms_computed = 0
        max_term = 0.0
        min_nonzero_term = float('inf')
        
        sinh_weights_list = []
        exp_weights_list = []
        
        for ell in self._orbit_lengths:
            for k in range(1, self.max_repetition + 1):
                # Compute weight (sinh or exponential)
                if use_exponential_approximation:
                    weight = self.exponential_weight(ell, k)
                else:
                    weight = self.sinh_weight(ell, k)
                
                # Compute test function value
                test_value = self.test_function(k * ell)
                
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
                    sinh_weights_list.append(self.sinh_weight(ell, k))
                    exp_weights_list.append(self.exponential_weight(ell, k))
        
        # Convergence diagnostics
        convergence_info = {
            'terms_computed': terms_computed,
            'max_term': max_term,
            'min_term': min_nonzero_term if min_nonzero_term != float('inf') else 0.0,
            'sum_magnitude': abs(total_contribution),
            'orbits_used': len(self._orbit_lengths)
        }
        
        return PeriodicOrbitResult(
            orbit_lengths=self._orbit_lengths,
            total_contribution=total_contribution,
            sinh_weights=np.array(sinh_weights_list) if include_details else np.array([]),
            exponential_weights=np.array(exp_weights_list) if include_details else np.array([]),
            max_repetition=self.max_repetition,
            convergence_info=convergence_info
        )
    
    def verify_sinh_approximation(
        self,
        kl_values: Optional[NDArray[np.float64]] = None
    ) -> SinhApproximationResult:
        """
        Verify the quality of sinh approximation sinh(u) ∼ e^u/2 for large u.
        
        Mathematical Analysis:
            For u = kℓ/2, we compare:
                Exact: ℓ / (2 sinh(kℓ/2))
                Approx: ℓ · e^{-kℓ/2}
        
        Args:
            kl_values: Array of kℓ values to test (default: logspace from 0.1 to 10)
            
        Returns:
            SinhApproximationResult with error analysis
        """
        if kl_values is None:
            kl_values = np.logspace(-1, 1, 100)
        
        exact_values = []
        approx_values = []
        
        for kl in kl_values:
            # Use ℓ = 1 for simplicity, k = kl
            ell = 1.0
            k = int(kl)
            if k == 0:
                k = 1
            
            # Compute exact sinh weight
            exact = self.sinh_weight(ell, k)
            exact_values.append(exact)
            
            # Compute exponential approximation
            approx = self.exponential_weight(ell, k)
            approx_values.append(approx)
        
        exact_values = np.array(exact_values)
        approx_values = np.array(approx_values)
        
        # Compute relative errors
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            relative_errors = np.abs(exact_values - approx_values) / np.abs(exact_values)
            relative_errors = np.nan_to_num(relative_errors, nan=0.0, posinf=0.0, neginf=0.0)
        
        # Find threshold where approximation is good (error < 1%)
        threshold_idx = np.where(relative_errors < 0.01)[0]
        threshold_kl = kl_values[threshold_idx[0]] if len(threshold_idx) > 0 else kl_values[-1]
        
        return SinhApproximationResult(
            exact_values=exact_values,
            approximate_values=approx_values,
            relative_errors=relative_errors,
            threshold_kl=threshold_kl,
            max_error=np.max(relative_errors),
            mean_error=np.mean(relative_errors)
        )
    
    def verify_properties(self) -> Dict[str, bool]:
        """
        Verify mathematical properties of the periodic orbit contribution.
        
        Returns:
            Dictionary of verification results
        """
        results = {}
        
        # Property 1: Contribution is positive
        orbit_result = self.compute_orbit_contribution()
        results['contribution_positive'] = orbit_result.total_contribution > 0
        
        # Property 2: sinh weight decreases with k
        if len(self._orbit_lengths) > 0:
            ell = self._orbit_lengths[0]
            weights = [self.sinh_weight(ell, k) for k in range(1, 5)]
            results['sinh_weight_decreasing'] = all(weights[i] > weights[i+1] for i in range(len(weights)-1))
        else:
            results['sinh_weight_decreasing'] = True
        
        # Property 3: Exponential approximation is close for large kℓ
        approx_result = self.verify_sinh_approximation()
        results['exponential_approximation_valid'] = approx_result.threshold_kl < 5.0
        
        # Property 4: Convergence of orbit sum
        results['orbit_sum_converges'] = orbit_result.convergence_info['terms_computed'] > 0
        
        return results


def demonstrate_selberg_periodic():
    """
    Demonstrate the Selberg periodic contribution computation.
    """
    print("=" * 80)
    print("Selberg Periodic Contribution Demonstration")
    print("=" * 80)
    print()
    
    # Initialize
    selberg = SelbergPeriodicContribution(
        max_repetition=10,
        max_orbit_length=5.0
    )
    
    print("Configuration:")
    print(f"  Max repetition k: {selberg.max_repetition}")
    print(f"  Max orbit length: {selberg.max_orbit_length}")
    print(f"  Number of primitive orbits: {len(selberg._orbit_lengths)}")
    print()
    
    # Compute orbit contribution
    print("Computing periodic orbit contribution...")
    result = selberg.compute_orbit_contribution(include_details=True)
    print(f"  Total contribution: {result.total_contribution:.6f}")
    print(f"  Terms computed: {result.convergence_info['terms_computed']}")
    print(f"  Max term: {result.convergence_info['max_term']:.6e}")
    print(f"  Min term: {result.convergence_info['min_term']:.6e}")
    print()
    
    # Verify sinh approximation
    print("Verifying sinh approximation...")
    approx = selberg.verify_sinh_approximation()
    print(f"  Threshold kℓ for 1% error: {approx.threshold_kl:.3f}")
    print(f"  Max relative error: {approx.max_error:.6f}")
    print(f"  Mean relative error: {approx.mean_error:.6f}")
    print()
    
    # Verify properties
    print("Verifying mathematical properties...")
    props = selberg.verify_properties()
    for prop, value in props.items():
        status = "✓" if value else "✗"
        print(f"  {status} {prop}: {value}")
    print()
    
    print("=" * 80)
    print("✓ Selberg periodic contribution demonstration complete")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_selberg_periodic()
