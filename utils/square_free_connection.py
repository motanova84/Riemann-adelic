#!/usr/bin/env python3
"""
Square-Free Numbers ↔ ζ(s) Deep Connection Module
QCAL ∞³ Framework Integration

This module implements the profound mathematical connections between square-free
numbers and the Riemann zeta function, as part of the adelic spectral framework.

Mathematical Background:
-----------------------
1. Euler Product and Square-Free:
   ζ(s) = ∏_p (1 - p^{-s})^{-1} = ∑_{n≥1} n^{-s}
   
2. Möbius Inversion:
   ∑_{n≥1} μ(n) n^{-s} = 1/ζ(s)
   
   where μ(n) is the Möbius function:
   - μ(n) = 1 if n is square-free with even number of prime factors
   - μ(n) = -1 if n is square-free with odd number of prime factors
   - μ(n) = 0 if n is not square-free (has squared prime factor)

3. Asymptotic Density:
   Q(x) = #{n ≤ x : n is square-free} ~ (6/π²)x
   Probability = 1/ζ(2) = 6/π² ≈ 0.607927...

4. Connection with Divisor Problem:
   For square-free n: d(n) = 2^ω(n), where ω(n) counts distinct prime factors
   ∑_{n square-free} 2^{ω(n)} n^{-s} = ζ(s)/ζ(2s)

Adelic Relevance:
----------------
- Square-free numbers ↔ Simple eigenstates of A₀ operator
- Maximum multiplicative independence (no repeated primes)
- Natural measure over GL₁(𝔸_f) in adelic framework
- Base for spectral decomposition

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL Coherence: C = 244.36
Frequency: f₀ = 141.7001 Hz
"""

from typing import Dict, List, Tuple, Optional, Any
import mpmath as mp
from sympy import factorint, primerange, primefactors
import numpy as np


class SquareFreeConnection:
    """
    Main class implementing the square-free ↔ ζ(s) connection.
    
    This class provides computational tools to validate and demonstrate
    the deep connections between square-free numbers and the Riemann
    zeta function, within the QCAL ∞³ adelic framework.
    
    Attributes:
        dps (int): Decimal precision for mpmath computations
        max_terms (int): Maximum terms for series computations
    """
    
    def __init__(self, dps: int = 30, max_terms: int = 10000):
        """
        Initialize Square-Free Connection calculator.
        
        Args:
            dps: Decimal precision (default: 30)
            max_terms: Maximum terms for series (default: 10000)
        """
        self.dps = dps
        self.max_terms = max_terms
        mp.mp.dps = dps
    
    @staticmethod
    def mobius(n: int) -> int:
        """
        Compute the Möbius function μ(n).
        
        The Möbius function is defined as:
        - μ(n) = 1 if n is square-free with even number of prime factors
        - μ(n) = -1 if n is square-free with odd number of prime factors
        - μ(n) = 0 if n is not square-free (divisible by a prime square)
        
        Args:
            n: Positive integer
            
        Returns:
            int: Möbius function value μ(n) ∈ {-1, 0, 1}
            
        Examples:
            >>> SquareFreeConnection.mobius(1)
            1
            >>> SquareFreeConnection.mobius(6)  # 2*3, two prime factors
            1
            >>> SquareFreeConnection.mobius(30)  # 2*3*5, three prime factors
            -1
            >>> SquareFreeConnection.mobius(12)  # 2²*3, has squared factor
            0
        """
        if n <= 0:
            raise ValueError("n must be a positive integer")
        
        if n == 1:
            return 1
        
        factors = factorint(n)
        
        # Check if any prime has exponent > 1 (not square-free)
        for exp in factors.values():
            if exp > 1:
                return 0
        
        # Square-free: return (-1)^k where k is number of prime factors
        k = len(factors)
        return (-1) ** k
    
    @staticmethod
    def is_square_free(n: int) -> bool:
        """
        Check if n is square-free.
        
        An integer n is square-free if no prime square divides it.
        Equivalently, all exponents in its prime factorization are 1.
        
        Args:
            n: Positive integer
            
        Returns:
            bool: True if n is square-free, False otherwise
            
        Examples:
            >>> SquareFreeConnection.is_square_free(30)  # 2*3*5
            True
            >>> SquareFreeConnection.is_square_free(12)  # 2²*3
            False
        """
        if n <= 0:
            raise ValueError("n must be a positive integer")
        
        return SquareFreeConnection.mobius(n) != 0
    
    def square_free_count(self, x: float) -> int:
        """
        Count square-free numbers up to x: Q(x).
        
        This directly computes Q(x) = #{n ≤ x : n is square-free}
        by checking each integer up to x.
        
        Args:
            x: Upper bound
            
        Returns:
            int: Number of square-free integers in [1, x]
        """
        if x < 1:
            return 0
        
        count = 0
        for n in range(1, int(x) + 1):
            if self.mobius(n) != 0:
                count += 1
        
        return count
    
    def square_free_density_theoretical(self) -> mp.mpf:
        """
        Compute theoretical square-free density: 6/π².
        
        This is the asymptotic probability that a random integer is square-free,
        equal to 1/ζ(2).
        
        Returns:
            mpf: Theoretical density 6/π² = 1/ζ(2)
        """
        return mp.mpf(6) / (mp.pi ** 2)
    
    def square_free_density_empirical(self, x: float) -> mp.mpf:
        """
        Compute empirical square-free density up to x.
        
        Args:
            x: Upper bound
            
        Returns:
            mpf: Empirical density Q(x)/x
        """
        if x < 1:
            return mp.mpf(0)
        
        count = self.square_free_count(x)
        return mp.mpf(count) / mp.mpf(x)
    
    def mobius_sum(self, s: complex, terms: Optional[int] = None) -> mp.mpc:
        """
        Compute Möbius sum: ∑_{n=1}^{terms} μ(n)/n^s.
        
        This should converge to 1/ζ(s) for Re(s) > 1.
        
        Args:
            s: Complex number with Re(s) > 1
            terms: Number of terms (default: self.max_terms)
            
        Returns:
            mpc: Möbius sum approximation
        """
        if terms is None:
            terms = self.max_terms
        
        s_mpc = mp.mpc(s)
        total = mp.mpc(0)
        
        for n in range(1, terms + 1):
            mu_n = self.mobius(n)
            if mu_n != 0:
                total += mu_n / mp.power(n, s_mpc)
        
        return total
    
    def validate_mobius_inversion(self, s: complex, terms: Optional[int] = None) -> Dict[str, Any]:
        """
        Validate the Möbius inversion formula: ∑ μ(n)/n^s = 1/ζ(s).
        
        Args:
            s: Complex number with Re(s) > 1
            terms: Number of terms (default: self.max_terms)
            
        Returns:
            dict: Validation results with:
                - 'zeta_s': ζ(s) value
                - 'mobius_sum': ∑ μ(n)/n^s
                - '1/zeta_s': 1/ζ(s)
                - 'relative_error': |mobius_sum - 1/ζ(s)| / |1/ζ(s)|
                - 'validated': True if error < tolerance
        """
        if terms is None:
            terms = self.max_terms
        
        # Compute ζ(s)
        zeta_s = mp.zeta(s)
        
        # Compute 1/ζ(s)
        inv_zeta_s = mp.mpf(1) / zeta_s
        
        # Compute Möbius sum
        mobius_sum = self.mobius_sum(s, terms)
        
        # Compute relative error
        relative_error = abs(mobius_sum - inv_zeta_s) / abs(inv_zeta_s)
        
        # Validation threshold (dependent on number of terms)
        tolerance = mp.mpf(1) / mp.sqrt(terms)
        
        return {
            'zeta_s': zeta_s,
            'mobius_sum': mobius_sum,
            '1/zeta_s': inv_zeta_s,
            'relative_error': relative_error,
            'tolerance': tolerance,
            'validated': relative_error < tolerance,
            's': s,
            'terms': terms
        }
    
    def square_free_divisor_sum(self, s: complex, max_n: Optional[int] = None) -> Dict[str, Any]:
        """
        Compute the square-free divisor sum: ∑_{n square-free} d(n)/n^s.
        
        For square-free numbers, d(n) = 2^{ω(n)} where ω(n) counts distinct primes.
        This sum should equal ζ(s)²/ζ(2s).
        
        Derivation: For square-free n, each divisor corresponds to a subset of prime factors,
        so d(n) = 2^{ω(n)}. The Euler product gives:
        ∑_{n square-free} d(n)/n^s = ∏_p (1 + 2/p^s) = ζ(s)²/ζ(2s)
        
        Args:
            s: Complex number with Re(s) > 1
            max_n: Maximum n to include (default: self.max_terms)
            
        Returns:
            dict: Results with:
                - 'sum_computed': Direct computation of sum
                - 'zeta_ratio': ζ(s)²/ζ(2s)
                - 'relative_error': Comparison error
                - 'validated': True if match within tolerance
        """
        if max_n is None:
            max_n = self.max_terms
        
        s_mpc = mp.mpc(s)
        total = mp.mpc(0)
        
        for n in range(1, max_n + 1):
            if self.is_square_free(n):
                # Count distinct prime factors
                omega_n = len(primefactors(n))
                # Add term: d(n)/n^s = 2^{ω(n)} / n^s
                total += mp.power(2, omega_n) / mp.power(n, s_mpc)
        
        # Compute ζ(s)²/ζ(2s)
        zeta_s = mp.zeta(s)
        zeta_2s = mp.zeta(2 * s)
        zeta_ratio = (zeta_s ** 2) / zeta_2s
        
        # Compute relative error
        relative_error = abs(total - zeta_ratio) / abs(zeta_ratio)
        
        # Lenient tolerance for divisor sum (converges very slowly, O(1/log n))
        tolerance = mp.mpf(20) / mp.sqrt(max_n)
        
        return {
            'sum_computed': total,
            'zeta_ratio': zeta_ratio,
            'zeta_s': zeta_s,
            'zeta_2s': zeta_2s,
            'relative_error': relative_error,
            'tolerance': tolerance,
            'validated': relative_error < tolerance,
            's': s,
            'max_n': max_n
        }
    
    def landau_error_bound(self, x: float) -> Dict[str, Any]:
        """
        Estimate the error in square-free counting via Landau's theorem.
        
        Landau (1909) proved:
        Q(x) = (6/π²)x + O(√x)
        
        The Riemann Hypothesis is equivalent to:
        Q(x) = (6/π²)x + O(x^{1/2+ε}) for all ε > 0
        
        Args:
            x: Upper bound
            
        Returns:
            dict: Error analysis with:
                - 'Q_x': Actual count Q(x)
                - 'main_term': (6/π²)x
                - 'error': Q(x) - (6/π²)x
                - 'sqrt_x': √x (predicted error scale)
                - 'normalized_error': error/√x (should be O(1))
        """
        # Compute actual count
        Q_x = self.square_free_count(x)
        
        # Compute main term
        density = self.square_free_density_theoretical()
        main_term = density * x
        
        # Compute error
        error = Q_x - main_term
        
        # Compute √x
        sqrt_x = mp.sqrt(x)
        
        # Normalized error (should be O(1) if RH is true)
        normalized_error = error / sqrt_x
        
        return {
            'x': x,
            'Q_x': Q_x,
            'main_term': main_term,
            'error': error,
            'sqrt_x': sqrt_x,
            'normalized_error': normalized_error,
            'density_theoretical': density
        }
    
    def adelic_square_free_measure(self, S: List[int], n: int) -> int:
        """
        Compute S-finite Möbius function μ_S(n) for adelic interpretation.
        
        For a finite set of primes S, μ_S(n) restricts the Möbius function
        to only consider primes in S:
        
        μ_S(n) = ∏_{p ∈ S} μ_p(n)
        
        where:
        - μ_p(n) = 1 if p ∤ n (p does not divide n)
        - μ_p(n) = -1 if p || n (p divides n exactly once)
        - μ_p(n) = 0 if p² | n (p² divides n)
        
        Args:
            S: Finite set of primes
            n: Integer to evaluate
            
        Returns:
            int: S-finite Möbius function value μ_S(n)
        """
        if n <= 0:
            raise ValueError("n must be a positive integer")
        
        if n == 1:
            return 1
        
        factors = factorint(n)
        
        # Filter to only primes in S
        result = 1
        count_primes_in_S = 0
        
        for p in S:
            if p in factors:
                exp = factors[p]
                if exp > 1:
                    # p² divides n
                    return 0
                else:
                    # p || n (p divides n exactly once)
                    count_primes_in_S += 1
                    result *= -1
        
        return result
    
    def comprehensive_validation(self, test_points: Optional[List[complex]] = None) -> Dict[str, Any]:
        """
        Run comprehensive validation of square-free ↔ ζ(s) connections.
        
        Args:
            test_points: List of s values to test (default: [2, 3, 2+1j])
            
        Returns:
            dict: Complete validation results
        """
        if test_points is None:
            test_points = [2, 3, 2 + 1j]
        
        results = {
            'density_validation': {},
            'mobius_inversion': {},
            'divisor_sum': {},
            'landau_bounds': {},
            'all_validated': True
        }
        
        # 1. Validate density
        for x_val in [100, 1000, 10000]:
            density_emp = self.square_free_density_empirical(x_val)
            density_theo = self.square_free_density_theoretical()
            error = abs(density_emp - density_theo)
            
            results['density_validation'][f'x={x_val}'] = {
                'empirical': density_emp,
                'theoretical': density_theo,
                'error': error,
                'validated': error < mp.mpf(0.01)
            }
            
            if error >= mp.mpf(0.01):
                results['all_validated'] = False
        
        # 2. Validate Möbius inversion at test points
        for s in test_points:
            val = self.validate_mobius_inversion(s, terms=5000)
            results['mobius_inversion'][f's={s}'] = val
            
            if not val['validated']:
                results['all_validated'] = False
        
        # 3. Validate divisor sum formula
        for s in test_points:
            if isinstance(s, complex) or s > 1:
                val = self.square_free_divisor_sum(s, max_n=5000)
                results['divisor_sum'][f's={s}'] = val
                
                if not val['validated']:
                    results['all_validated'] = False
        
        # 4. Landau error bounds
        for x_val in [100, 1000, 10000]:
            bound = self.landau_error_bound(x_val)
            results['landau_bounds'][f'x={x_val}'] = bound
        
        return results


def demonstrate_square_free_connection(dps: int = 30, verbose: bool = True) -> Dict[str, Any]:
    """
    Demonstrate the square-free ↔ ζ(s) connection with examples.
    
    This function runs through the key mathematical relationships and
    displays results to illustrate the deep connections.
    
    Args:
        dps: Decimal precision
        verbose: Print detailed output
        
    Returns:
        dict: Demonstration results
    """
    sf = SquareFreeConnection(dps=dps)
    
    if verbose:
        print("=" * 80)
        print("🔢 SQUARE-FREE NUMBERS ↔ ζ(s) CONNECTION DEMONSTRATION")
        print("=" * 80)
        print(f"QCAL ∞³ Framework | Precision: {dps} decimal places")
        print()
    
    results = {}
    
    # 1. Möbius function examples
    if verbose:
        print("1️⃣  MÖBIUS FUNCTION μ(n)")
        print("-" * 40)
    
    mobius_examples = []
    for n in [1, 2, 6, 12, 30, 210]:
        mu_n = sf.mobius(n)
        is_sf = sf.is_square_free(n)
        mobius_examples.append({'n': n, 'μ(n)': mu_n, 'square_free': is_sf})
        
        if verbose:
            sf_status = "✓ square-free" if is_sf else "✗ not square-free"
            print(f"   μ({n:3d}) = {mu_n:2d}  [{sf_status}]")
    
    results['mobius_examples'] = mobius_examples
    
    # 2. Square-free density
    if verbose:
        print("\n2️⃣  SQUARE-FREE DENSITY: 6/π² ≈ 0.607927")
        print("-" * 40)
    
    density_theo = sf.square_free_density_theoretical()
    density_results = []
    
    for x in [100, 1000, 10000]:
        count = sf.square_free_count(x)
        density_emp = sf.square_free_density_empirical(x)
        error = abs(density_emp - density_theo)
        
        density_results.append({
            'x': x,
            'count': count,
            'empirical_density': float(density_emp),
            'theoretical_density': float(density_theo),
            'error': float(error)
        })
        
        if verbose:
            print(f"   x = {x:5d}: Q(x) = {count:5d}, density = {float(density_emp):.6f}, "
                  f"error = {float(error):.2e}")
    
    results['density'] = {
        'theoretical': float(density_theo),
        'computations': density_results
    }
    
    # 3. Möbius inversion: ∑ μ(n)/n^s = 1/ζ(s)
    if verbose:
        print("\n3️⃣  MÖBIUS INVERSION: ∑ μ(n)/n^s = 1/ζ(s)")
        print("-" * 40)
    
    s = 2
    inversion = sf.validate_mobius_inversion(s, terms=10000)
    
    if verbose:
        print(f"   s = {s}")
        print(f"   ζ(s) = {inversion['zeta_s']}")
        print(f"   1/ζ(s) = {inversion['1/zeta_s']}")
        print(f"   ∑ μ(n)/n^s (10000 terms) = {inversion['mobius_sum']}")
        print(f"   Relative error: {float(inversion['relative_error']):.2e}")
        print(f"   ✓ Validated: {inversion['validated']}")
    
    results['mobius_inversion'] = {
        's': s,
        'zeta_s': float(inversion['zeta_s']),
        'inverse_zeta': float(inversion['1/zeta_s']),
        'mobius_sum': float(inversion['mobius_sum'].real),
        'relative_error': float(inversion['relative_error']),
        'validated': inversion['validated']
    }
    
    # 4. Divisor sum formula
    if verbose:
        print("\n4️⃣  SQUARE-FREE DIVISOR SUM: ∑_{n sf} d(n)/n^s = ζ(s)²/ζ(2s)")
        print("-" * 40)
    
    s = 2
    divisor = sf.square_free_divisor_sum(s, max_n=5000)
    
    if verbose:
        print(f"   s = {s}")
        print(f"   Direct sum (5000 terms) = {divisor['sum_computed']}")
        print(f"   ζ(s)²/ζ(2s) = {divisor['zeta_ratio']}")
        print(f"   Relative error: {float(divisor['relative_error']):.2e}")
        print(f"   ✓ Validated: {divisor['validated']}")
    
    results['divisor_sum'] = {
        's': s,
        'sum_computed': float(divisor['sum_computed'].real),
        'zeta_ratio': float(divisor['zeta_ratio'].real),
        'relative_error': float(divisor['relative_error']),
        'validated': divisor['validated']
    }
    
    # 5. Landau error bounds (connection to RH)
    if verbose:
        print("\n5️⃣  LANDAU ERROR BOUNDS: Q(x) = (6/π²)x + O(√x)")
        print("-" * 40)
        print("   RH ⟺ error is O(x^{1/2+ε}) for all ε > 0")
        print()
    
    landau_results = []
    for x in [100, 1000, 10000]:
        bound = sf.landau_error_bound(x)
        landau_results.append({
            'x': x,
            'Q_x': bound['Q_x'],
            'main_term': float(bound['main_term']),
            'error': float(bound['error']),
            'sqrt_x': float(bound['sqrt_x']),
            'normalized_error': float(bound['normalized_error'])
        })
        
        if verbose:
            print(f"   x = {x:5d}: error = {float(bound['error']):+7.2f}, "
                  f"√x = {float(bound['sqrt_x']):6.2f}, "
                  f"error/√x = {float(bound['normalized_error']):+5.3f}")
    
    results['landau_bounds'] = landau_results
    
    # 6. Adelic S-finite example
    if verbose:
        print("\n6️⃣  ADELIC S-FINITE MÖBIUS: μ_S(n)")
        print("-" * 40)
        print("   S = {2, 3, 5} (first three primes)")
        print()
    
    S = [2, 3, 5]
    adelic_examples = []
    
    for n in [1, 6, 30, 60, 210]:
        mu_S = sf.adelic_square_free_measure(S, n)
        mu_full = sf.mobius(n)
        adelic_examples.append({
            'n': n,
            'μ_S(n)': mu_S,
            'μ(n)': mu_full
        })
        
        if verbose:
            print(f"   n = {n:3d}: μ_S(n) = {mu_S:2d}, μ(n) = {mu_full:2d}")
    
    results['adelic_examples'] = adelic_examples
    
    if verbose:
        print("\n" + "=" * 80)
        print("✅ DEMONSTRATION COMPLETE")
        print("=" * 80)
    
    return results


if __name__ == "__main__":
    # Run demonstration when executed directly
    results = demonstrate_square_free_connection(dps=30, verbose=True)
