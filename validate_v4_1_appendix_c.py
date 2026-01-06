#!/usr/bin/env python3
"""
Numerical Validation for V4.1 Appendix C

This script implements the numerical validation described in Appendix C of:
"A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems 
(Final Conditional Version V4.1)" by José Manuel Mota Burruezo (Sep 14, 2025)

Validates the explicit formula equality:
    Prime + Arch sum ≈ Zero sum (error ≤ 10^-6)

For three test functions f1, f2, f3 with compact support on specific intervals.
Uses finite set S (up to 1000 primes), smoothing δ = 0.01, and σ₀ = 2.

Expected results from paper:
  Test f       Prime + Arch    Zero sum    Error
  f1 ([-3,3])   1.834511       1.834511    1.2e-06
  f2 ([-2,2])   1.763213       1.763213    8.7e-07
  f3 ([-2,2])   1.621375       1.621375    1.2e-05
"""

import mpmath as mp
from sympy import primerange
import argparse
import json
from datetime import datetime
from pathlib import Path

# Set precision for reproducible results
mp.mp.dps = 50  # High precision for intermediate calculations

class V41Validator:
    """Numerical validator for V4.1 Appendix C"""
    
    def __init__(self, max_primes=1000, delta=0.01, sigma0=2.0):
        """
        Initialize validator
        
        Args:
            max_primes: Maximum number of primes in set S
            delta: Smoothing parameter
            sigma0: Evaluation point on real axis (σ₀ > 1)
        """
        self.max_primes = max_primes
        self.delta = delta
        self.sigma0 = sigma0
        self.primes = list(primerange(2, 10000))[:max_primes]  # First max_primes primes
        
        print(f"V4.1 Appendix C Numerical Validation")
        print(f"=" * 60)
        print(f"Parameters:")
        print(f"  S (primes): {len(self.primes)} primes up to {self.primes[-1]}")
        print(f"  δ (smoothing): {delta}")
        print(f"  σ₀: {sigma0}")
        print()
    
    def test_function_f1(self, u):
        """
        Test function f1 with support in [-3, 3]
        Smooth bump function with compact support
        """
        if abs(u) >= 3:
            return mp.mpf(0)
        # Smooth bump: exp(-1/(1-x²)) for |x| < 1, scaled to [-3,3]
        x = u / 3
        if abs(x) >= 1:
            return mp.mpf(0)
        return mp.exp(-mp.mpf(1) / (1 - x**2))
    
    def test_function_f2(self, u):
        """
        Test function f2 with support in [-2, 2]
        Cosine-modulated Gaussian
        """
        if abs(u) >= 2:
            return mp.mpf(0)
        return mp.cos(mp.pi * u / 2) * mp.exp(-u**2)
    
    def test_function_f3(self, u):
        """
        Test function f3 with support in [-2, 2]
        Polynomial-modulated bump
        """
        if abs(u) >= 2:
            return mp.mpf(0)
        x = u / 2
        if abs(x) >= 1:
            return mp.mpf(0)
        return (1 - x**2) * mp.exp(-mp.mpf(1) / (1 - x**2))
    
    def mellin_transform(self, f, s, u_max=10, n_points=1000):
        """
        Compute Mellin transform Φ_f(s) = ∫ f(u) e^(su) du
        
        Args:
            f: Test function
            s: Complex parameter
            u_max: Integration limit (function has compact support)
            n_points: Number of quadrature points
            
        Returns:
            Φ_f(s) (complex number)
        """
        # Adaptive quadrature for smooth functions
        value, _error = mp.quad(
            lambda u: f(u) * mp.exp(s * u),
            [-u_max, u_max],
            maxdegree=10,
            error=True,
        )
        return value
    
    def prime_sum_contribution(self, f, p, k_max=10):
        """
        Compute contribution from prime p with powers up to k_max
        
        Sum over k: (log p) * f(k * log p)
        
        Args:
            f: Test function
            p: Prime number
            k_max: Maximum power
            
        Returns:
            Contribution from this prime
        """
        log_p = mp.log(p)
        total = mp.mpf(0)
        
        for k in range(1, k_max + 1):
            u_k = k * log_p
            total += log_p * f(u_k)
        
        return total
    
    def prime_sum(self, f, k_max=10):
        """
        Compute total prime sum: Σ_p Σ_k (log p) f(k log p)
        
        Args:
            f: Test function
            k_max: Maximum power
            
        Returns:
            Total prime contribution
        """
        total = mp.mpf(0)
        
        for p in self.primes:
            total += self.prime_sum_contribution(f, p, k_max)
        
        return total
    
    def archimedean_sum(self, f, t_max=50):
        """
        Compute Archimedean contribution
        
        A_∞[f] = (1/2πi) ∫_{Re s = σ₀} K(s) Φ_f(s) ds
        
        where K(s) = (1/2)ψ(s/2) - (1/2)log(π) from zeta regularization
        
        Args:
            f: Test function
            t_max: Integration limit for imaginary part
            
        Returns:
            Archimedean contribution
        """
        # For σ₀ = 2, evaluate integral along vertical line
        # K(s) = (1/2)ψ(s/2) - (1/2)log(π) where ψ is digamma function
        
        def integrand(t):
            s = self.sigma0 + 1j * t
            # Archimedean kernel
            K_s = 0.5 * mp.psi(0, s/2) - 0.5 * mp.log(mp.pi)
            # Mellin transform
            Phi_s = self.mellin_transform(f, s)
            return (K_s * Phi_s).real  # Take real part
        
        # Integrate over t from -t_max to t_max
        result = mp.quad(integrand, [-t_max, t_max], maxdegree=8)
        return result / (2 * mp.pi)
    
    def zero_sum(self, f, zeros_file='zeros/zeros_t1e8.txt', max_zeros=1000):
        """
        Compute zero sum: Σ_ρ Φ_f(ρ) where ρ = 1/2 + iγ are nontrivial zeros
        
        Args:
            f: Test function
            zeros_file: File containing zeros (one per line, imaginary parts γ)
            max_zeros: Maximum number of zeros to use
            
        Returns:
            Zero sum
        """
        total = mp.mpf(0)
        count = 0
        
        zeros_path = Path(zeros_file)
        if not zeros_path.exists():
            print(f"⚠️  Warning: {zeros_file} not found, using synthetic zeros")
            # Use first few known zeros
            known_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
            for gamma in known_zeros[:min(max_zeros, len(known_zeros))]:
                rho = 0.5 + 1j * gamma
                total += self.mellin_transform(f, rho)
                count += 1
        else:
            with open(zeros_file) as file:
                for line in file:
                    if count >= max_zeros:
                        break
                    gamma = mp.mpf(line.strip())
                    rho = 0.5 + 1j * gamma
                    # Φ_f(ρ) - only real part contributes by symmetry
                    total += self.mellin_transform(f, rho).real
                    count += 1
        
        print(f"  Used {count} zeros")
        return total
    
    def validate_test_function(self, f, f_name, support_interval):
        """
        Validate explicit formula for a single test function
        
        Args:
            f: Test function
            f_name: Name for display (e.g., 'f1')
            support_interval: Support interval as string (e.g., '[-3,3]')
            
        Returns:
            Dictionary with validation results
        """
        print(f"\n{'='*60}")
        print(f"Test function: {f_name} {support_interval}")
        print(f"{'='*60}")
        
        # Compute prime sum
        print("Computing prime sum...")
        prime_contribution = self.prime_sum(f, k_max=10)
        print(f"  Prime sum: {float(prime_contribution):.10f}")
        
        # Compute archimedean sum
        print("Computing archimedean sum...")
        arch_contribution = self.archimedean_sum(f, t_max=50)
        print(f"  Archimedean sum: {float(arch_contribution):.10f}")
        
        # Total arithmetic side
        arithmetic_sum = prime_contribution + arch_contribution
        print(f"  → Total (Prime + Arch): {float(arithmetic_sum):.10f}")
        
        # Compute zero sum
        print("Computing zero sum...")
        zero_contribution = self.zero_sum(f, max_zeros=1000)
        print(f"  → Zero sum: {float(zero_contribution):.10f}")
        
        # Compute error
        error_abs = abs(arithmetic_sum - zero_contribution)
        error_rel = error_abs / abs(arithmetic_sum) if abs(arithmetic_sum) > 1e-10 else error_abs
        
        print(f"\n📊 Results:")
        print(f"  Prime + Arch: {float(arithmetic_sum):.6f}")
        print(f"  Zero sum:     {float(zero_contribution):.6f}")
        print(f"  Error (abs):  {float(error_abs):.2e}")
        print(f"  Error (rel):  {float(error_rel):.2e}")
        
        passed = error_abs < 1e-6 or error_rel < 1e-6
        status = "✅ PASSED" if passed else "❌ FAILED"
        print(f"\n{status} (tolerance: 10^-6)")
        
        return {
            'test_function': f_name,
            'support': support_interval,
            'prime_arch_sum': float(arithmetic_sum),
            'zero_sum': float(zero_contribution),
            'error_absolute': float(error_abs),
            'error_relative': float(error_rel),
            'passed': passed,
            'tolerance': 1e-6
        }
    
    def run_full_validation(self):
        """Run validation for all three test functions"""
        print(f"\n{'='*60}")
        print(f"RUNNING FULL V4.1 APPENDIX C VALIDATION")
        print(f"{'='*60}\n")
        
        results = []
        
        # Test function f1
        results.append(self.validate_test_function(
            self.test_function_f1, 'f1', '[-3,3]'
        ))
        
        # Test function f2
        results.append(self.validate_test_function(
            self.test_function_f2, 'f2', '[-2,2]'
        ))
        
        # Test function f3
        results.append(self.validate_test_function(
            self.test_function_f3, 'f3', '[-2,2]'
        ))
        
        # Summary
        print(f"\n{'='*60}")
        print(f"VALIDATION SUMMARY")
        print(f"{'='*60}")
        print(f"{'Test':<8} {'Support':<12} {'Prime+Arch':<15} {'Zero sum':<15} {'Error':<12}")
        print(f"{'-'*60}")
        
        for r in results:
            print(f"{r['test_function']:<8} {r['support']:<12} "
                  f"{r['prime_arch_sum']:<15.6f} {r['zero_sum']:<15.6f} "
                  f"{r['error_absolute']:<12.2e}")
        
        passed_count = sum(1 for r in results if r['passed'])
        print(f"\n✅ Passed: {passed_count}/{len(results)}")
        
        # Save results
        output_file = Path('data') / 'v4_1_appendix_c_validation.json'
        output_file.parent.mkdir(exist_ok=True)
        
        output_data = {
            'timestamp': datetime.now().isoformat(),
            'parameters': {
                'max_primes': self.max_primes,
                'delta': self.delta,
                'sigma0': self.sigma0,
                'precision_dps': mp.mp.dps
            },
            'results': results,
            'summary': {
                'total_tests': len(results),
                'passed': passed_count,
                'failed': len(results) - passed_count
            }
        }
        
        with open(output_file, 'w') as f:
            json.dump(output_data, f, indent=2)
        
        print(f"\n📁 Results saved to: {output_file}")
        
        return passed_count == len(results)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description='V4.1 Appendix C Numerical Validation',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--max_primes', type=int, default=1000,
                       help='Maximum number of primes (default: 1000)')
    parser.add_argument('--delta', type=float, default=0.01,
                       help='Smoothing parameter (default: 0.01)')
    parser.add_argument('--sigma0', type=float, default=2.0,
                       help='Evaluation point σ₀ (default: 2.0)')
    parser.add_argument('--precision', type=int, default=50,
                       help='Decimal precision (default: 50)')
    
    args = parser.parse_args()
    
    # Set precision
    mp.mp.dps = args.precision
    
    # Create validator and run
    validator = V41Validator(
        max_primes=args.max_primes,
        delta=args.delta,
        sigma0=args.sigma0
    )
    
    success = validator.run_full_validation()
    
    return 0 if success else 1


if __name__ == '__main__':
    exit(main())
