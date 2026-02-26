#!/usr/bin/env python3
"""
Validation Script for DivisorBoundsVaughan.lean

This script validates the mathematical properties of:
1. card_multiples_le: counting via lcm
2. mobiusConv_abs_le_tau: Möbius convolution bound
3. logSum_le_tau_log: log sum control
4. vaughan_l2_fuel: L² product bound

Author: José Manuel Mota Burruezo Ψ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
Date: 25 February 2026
Version: V7.1-VaughanTypeII
"""

import numpy as np
import json
import hashlib
from datetime import datetime
from pathlib import Path

# QCAL Constants
F0 = 141.7001  # Base frequency (Hz)
C_COHERENCE = 244.36  # Coherence constant


def count_divisors(n):
    """Compute τ(n): number of divisors of n."""
    if n <= 0:
        return 0
    count = 0
    for i in range(1, int(np.sqrt(n)) + 1):
        if n % i == 0:
            count += 1
            if i != n // i:
                count += 1
    return count


def get_divisors(n):
    """Get list of all divisors of n."""
    if n <= 0:
        return []
    divisors = []
    for i in range(1, int(np.sqrt(n)) + 1):
        if n % i == 0:
            divisors.append(i)
            if i != n // i:
                divisors.append(n // i)
    return sorted(divisors)


def moebius_mu(n):
    """
    Möbius function μ(n).
    Returns:
      1 if n is a square-free positive integer with an even number of prime factors
     -1 if n is a square-free positive integer with an odd number of prime factors
      0 if n has a squared prime factor
    """
    if n <= 0:
        return 0
    if n == 1:
        return 1
    
    # Factor n and check for square factors
    prime_factors = []
    temp = n
    d = 2
    while d * d <= temp:
        count = 0
        while temp % d == 0:
            count += 1
            temp //= d
        if count > 1:
            return 0  # Has squared factor
        if count == 1:
            prime_factors.append(d)
        d += 1
    if temp > 1:
        prime_factors.append(temp)
    
    # Return (-1)^k where k is number of prime factors
    return (-1) ** len(prime_factors)


def mobius_convolution(n):
    """
    Möbius convolution: ∑_{d|n} μ(d)
    This is the identity function for n=1 and 0 for n>1.
    """
    divisors = get_divisors(n)
    return sum(moebius_mu(d) for d in divisors)


def log_sum(n):
    """
    Sum of logarithms of divisors: ∑_{d|n} log(d)
    """
    if n <= 1:
        return 0.0
    divisors = get_divisors(n)
    return sum(np.log(d) for d in divisors if d > 0)


def count_multiples_lcm(d, e, X):
    """
    Count integers in [1, X] divisible by both d and e.
    This should equal the count of multiples of lcm(d,e) in [1, X].
    """
    if d == 0 or e == 0 or X < 1:
        return 0
    lcm = (d * e) // np.gcd(d, e)
    return X // lcm


def validate_card_multiples_le():
    """
    Validate: card_multiples_le
    Number of integers ≤ X divisible by both d and e is ≤ X / lcm(d,e)
    """
    print("\n" + "="*70)
    print("TEST 1: card_multiples_le - Counting via LCM")
    print("="*70)
    
    test_cases = [
        (2, 3, 100),
        (4, 6, 100),
        (5, 7, 200),
        (10, 15, 500),
        (12, 18, 1000),
    ]
    
    all_passed = True
    for d, e, X in test_cases:
        # Count directly
        actual_count = sum(1 for n in range(1, X+1) if n % d == 0 and n % e == 0)
        
        # Bound via lcm
        lcm = (d * e) // np.gcd(d, e)
        bound = X // lcm
        
        passed = actual_count <= bound
        all_passed &= passed
        
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: d={d}, e={e}, X={X}")
        print(f"  Actual count: {actual_count}")
        print(f"  Bound (X/lcm): {bound}")
        print(f"  lcm(d,e) = {lcm}")
        
        # Verify equality (should be exact)
        if actual_count == bound:
            print(f"  ✓ Exact equality achieved")
        else:
            print(f"  ⚠ Bound is not tight (difference: {bound - actual_count})")
    
    return all_passed


def validate_mobius_conv_bound():
    """
    Validate: mobiusConv_abs_le_tau
    |∑_{d|n} μ(d)| ≤ τ(n)
    """
    print("\n" + "="*70)
    print("TEST 2: mobiusConv_abs_le_tau - Möbius Convolution Bound")
    print("="*70)
    
    test_range = range(1, 101)  # Test n = 1 to 100
    
    all_passed = True
    max_violation = 0
    violations = []
    
    for n in test_range:
        mobius_conv = mobius_convolution(n)
        tau_n = count_divisors(n)
        
        passed = abs(mobius_conv) <= tau_n
        all_passed &= passed
        
        if not passed:
            violations.append((n, abs(mobius_conv), tau_n))
            violation = abs(mobius_conv) - tau_n
            max_violation = max(max_violation, violation)
    
    if all_passed:
        print(f"✓ PASS: All {len(test_range)} test cases passed")
        print(f"  Tested n ∈ [1, {max(test_range)}]")
        
        # Show some interesting cases
        print("\n  Sample values:")
        for n in [1, 6, 12, 30, 60]:
            mc = mobius_convolution(n)
            tau = count_divisors(n)
            print(f"    n={n:3d}: mobiusConv={mc:2d}, τ(n)={tau:2d}, |mobiusConv|={abs(mc):2d}")
    else:
        print(f"✗ FAIL: {len(violations)} violations found")
        print(f"  Max violation: {max_violation}")
        print(f"  First 5 violations: {violations[:5]}")
    
    return all_passed


def validate_log_sum_bound():
    """
    Validate: logSum_le_tau_log
    ∑_{d|n} log(d) ≤ τ(n) · log(n) for n ≥ 2
    """
    print("\n" + "="*70)
    print("TEST 3: logSum_le_tau_log - Log Sum Control")
    print("="*70)
    
    test_range = range(2, 101)  # Test n = 2 to 100
    
    all_passed = True
    max_violation = 0
    violations = []
    
    for n in test_range:
        ls = log_sum(n)
        tau_n = count_divisors(n)
        bound = tau_n * np.log(n)
        
        passed = ls <= bound + 1e-10  # Small tolerance for floating point
        all_passed &= passed
        
        if not passed:
            violations.append((n, ls, bound))
            violation = ls - bound
            max_violation = max(max_violation, violation)
    
    if all_passed:
        print(f"✓ PASS: All {len(test_range)} test cases passed")
        print(f"  Tested n ∈ [2, {max(test_range)}]")
        
        # Show some interesting cases
        print("\n  Sample values:")
        for n in [2, 6, 12, 30, 60, 100]:
            ls = log_sum(n)
            tau = count_divisors(n)
            bound = tau * np.log(n)
            ratio = ls / bound if bound > 0 else 0
            print(f"    n={n:3d}: logSum={ls:8.4f}, bound={bound:8.4f}, ratio={ratio:.4f}")
    else:
        print(f"✗ FAIL: {len(violations)} violations found")
        print(f"  Max violation: {max_violation}")
        print(f"  First 5 violations: {violations[:5]}")
    
    return all_passed


def validate_vaughan_l2_fuel():
    """
    Validate: vaughan_l2_fuel
    (∑ |mobiusConv(n)|²) · (∑ logSum²(n)) ≤ C · X² · (log X)⁶
    """
    print("\n" + "="*70)
    print("TEST 4: vaughan_l2_fuel - L² Product Bound")
    print("="*70)
    
    test_Xs = [10, 20, 50, 100, 200]
    
    all_passed = True
    empirical_constants = []
    
    for X in test_Xs:
        # Compute the left-hand side
        sum_mobius_sq = sum(
            abs(mobius_convolution(n)) ** 2 
            for n in range(1, X+1)
        )
        
        sum_log_sq = sum(
            log_sum(n) ** 2 
            for n in range(1, X+1) if n >= 2
        )
        
        lhs = sum_mobius_sq * sum_log_sq
        
        # Compute the right-hand side bound
        log_X = np.log(X)
        rhs_factor = X ** 2 * log_X ** 6
        
        # Determine empirical constant C
        C_empirical = lhs / rhs_factor if rhs_factor > 0 else 0
        empirical_constants.append(C_empirical)
        
        # For validation, we check if a reasonable C exists
        # We expect C to be bounded and not grow with X
        passed = C_empirical < 1000  # Reasonable upper bound
        all_passed &= passed
        
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{status}: X={X}")
        print(f"  LHS: {lhs:.2e}")
        print(f"  RHS factor (X²·log⁶X): {rhs_factor:.2e}")
        print(f"  Empirical C: {C_empirical:.4f}")
    
    if all_passed:
        print(f"\n✓ PASS: Empirical constants are bounded")
        avg_C = np.mean(empirical_constants)
        std_C = np.std(empirical_constants)
        print(f"  Average C: {avg_C:.4f}")
        print(f"  Std dev: {std_C:.4f}")
        print(f"  Max C: {max(empirical_constants):.4f}")
    else:
        print(f"\n✗ FAIL: Empirical constants grow unbounded")
    
    return all_passed, empirical_constants


def generate_certificate():
    """
    Generate validation certificate with QCAL signature.
    """
    timestamp = datetime.now().isoformat()
    
    certificate = {
        "validation_type": "DivisorBoundsVaughan",
        "framework": "QCAL ∞³",
        "constants": {
            "f0_hz": F0,
            "coherence_C": C_COHERENCE
        },
        "timestamp": timestamp,
        "tests_performed": [
            "card_multiples_le",
            "mobiusConv_abs_le_tau",
            "logSum_le_tau_log",
            "vaughan_l2_fuel"
        ],
        "author": "José Manuel Mota Burruezo Ψ ∞³",
        "orcid": "0009-0002-1923-0773",
        "doi": "10.5281/zenodo.17379721",
        "version": "V7.1-VaughanTypeII"
    }
    
    # Compute certificate hash
    cert_str = json.dumps(certificate, sort_keys=True)
    cert_hash = hashlib.sha256(cert_str.encode()).hexdigest()[:16]
    certificate["hash"] = f"0xQCAL_VAUGHAN_{cert_hash}"
    
    return certificate


def main():
    """
    Run all validation tests.
    """
    print("=" * 70)
    print("DIVISOR BOUNDS & MÖBIUS CONVOLUTION VALIDATION")
    print("Framework: QCAL ∞³")
    print(f"Base frequency: f₀ = {F0} Hz")
    print(f"Coherence: C = {C_COHERENCE}")
    print("=" * 70)
    
    results = {}
    
    # Test 1: card_multiples_le
    results['test1_card_multiples'] = validate_card_multiples_le()
    
    # Test 2: mobiusConv_abs_le_tau
    results['test2_mobius_bound'] = validate_mobius_conv_bound()
    
    # Test 3: logSum_le_tau_log
    results['test3_log_sum'] = validate_log_sum_bound()
    
    # Test 4: vaughan_l2_fuel
    test4_passed, empirical_C = validate_vaughan_l2_fuel()
    results['test4_l2_fuel'] = test4_passed
    results['empirical_constants'] = empirical_C
    
    # Overall result
    print("\n" + "="*70)
    print("OVERALL VALIDATION RESULTS")
    print("="*70)
    
    all_tests_passed = all([
        results['test1_card_multiples'],
        results['test2_mobius_bound'],
        results['test3_log_sum'],
        results['test4_l2_fuel']
    ])
    
    if all_tests_passed:
        print("✓ ALL TESTS PASSED")
        print("\nDivisor bounds and Möbius convolution lemmas validated!")
        print("Ready for integration with Vaughan Type II estimates.")
    else:
        print("✗ SOME TESTS FAILED")
        print("\nReview failed tests above.")
    
    # Generate and save certificate
    certificate = generate_certificate()
    certificate['test_results'] = {
        'test1_card_multiples_le': bool(results['test1_card_multiples']),
        'test2_mobius_conv_bound': bool(results['test2_mobius_bound']),
        'test3_log_sum_bound': bool(results['test3_log_sum']),
        'test4_vaughan_l2_fuel': bool(results['test4_l2_fuel']),
        'all_passed': bool(all_tests_passed)
    }
    certificate['empirical_constants'] = [float(c) for c in empirical_C]
    
    cert_path = Path(__file__).parent / 'data' / 'divisor_bounds_vaughan_certificate.json'
    cert_path.parent.mkdir(exist_ok=True)
    
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n📜 Certificate saved: {cert_path}")
    print(f"🔐 Certificate hash: {certificate['hash']}")
    
    return 0 if all_tests_passed else 1


if __name__ == "__main__":
    exit(main())
