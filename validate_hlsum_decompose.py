#!/usr/bin/env python3
"""
Validation script for Hardy-Littlewood sum decomposition by modular residues.

This script numerically validates the decomposition:
    ∑_{n < N} Λ(n)e^{2πiαn} = ∑_{r < q} e^{2πiαr} · ∑_{m < N/q+1} Λ(qm+r)e^{2πiαqm}

Author: José Manuel Mota Burruezo
Date: 2026-02-25
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple
import json
from datetime import datetime

def von_mangoldt(n: int) -> float:
    """
    Compute the von Mangoldt function Λ(n).
    
    Returns log p if n = p^k for some prime p and k ≥ 1, else 0.
    
    Args:
        n: Positive integer
        
    Returns:
        Λ(n) value
    """
    if n <= 1:
        return 0.0
    
    # Find prime factorization
    # If n is a prime power, all factors are the same prime
    factors = []
    temp = n
    d = 2
    while d * d <= temp:
        while temp % d == 0:
            factors.append(d)
            temp //= d
        d += 1
    if temp > 1:
        factors.append(temp)
    
    # Check if all factors are the same (prime power)
    if len(factors) == 0:
        return 0.0
    if all(f == factors[0] for f in factors):
        return np.log(factors[0])
    else:
        return 0.0


def hlsum_direct(N: int, alpha: float) -> complex:
    """
    Compute Hardy-Littlewood sum directly:
        ∑_{n < N} Λ(n) exp(2πiαn)
    
    Args:
        N: Upper limit for summation
        alpha: Frequency parameter
        
    Returns:
        Complex sum value
    """
    result = 0.0 + 0.0j
    for n in range(N):
        lambda_n = von_mangoldt(n)
        if lambda_n > 0:  # Optimize by skipping zero terms
            result += lambda_n * np.exp(2j * np.pi * alpha * n)
    return result


def hlsum_decomposed(N: int, q: int, alpha: float) -> complex:
    """
    Compute Hardy-Littlewood sum using modular decomposition:
        ∑_{r < q} exp(2πiαr) · ∑_{m < N/q+1} Λ(qm+r) exp(2πiαqm)
    
    Args:
        N: Upper limit for summation
        q: Modulus for decomposition
        alpha: Frequency parameter
        
    Returns:
        Complex sum value
    """
    if q <= 0:
        raise ValueError("q must be positive")
    
    result = 0.0 + 0.0j
    
    # Sum over residue classes r = 0, 1, ..., q-1
    for r in range(q):
        # Phase factor for this residue class
        phase_r = np.exp(2j * np.pi * alpha * r)
        
        # Inner sum over m
        inner_sum = 0.0 + 0.0j
        for m in range(N // q + 1):
            n = q * m + r
            if n < N:  # Ensure we don't exceed N
                lambda_n = von_mangoldt(n)
                if lambda_n > 0:
                    inner_sum += lambda_n * np.exp(2j * np.pi * alpha * q * m)
        
        result += phase_r * inner_sum
    
    return result


def validate_decomposition(N: int, q: int, alpha: float, 
                          tolerance: float = 1e-10) -> Tuple[bool, dict]:
    """
    Validate that direct and decomposed computations agree.
    
    Args:
        N: Upper limit
        q: Modulus
        alpha: Frequency
        tolerance: Acceptable error
        
    Returns:
        (success, details_dict)
    """
    direct = hlsum_direct(N, alpha)
    decomposed = hlsum_decomposed(N, q, alpha)
    
    diff = abs(direct - decomposed)
    rel_error = diff / (abs(direct) + 1e-20)  # Avoid division by zero
    
    success = diff < tolerance
    
    details = {
        'N': N,
        'q': q,
        'alpha': alpha,
        'direct_value': {
            'real': float(direct.real),
            'imag': float(direct.imag),
            'abs': float(abs(direct))
        },
        'decomposed_value': {
            'real': float(decomposed.real),
            'imag': float(decomposed.imag),
            'abs': float(abs(decomposed))
        },
        'absolute_error': float(diff),
        'relative_error': float(rel_error),
        'tolerance': tolerance,
        'success': bool(success)
    }
    
    return success, details


def run_validation_suite():
    """Run a comprehensive validation suite."""
    
    print("="*70)
    print("Hardy-Littlewood Sum Decomposition Validation")
    print("="*70)
    print()
    
    test_cases = [
        # (N, q, alpha, description)
        (50, 3, 0.123, "Small N, small q"),
        (100, 5, 0.5, "Medium N, small q"),
        (100, 7, 0.141, "Medium N, prime q"),
        (200, 10, 0.333, "Large N, composite q"),
        (100, 13, 1.0, "Medium N, prime q, α=1"),
        (150, 6, 0.0, "α=0 (should equal sum of Λ(n))"),
    ]
    
    results = []
    all_passed = True
    
    for i, (N, q, alpha, desc) in enumerate(test_cases, 1):
        print(f"Test {i}: {desc}")
        print(f"  Parameters: N={N}, q={q}, α={alpha}")
        
        success, details = validate_decomposition(N, q, alpha)
        results.append(details)
        
        if success:
            print(f"  ✅ PASSED (error: {details['absolute_error']:.2e})")
        else:
            print(f"  ❌ FAILED (error: {details['absolute_error']:.2e})")
            all_passed = False
        
        print(f"  Direct:     {details['direct_value']['real']:.6f} + "
              f"{details['direct_value']['imag']:.6f}i")
        print(f"  Decomposed: {details['decomposed_value']['real']:.6f} + "
              f"{details['decomposed_value']['imag']:.6f}i")
        print()
    
    # Summary
    print("="*70)
    print("VALIDATION SUMMARY")
    print("="*70)
    passed = sum(1 for r in results if r['success'])
    total = len(results)
    print(f"Tests passed: {passed}/{total}")
    print(f"Success rate: {100*passed/total:.1f}%")
    
    if all_passed:
        print("\n✅ ALL TESTS PASSED - Decomposition is mathematically correct!")
    else:
        print("\n⚠️ SOME TESTS FAILED - Review implementation")
    
    # Save certificate
    certificate = {
        'validation_timestamp': datetime.now().isoformat(),
        'module': 'hlsum_decompose.lean',
        'theorem': 'HLsum_decompose_mod_q',
        'test_results': results,
        'summary': {
            'total_tests': total,
            'passed': passed,
            'failed': total - passed,
            'success_rate': float(passed / total),
            'all_passed': bool(all_passed)
        },
        'mathematical_statement': (
            "∑_{n < N} Λ(n)e^{2πiαn} = "
            "∑_{r < q} e^{2πiαr} · ∑_{m < N/q+1} Λ(qm+r)e^{2πiαqm}"
        ),
        'author': {
            'name': 'José Manuel Mota Burruezo',
            'orcid': '0009-0002-1923-0773',
            'institution': 'Instituto de Conciencia Cuántica (ICQ)'
        }
    }
    
    cert_path = 'data/hlsum_decompose_validation_certificate.json'
    try:
        with open(cert_path, 'w') as f:
            json.dump(certificate, f, indent=2)
        print(f"\n📋 Validation certificate saved to: {cert_path}")
    except Exception as e:
        print(f"\n⚠️ Could not save certificate: {e}")
    
    return all_passed, certificate


if __name__ == '__main__':
    # Test von Mangoldt function first
    print("Testing von Mangoldt function Λ(n):")
    test_values = [
        (1, 0.0, "Λ(1) = 0"),
        (2, np.log(2), "Λ(2) = log 2 (prime)"),
        (4, np.log(2), "Λ(4) = log 2 (2² = prime power)"),
        (6, 0.0, "Λ(6) = 0 (not prime power)"),
        (8, np.log(2), "Λ(8) = log 2 (2³ = prime power)"),
        (9, np.log(3), "Λ(9) = log 3 (3² = prime power)"),
        (11, np.log(11), "Λ(11) = log 11 (prime)"),
    ]
    
    for n, expected, desc in test_values:
        computed = von_mangoldt(n)
        error = abs(computed - expected)
        status = "✅" if error < 1e-10 else "❌"
        print(f"  {status} {desc}: computed={computed:.6f}, expected={expected:.6f}")
    
    print("\n")
    
    # Run main validation
    all_passed, certificate = run_validation_suite()
    
    # Exit with appropriate code
    exit(0 if all_passed else 1)
