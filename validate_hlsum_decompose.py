#!/usr/bin/env python3
"""
validate_hlsum_decompose.py
Numerical validation of HLsum decomposition into arithmetic progressions

This script validates that the HLsum decomposition formula:
  ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} e^{2πiαr} · ∑_{m<M_r} Λ(qm+r)e^{2πiαqm}

is numerically correct for various choices of N, q, and α.

Framework: QCAL ∞³ (f₀ = 141.7001 Hz, C = 244.36)
"""

import numpy as np
from sympy import primefactors, factorint, log
from decimal import Decimal, getcontext
import json
import hashlib
from typing import Tuple, List

# Set high precision
getcontext().prec = 50

# QCAL Constants
F0 = 141.7001  # Hz
C_COHERENCE = 244.36

def von_mangoldt(n: int) -> float:
    """
    Compute the von Mangoldt function Λ(n).
    
    Returns log(p) if n = p^k for some prime p, otherwise 0.
Validation script for Hardy-Littlewood Sum Decomposition
Tests the HLsum_decompose_mod_q lemma numerically.

This script validates that the decomposition:
  ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} ∑_{m<N/q+1} [qm+r<N] Λ(qm+r)e^{2πiα(qm+r)}
holds numerically for various test cases.
"""

import numpy as np
import json
import hashlib
from typing import Dict, Any, List, Tuple
from datetime import datetime


def von_mangoldt(n: int) -> float:
    """
    Von Mangoldt function Λ(n).
    Returns log(p) if n = p^k for some prime p, else 0.
    """
    if n <= 1:
        return 0.0
    
    factors = factorint(n)
    if len(factors) == 1:
        # n is a prime power
        p = list(factors.keys())[0]
        return float(log(p).evalf())
    return 0.0

def HLsum_direct(N: int, alpha: float) -> complex:
    """
    Compute HLsum directly: ∑_{n=0}^{N-1} Λ(n) · e^{2πiαn}
    # Factor n
    factors = []
    temp = n
    d = 2
    while d * d <= temp:
        count = 0
        while temp % d == 0:
            count += 1
            temp //= d
        if count > 0:
            factors.append((d, count))
        d += 1
    if temp > 1:
        factors.append((temp, 1))
    
    # Check if n is a prime power
    if len(factors) == 1:
        p, k = factors[0]
        return np.log(p)
    return 0.0


def HLsum_direct(N: int, alpha: float) -> complex:
    """
    Direct computation of Hardy-Littlewood sum:
    ∑_{n<N} Λ(n)·e^{2πiαn}
    """
    result = 0.0 + 0.0j
    for n in range(N):
        Lambda_n = von_mangoldt(n)
        if Lambda_n > 0:
            phase = 2 * np.pi * alpha * n
            result += Lambda_n * np.exp(1j * phase)
    return result

def HLsum_decomposed(N: int, q: int, alpha: float) -> complex:
    """
    Compute HLsum using decomposition:
      ∑_{r<q} e^{2πiαr} · ∑_{m<M_r} Λ(qm+r) · e^{2πiαqm}
    """
    result = 0.0 + 0.0j
    
    for r in range(q):
        # Compute M_r = ceil((N - r) / q)
        if N > r:
            M_r = (N - r + q - 1) // q
        else:
            M_r = 0
        
        # Phase factor for r
        phase_r = 2 * np.pi * alpha * r
        exp_r = np.exp(1j * phase_r)
        
        # Inner sum over m
        inner_sum = 0.0 + 0.0j
        for m in range(M_r):
            n = q * m + r
            if n < N:
                Lambda_n = von_mangoldt(n)
                if Lambda_n > 0:
                    phase_m = 2 * np.pi * alpha * q * m
                    inner_sum += Lambda_n * np.exp(1j * phase_m)
        
        result += exp_r * inner_sum
    
    return result

def test_hlsum_decomposition(N: int, q: int, alpha: float, 
                             tolerance: float = 1e-10) -> Tuple[bool, float]:
    """
    Test that HLsum_direct and HLsum_decomposed give the same result.
    
    Returns:
        (passed, error): Whether test passed and the absolute error
    """
    direct = HLsum_direct(N, alpha)
    decomposed = HLsum_decomposed(N, q, alpha)
    
    error = abs(direct - decomposed)
    passed = error < tolerance
    
    return passed, error

def run_validation_suite() -> dict:
    """
    Run comprehensive validation suite for HLsum decomposition.
    """
    print("=" * 80)
    print("QCAL ∞³ HLsum Decomposition Validation")
    print(f"Frequency: f₀ = {F0} Hz")
    print(f"Coherence: C = {C_COHERENCE}")
    print("=" * 80)
    print()
    
    test_cases = [
        # (N, q, alpha, description)
        (10, 2, 0.0, "Small N, q=2, α=0"),
        (10, 3, 0.5, "Small N, q=3, α=0.5"),
        (20, 5, 0.1, "Medium N, q=5, α=0.1"),
        (50, 7, 0.25, "Larger N, q=7, α=0.25"),
        (100, 11, F0/1000, "N=100, q=11, α=f₀/1000 (QCAL)"),
        (100, 13, 1/np.sqrt(2), "N=100, q=13, α=1/√2 (irrational)"),
    ]
    
    results = []
    all_passed = True
    
    for i, (N, q, alpha, desc) in enumerate(test_cases, 1):
        print(f"Test {i}: {desc}")
        print(f"  Parameters: N={N}, q={q}, α={alpha:.6f}")
        
        passed, error = test_hlsum_decomposition(N, q, alpha)
        
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"  Result: {status}")
        print(f"  Error: {error:.2e}")
        print()
        
        results.append({
            "test_number": i,
            "description": desc,
            "N": N,
            "q": q,
            "alpha": float(alpha),
            "passed": bool(passed),
            "error": float(error)
        })
        
        if not passed:
            all_passed = False
    
    # Summary
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    passed_count = sum(1 for r in results if r["passed"])
    total_count = len(results)
    print(f"Tests passed: {passed_count}/{total_count}")
    
    if all_passed:
        print("✓ ALL TESTS PASSED - HLsum decomposition is numerically correct")
    else:
        print("✗ SOME TESTS FAILED - Check implementation")
    
    return {
        "framework": "QCAL ∞³",
        "f0_hz": F0,
        "coherence": C_COHERENCE,
        "all_passed": all_passed,
        "tests": results,
        "summary": {
            "total": total_count,
            "passed": passed_count,
            "failed": total_count - passed_count
        }
    }

def generate_certificate(results: dict) -> str:
    """
    Generate validation certificate with QCAL hash.
    """
    # Compute hash of results
    result_str = json.dumps(results, sort_keys=True)
    hash_obj = hashlib.sha256(result_str.encode())
    cert_hash = hash_obj.hexdigest()[:16]
    
    certificate = {
        "validation_type": "HLsum_decomposition",
        "framework": "QCAL ∞³",
        "timestamp": "2026-02-26",
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "orcid": "0009-0002-1923-0773",
        "doi": "10.5281/zenodo.17379721",
        "all_tests_passed": results["all_passed"],
        "test_summary": results["summary"],
        "certificate_hash": f"0xQCAL_HLSUM_{cert_hash}"
    }
    
    return json.dumps(certificate, indent=2)

def main():
    """Main validation routine."""
    results = run_validation_suite()
    
    # Save results
    with open("data/hlsum_decompose_validation.json", "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to: data/hlsum_decompose_validation.json")
    
    # Generate certificate
    cert = generate_certificate(results)
    with open("data/hlsum_decompose_certificate.json", "w") as f:
        f.write(cert)
    print(f"Certificate saved to: data/hlsum_decompose_certificate.json")
    
    # Print certificate
    print("\n" + "=" * 80)
    print("VALIDATION CERTIFICATE")
    print("=" * 80)
    print(cert)

if __name__ == "__main__":
    main()
        phase = 2 * np.pi * alpha * n
        result += Lambda_n * np.exp(1j * phase)
    return result


def HLsum_decomposed(N: int, q: int, alpha: float) -> complex:
    """
    Decomposed computation using residue classes:
    ∑_{r<q} ∑_{m<N/q+1} [qm+r<N] Λ(qm+r)·e^{2πiα(qm+r)}
    """
    if q <= 0:
        raise ValueError("q must be positive")
    
    result = 0.0 + 0.0j
    for r in range(q):
        for m in range(N // q + 1):
            n = q * m + r
            if n < N:
                Lambda_n = von_mangoldt(n)
                phase = 2 * np.pi * alpha * n
                result += Lambda_n * np.exp(1j * phase)
    return result


def test_hlsum_decomposition(N: int, q: int, alpha: float, 
                             test_name: str, tolerance: float = 1e-10) -> Dict[str, Any]:
    """
    Test HLsum decomposition for given parameters.
    
    Args:
        N: Upper limit for summation
        q: Modulus for decomposition
        alpha: Phase parameter
        test_name: Name of the test
        tolerance: Numerical tolerance for comparison
        
    Returns:
        Dictionary with test results
    """
    print(f"\n{'='*60}")
    print(f"Test: {test_name}")
    print(f"Parameters: N={N}, q={q}, α={alpha}")
    print(f"{'='*60}")
    
    # Compute both sums
    direct = HLsum_direct(N, alpha)
    decomposed = HLsum_decomposed(N, q, alpha)
    
    # Compare results
    diff = abs(direct - decomposed)
    relative_error = diff / (abs(direct) + 1e-12) if abs(direct) > 1e-12 else diff
    
    passed = diff < tolerance
    
    print(f"Direct sum:      {direct}")
    print(f"Decomposed sum:  {decomposed}")
    print(f"Absolute error:  {diff:.2e}")
    print(f"Relative error:  {relative_error:.2e}")
    print(f"Status:          {'✓ PASS' if passed else '✗ FAIL'}")
    
    return {
        'test_name': test_name,
        'parameters': {'N': N, 'q': q, 'alpha': alpha},
        'direct_sum': {'real': float(direct.real), 'imag': float(direct.imag)},
        'decomposed_sum': {'real': float(decomposed.real), 'imag': float(decomposed.imag)},
        'absolute_error': float(diff),
        'relative_error': float(relative_error),
        'passed': bool(passed),
        'tolerance': tolerance
    }


def run_all_tests() -> Tuple[List[Dict[str, Any]], bool]:
    """
    Run comprehensive test suite for HLsum decomposition.
    
    Returns:
        Tuple of (test_results, all_passed)
    """
    print("\n" + "="*70)
    print("HARDY-LITTLEWOOD SUM DECOMPOSITION VALIDATION")
    print("="*70)
    
    tests = []
    
    # Test 1: Small N, small q, rational alpha
    tests.append(test_hlsum_decomposition(
        N=100, q=10, alpha=0.5,
        test_name="Test 1: Small N, rational α"
    ))
    
    # Test 2: Medium N, prime q, irrational alpha
    tests.append(test_hlsum_decomposition(
        N=500, q=7, alpha=np.pi/7,
        test_name="Test 2: Medium N, prime q, irrational α"
    ))
    
    # Test 3: Large N, composite q
    tests.append(test_hlsum_decomposition(
        N=1000, q=12, alpha=0.123456,
        test_name="Test 3: Large N, composite q"
    ))
    
    # Test 4: Edge case q=1 (no decomposition)
    tests.append(test_hlsum_decomposition(
        N=200, q=1, alpha=0.25,
        test_name="Test 4: Edge case q=1"
    ))
    
    # Test 5: Large q relative to N
    tests.append(test_hlsum_decomposition(
        N=150, q=50, alpha=0.707,
        test_name="Test 5: Large q relative to N"
    ))
    
    # Test 6: Golden ratio alpha (highly irrational)
    golden = (1 + np.sqrt(5)) / 2
    tests.append(test_hlsum_decomposition(
        N=300, q=17, alpha=1/golden,
        test_name="Test 6: Golden ratio α"
    ))
    
    # Summary
    all_passed = all(t['passed'] for t in tests)
    passed_count = sum(1 for t in tests if t['passed'])
    
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Total tests:  {len(tests)}")
    print(f"Passed:       {passed_count}")
    print(f"Failed:       {len(tests) - passed_count}")
    print(f"Success rate: {passed_count}/{len(tests)} ({100*passed_count/len(tests):.1f}%)")
    print(f"Overall:      {'✓ ALL TESTS PASSED' if all_passed else '✗ SOME TESTS FAILED'}")
    print("="*70)
    
    return tests, all_passed


def generate_certificate(test_results: List[Dict[str, Any]], all_passed: bool) -> Dict[str, Any]:
    """
    Generate validation certificate with test results.
    """
    # Create certificate data
    certificate = {
        'validation_type': 'HLsum_decompose_mod_q',
        'timestamp': datetime.now().isoformat() + 'Z',
        'validator': 'validate_hlsum_decompose.py',
        'framework': 'QCAL ∞³',
        'all_tests_passed': bool(all_passed),
        'test_count': len(test_results),
        'passed_count': sum(1 for t in test_results if t['passed']),
        'test_results': test_results,
        'mathematical_property': 'HLsum decomposition by residue classes mod q',
        'implementation_files': [
            'formalization/lean/RiemannAdelic/core/analytic/von_mangoldt.lean',
            'formalization/lean/RiemannAdelic/core/analytic/hlsum_decompose.lean'
        ],
        'qcal_coherence': {
            'base_frequency': 141.7001,
            'framework': 'QCAL ∞³',
            'validation_status': 'coherent' if all_passed else 'requires_review'
        }
    }
    
    # Generate hash
    cert_str = json.dumps(certificate, sort_keys=True)
    cert_hash = hashlib.sha256(cert_str.encode()).hexdigest()[:16]
    certificate['certificate_hash'] = f"0xQCAL_HLSUM_{cert_hash}"
    
    return certificate


def save_certificate(certificate: Dict[str, Any], filename: str = 'data/hlsum_decompose_validation_certificate.json'):
    """
    Save validation certificate to JSON file.
    """
    import os
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    with open(filename, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n✓ Certificate saved to: {filename}")
    print(f"  Hash: {certificate['certificate_hash']}")


def main():
    """
    Main validation routine.
    """
    # Run all tests
    test_results, all_passed = run_all_tests()
    
    # Generate and save certificate
    certificate = generate_certificate(test_results, all_passed)
    save_certificate(certificate)
    
    # Exit with appropriate code
    exit_code = 0 if all_passed else 1
    
    print("\n" + "="*70)
    if all_passed:
        print("✅ VALIDATION COMPLETE - All tests passed!")
        print("   HLsum decomposition lemma is numerically validated.")
    else:
        print("⚠️  VALIDATION INCOMPLETE - Some tests failed.")
        print("   Review test results above.")
    print("="*70)
    
    return exit_code


if __name__ == '__main__':
    import sys
    sys.exit(main())
