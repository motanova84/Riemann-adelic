#!/usr/bin/env python3
"""
validate_hlsum_decompose.py
========================================================================
Numerical validation of HLsum decomposition into arithmetic progressions

This script validates that the HLsum decomposition formula:
  ∑_{n<N} Λ(n)e^{2πiαn} = ∑_{r<q} e^{2πiαr} · ∑_{m<M_r} Λ(qm+r)e^{2πiαqm}

is numerically correct for various choices of N, q, and α.

Framework: QCAL ∞³ (f₀ = 141.7001 Hz, C = 244.36)
========================================================================
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
