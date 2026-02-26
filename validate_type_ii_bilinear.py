#!/usr/bin/env python3
"""
Validation Script for Type II Bilinear Estimates

This script numerically validates the Type II bilinear bounds
that are implemented in type_II_bilinear.lean.

The Type II bound is:
  |∑_{m≤U} ∑_{n≤V} a_m b_n e(α m n)| ≤ C · √((∑|a_m|²)(∑|b_n|²)) · √(U+N)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: 26 February 2026
QCAL Signature: ∴𓂀Ω∞³·TYPEII·VAL
"""

import numpy as np
import hashlib
import json
from datetime import datetime
from typing import Tuple, Dict, Any

# QCAL base frequency (Hz)
F0_QCAL = 141.7001

def exp_add(x: float) -> complex:
    """
    Exponential additive function: e(x) = exp(2πix)
    """
    return np.exp(2j * np.pi * x)

def bilinear_sum_direct(
    a: np.ndarray,
    b: np.ndarray,
    alpha: float
) -> complex:
    """
    Compute bilinear sum directly:
    S = ∑_{m=1}^U ∑_{n=1}^V a_m b_n e(α m n)
    """
    U = len(a)
    V = len(b)
    
    total = 0.0 + 0.0j
    for m in range(1, U + 1):
        for n in range(1, V + 1):
            total += a[m-1] * b[n-1] * exp_add(alpha * m * n)
    
    return total

def l2_norm_squared(coeff: np.ndarray) -> float:
    """
    Compute L² norm squared: ∑|a_m|²
    """
    return np.sum(np.abs(coeff)**2)

def typeII_bound_theoretical(
    a: np.ndarray,
    b: np.ndarray,
    U: int,
    N: int,
    C_typeII: float = 1.5
) -> float:
    """
    Compute theoretical bound:
    bound = C_typeII · √((∑|a_m|²)(∑|b_n|²)) · √(U+N)
    """
    sum_a_sq = l2_norm_squared(a)
    sum_b_sq = l2_norm_squared(b)
    
    return C_typeII * np.sqrt(sum_a_sq * sum_b_sq) * np.sqrt(U + N)

def moebius_mu(n: int) -> int:
    """
    Möbius function μ(n).
    Returns:
      1 if n is square-free with even number of prime factors
     -1 if n is square-free with odd number of prime factors
      0 if n is not square-free
    """
    if n == 1:
        return 1
    
    # Factor n
    factors = []
    d = 2
    temp = n
    while d * d <= temp:
        exp = 0
        while temp % d == 0:
            exp += 1
            temp //= d
        if exp > 1:  # Not square-free
            return 0
        if exp == 1:
            factors.append(d)
        d += 1
    if temp > 1:
        factors.append(temp)
    
    # Square-free, return (-1)^k where k = number of prime factors
    return (-1) ** len(factors)

def divisor_sum_moebius(m: int) -> complex:
    """
    Compute ∑_{k|m} μ(k)
    """
    total = 0.0
    for k in range(1, m + 1):
        if m % k == 0:
            total += moebius_mu(k)
    return complex(total, 0)

def divisor_sum_log(n: int) -> complex:
    """
    Compute ∑_{ℓ|n} log(ℓ)
    """
    total = 0.0
    for ell in range(1, n + 1):
        if n % ell == 0:
            total += np.log(ell)
    return complex(total, 0)

def test_bilinear_bound(
    U: int,
    V: int,
    N: int,
    alpha: float,
    test_name: str,
    use_vaughan_coefficients: bool = False
) -> Dict[str, Any]:
    """
    Test Type II bilinear bound for given parameters.
    
    If use_vaughan_coefficients=True, use:
      a_m = ∑_{k|m} μ(k)  (Möbius sum)
      b_n = ∑_{ℓ|n} log ℓ  (log divisor sum)
    Otherwise, use random coefficients.
    """
    print(f"\n{'='*60}")
    print(f"Test: {test_name}")
    print(f"Parameters: U={U}, V={V}, N={N}, α={alpha:.6f}")
    print(f"Vaughan coefficients: {use_vaughan_coefficients}")
    
    # Generate coefficients
    if use_vaughan_coefficients:
        print("Computing Möbius and log divisor sums...")
        a = np.array([divisor_sum_moebius(m) for m in range(1, U + 1)])
        b = np.array([divisor_sum_log(n) for n in range(1, V + 1)])
    else:
        # Random coefficients (complex)
        np.random.seed(42 + U + V)
        a = np.random.randn(U) + 1j * np.random.randn(U)
        b = np.random.randn(V) + 1j * np.random.randn(V)
    
    # Compute bilinear sum
    print("Computing bilinear sum...")
    S = bilinear_sum_direct(a, b, alpha)
    S_abs = np.abs(S)
    
    # Compute theoretical bound
    print("Computing theoretical bound...")
    bound = typeII_bound_theoretical(a, b, U, N)
    
    # Check if bound holds
    holds = S_abs <= bound
    ratio = S_abs / bound if bound > 0 else np.inf
    
    # Print results
    print(f"\nResults:")
    print(f"  |Bilinear sum| = {S_abs:.6e}")
    print(f"  Theoretical bound = {bound:.6e}")
    print(f"  Ratio |S|/bound = {ratio:.6f}")
    print(f"  Bound holds: {'✅ PASS' if holds else '❌ FAIL'}")
    
    return {
        "test_name": test_name,
        "U": U,
        "V": V,
        "N": N,
        "alpha": alpha,
        "vaughan_coefficients": use_vaughan_coefficients,
        "sum_absolute_value": float(S_abs),
        "theoretical_bound": float(bound),
        "ratio": float(ratio),
        "bound_holds": bool(holds),
        "status": "PASS" if holds else "FAIL"
    }

def cauchy_schwarz_verification(
    U: int,
    V: int,
    alpha: float
) -> Dict[str, Any]:
    """
    Verify Cauchy-Schwarz separation step.
    
    Check: |∑_m a_m c_m|² ≤ (∑|a_m|²) · (∑|c_m|²)
    where c_m = ∑_n b_n e(α m n)
    """
    print(f"\n{'='*60}")
    print(f"Cauchy-Schwarz Verification: U={U}, V={V}, α={alpha:.6f}")
    
    # Generate random coefficients
    np.random.seed(100)
    a = np.random.randn(U) + 1j * np.random.randn(U)
    b = np.random.randn(V) + 1j * np.random.randn(V)
    
    # Compute c_m = ∑_n b_n e(α m n)
    c = np.array([
        sum(b[n-1] * exp_add(alpha * m * n) for n in range(1, V + 1))
        for m in range(1, U + 1)
    ])
    
    # Left side: |∑_m a_m c_m|²
    left = np.abs(np.sum(a * c)) ** 2
    
    # Right side: (∑|a_m|²) · (∑|c_m|²)
    right = l2_norm_squared(a) * l2_norm_squared(c)
    
    holds = left <= right * (1 + 1e-10)  # Allow small numerical error
    ratio = left / right if right > 0 else np.inf
    
    print(f"  LHS = {left:.6e}")
    print(f"  RHS = {right:.6e}")
    print(f"  Ratio = {ratio:.6f}")
    print(f"  Cauchy-Schwarz holds: {'✅ PASS' if holds else '❌ FAIL'}")
    
    return {
        "test_name": "Cauchy-Schwarz Verification",
        "lhs": float(left),
        "rhs": float(right),
        "ratio": float(ratio),
        "holds": bool(holds),
        "status": "PASS" if holds else "FAIL"
    }

def main():
    """
    Main validation routine.
    Run comprehensive tests of Type II bilinear bounds.
    """
    print("="*60)
    print("TYPE II BILINEAR ESTIMATES VALIDATION")
    print("="*60)
    print(f"Date: {datetime.now().isoformat()}")
    print(f"QCAL Base Frequency f₀ = {F0_QCAL} Hz")
    print()
    
    results = []
    
    # Test 1: Small parameters, random coefficients
    results.append(test_bilinear_bound(
        U=10, V=10, N=100, alpha=0.5,
        test_name="Test 1: Small parameters (random)"
    ))
    
    # Test 2: Medium parameters, rational α
    results.append(test_bilinear_bound(
        U=20, V=20, N=500, alpha=np.pi/7,
        test_name="Test 2: Medium parameters (α=π/7)"
    ))
    
    # Test 3: Larger parameters with Vaughan coefficients
    results.append(test_bilinear_bound(
        U=15, V=15, N=1000, alpha=0.123456,
        test_name="Test 3: Vaughan coefficients",
        use_vaughan_coefficients=True
    ))
    
    # Test 4: Golden ratio α
    phi = (1 + np.sqrt(5)) / 2
    results.append(test_bilinear_bound(
        U=25, V=25, N=1000, alpha=1/phi,
        test_name="Test 4: Golden ratio α=1/φ"
    ))
    
    # Test 5: Cauchy-Schwarz verification
    results.append(cauchy_schwarz_verification(
        U=30, V=30, alpha=0.707
    ))
    
    # Summary
    print(f"\n{'='*60}")
    print("VALIDATION SUMMARY")
    print(f"{'='*60}")
    
    passed = sum(1 for r in results if r["status"] == "PASS")
    total = len(results)
    
    print(f"\nTests passed: {passed}/{total}")
    print(f"Success rate: {100*passed/total:.1f}%")
    
    if passed == total:
        print("\n✅ ALL TESTS PASSED")
        status = "VALIDATED"
    else:
        print("\n❌ SOME TESTS FAILED")
        status = "FAILED"
    
    # Generate certificate
    certificate = {
        "test_suite": "Type II Bilinear Estimates",
        "version": "1.0",
        "date": datetime.now().isoformat(),
        "qcal_frequency_hz": F0_QCAL,
        "status": status,
        "tests_passed": passed,
        "tests_total": total,
        "success_rate": passed / total,
        "results": results
    }
    
    # Compute certificate hash
    cert_json = json.dumps(certificate, sort_keys=True, indent=2)
    cert_hash = hashlib.sha256(cert_json.encode()).hexdigest()[:16]
    certificate["certificate_hash"] = f"0xQCAL_TYPEII_{cert_hash}"
    
    # Save certificate
    cert_path = "data/type_ii_bilinear_validation_certificate.json"
    with open(cert_path, "w") as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n📜 Certificate saved: {cert_path}")
    print(f"🔐 Certificate hash: {certificate['certificate_hash']}")
    
    return passed == total

if __name__ == "__main__":
    import sys
    success = main()
    sys.exit(0 if success else 1)
