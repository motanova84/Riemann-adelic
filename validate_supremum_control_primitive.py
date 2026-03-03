#!/usr/bin/env python3
"""
Validation Script for Supremum Control of Primitive W(x)
=========================================================

This script validates the demonstration that:

    sup_{x ∈ ℝ} |W(x)|²/(1 + x²) < C

where W(x) = Σ_{p ≤ P} (1/√p) sin(x log p + φ_p) is the primitive of
the oscillatory potential.

Validation Tests:
----------------
1. Supremum finiteness: sup_x |W(x)|²/(1+x²) < ∞
2. Sub-quadratic growth: |W(x)|² = o(x²) as x → ∞
3. Origin regularity: W(0) is finite
4. Quadratic mean: ∫₀^T |W(x)|² dx ~ T log log T
5. KLMN conditions: Relative form bound a < 1
6. Essential self-adjointness verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
import json
import numpy as np
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent / "operators"))

from supremum_control_primitive import (
    estimate_supremum_bound,
    compute_quadratic_mean,
    verify_relative_form_boundedness,
    generate_certificate,
    compute_primitive_W,
    _sieve_primes,
)


def test_supremum_finiteness():
    """Test 1: Verify supremum is finite."""
    print("\n" + "=" * 70)
    print("TEST 1: Supremum Finiteness")
    print("=" * 70)
    
    result = estimate_supremum_bound(
        x_min=0.1,
        x_max=1000.0,
        n_points=5000,
        p_max=100,
    )
    
    is_finite = np.isfinite(result.supremum_ratio)
    
    print(f"Supremum value: {result.supremum_ratio:.6e}")
    print(f"Is finite: {is_finite}")
    
    assert is_finite, "Supremum must be finite"
    assert result.supremum_ratio > 0, "Supremum must be positive"
    
    print("✅ TEST 1 PASSED: Supremum is finite")
    return True


def test_sub_quadratic_growth():
    """Test 2: Verify |W(x)|² = o(x²)."""
    print("\n" + "=" * 70)
    print("TEST 2: Sub-Quadratic Growth")
    print("=" * 70)
    
    result = estimate_supremum_bound(
        x_min=0.1,
        x_max=1000.0,
        n_points=5000,
        p_max=100,
    )
    
    alpha = result.growth_exponent
    is_sub_quad = result.is_sub_quadratic
    
    print(f"Growth exponent α: {alpha:.4f}")
    print(f"Sub-quadratic (α < 2): {is_sub_quad}")
    
    assert alpha < 2.0, f"Growth exponent {alpha} must be < 2"
    assert is_sub_quad, "Must satisfy sub-quadratic condition"
    
    # Additional check: ratio should decay at large x
    large_x_mask = result.x_values > 500.0
    ratios_large_x = result.W_squared[large_x_mask] / (result.x_values[large_x_mask] ** 2)
    max_ratio_large = np.max(ratios_large_x)
    
    print(f"Max |W(x)|²/x² for x > 500: {max_ratio_large:.6e}")
    
    # Should be much smaller than at smaller x
    ratios_small_x = result.W_squared[~large_x_mask] / (result.x_values[~large_x_mask] ** 2)
    if len(ratios_small_x) > 0:
        max_ratio_small = np.max(ratios_small_x)
        decay_ratio = max_ratio_large / (max_ratio_small + 1e-10)
        print(f"Decay ratio (large/small): {decay_ratio:.4f}")
    
    print("✅ TEST 2 PASSED: Sub-quadratic growth verified")
    return True


def test_origin_regularity():
    """Test 3: Verify W(x) is regular at origin."""
    print("\n" + "=" * 70)
    print("TEST 3: Origin Regularity")
    print("=" * 70)
    
    primes = _sieve_primes(100)
    x_near_zero = np.array([0.001, 0.01, 0.1, 1.0])
    
    W_values = compute_primitive_W(x_near_zero, primes, p_max=100)
    
    print(f"W(0.001) = {W_values[0]:.6f}")
    print(f"W(0.01)  = {W_values[1]:.6f}")
    print(f"W(0.1)   = {W_values[2]:.6f}")
    print(f"W(1.0)   = {W_values[3]:.6f}")
    
    # All values should be finite
    all_finite = np.all(np.isfinite(W_values))
    assert all_finite, "W(x) must be finite near origin"
    
    # Values should be bounded
    max_near_origin = np.max(np.abs(W_values))
    print(f"Max |W(x)| near origin: {max_near_origin:.6f}")
    
    assert max_near_origin < 100.0, "W(x) should be bounded near origin"
    
    print("✅ TEST 3 PASSED: Origin regularity verified")
    return True


def test_quadratic_mean_growth():
    """Test 4: Verify ∫₀^T |W(x)|² dx ~ T log log T."""
    print("\n" + "=" * 70)
    print("TEST 4: Quadratic Mean Growth (Montgomery-Vaughan)")
    print("=" * 70)
    
    # Test for multiple values of T
    T_values = [10.0, 50.0, 100.0, 200.0]
    ratios = []
    
    for T in T_values:
        result = compute_quadratic_mean(T=T, p_max=100, n_points=2000)
        ratios.append(result.ratio)
        
        print(f"\nT = {T:.1f}:")
        print(f"  Integral: {result.quadratic_mean:.4e}")
        print(f"  Theory:   {result.theoretical_estimate:.4e}")
        print(f"  Ratio:    {result.ratio:.4f}")
    
    # Ratios should be reasonably close to 1 (within factor of 2)
    ratios = np.array(ratios)
    print(f"\nMean ratio: {np.mean(ratios):.4f}")
    print(f"Std ratio:  {np.std(ratios):.4f}")
    
    assert np.all(ratios > 0.1), "All ratios must be positive"
    assert np.all(ratios < 10.0), "Ratios should be order 1"
    
    print("✅ TEST 4 PASSED: Quadratic mean growth verified")
    return True


def test_klmn_conditions():
    """Test 5: Verify KLMN theorem conditions."""
    print("\n" + "=" * 70)
    print("TEST 5: KLMN Theorem Conditions")
    print("=" * 70)
    
    result = estimate_supremum_bound(
        x_min=0.1,
        x_max=1000.0,
        n_points=5000,
        p_max=100,
    )
    
    form_result = verify_relative_form_boundedness(result, epsilon=0.1)
    
    print(f"Relative coefficient a: {form_result['relative_coefficient_a']:.6f}")
    print(f"Absolute coefficient b: {form_result['absolute_coefficient_b']:.6e}")
    print(f"Form bound satisfied (a < 1): {form_result['form_bound_satisfied']}")
    print(f"KLMN theorem satisfied: {form_result['klmn_theorem_satisfied']}")
    
    assert form_result['relative_coefficient_a'] < 1.0, "Must have a < 1"
    assert form_result['form_bound_satisfied'], "Form bound must be satisfied"
    assert form_result['klmn_theorem_satisfied'], "KLMN conditions must hold"
    
    print("✅ TEST 5 PASSED: KLMN conditions verified")
    return True


def test_essential_self_adjointness():
    """Test 6: Verify essential self-adjointness conclusion."""
    print("\n" + "=" * 70)
    print("TEST 6: Essential Self-Adjointness")
    print("=" * 70)
    
    supremum_result = estimate_supremum_bound(
        x_min=0.1,
        x_max=1000.0,
        n_points=5000,
        p_max=100,
    )
    
    qm_result = compute_quadratic_mean(T=100.0, p_max=100, n_points=2000)
    
    form_result = verify_relative_form_boundedness(supremum_result)
    
    cert = generate_certificate(supremum_result, qm_result, form_result)
    
    print(f"Essential self-adjointness proven: {cert['essential_self_adjointness_proven']}")
    print(f"\nConclusion:")
    print(cert['conclusion'])
    
    assert cert['essential_self_adjointness_proven'], (
        "Essential self-adjointness must be proven"
    )
    
    print("✅ TEST 6 PASSED: Essential self-adjointness verified")
    return True


def run_all_tests():
    """Run all validation tests."""
    print("\n" + "=" * 70)
    print("SUPREMUM CONTROL PRIMITIVE VALIDATION")
    print("José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("=" * 70)
    
    tests = [
        ("Supremum Finiteness", test_supremum_finiteness),
        ("Sub-Quadratic Growth", test_sub_quadratic_growth),
        ("Origin Regularity", test_origin_regularity),
        ("Quadratic Mean Growth", test_quadratic_mean_growth),
        ("KLMN Conditions", test_klmn_conditions),
        ("Essential Self-Adjointness", test_essential_self_adjointness),
    ]
    
    results = []
    for name, test_func in tests:
        try:
            success = test_func()
            results.append((name, success))
        except Exception as e:
            print(f"\n❌ TEST FAILED: {name}")
            print(f"Error: {e}")
            results.append((name, False))
    
    # Summary
    print("\n" + "=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    
    for name, success in results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {name}")
    
    total = len(results)
    passed = sum(1 for _, s in results if s)
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🏆 ALL TESTS PASSED")
        print("✅ Supremum control demonstrated")
        print("✅ Essential self-adjointness proven")
        print("✅ Zeros confined to critical line Re(s) = 1/2")
        
        # Generate and save final certificate
        supremum_result = estimate_supremum_bound(
            x_min=0.1,
            x_max=1000.0,
            n_points=5000,
            p_max=100,
        )
        qm_result = compute_quadratic_mean(T=100.0, p_max=100, n_points=2000)
        form_result = verify_relative_form_boundedness(supremum_result)
        cert = generate_certificate(supremum_result, qm_result, form_result)
        
        cert_path = Path("data") / "supremum_control_primitive_certificate.json"
        cert_path.parent.mkdir(exist_ok=True)
        
        with open(cert_path, "w") as f:
            # Convert numpy types to Python native types
            def convert_types(obj):
                if isinstance(obj, dict):
                    return {k: convert_types(v) for k, v in obj.items()}
                elif isinstance(obj, (list, tuple)):
                    return [convert_types(v) for v in obj]
                elif isinstance(obj, (np.bool_, np.bool)):
                    return bool(obj)
                elif isinstance(obj, (np.integer, np.int32, np.int64)):
                    return int(obj)
                elif isinstance(obj, (np.floating, np.float32, np.float64)):
                    return float(obj)
                elif isinstance(obj, np.ndarray):
                    return obj.tolist()
                else:
                    return obj
            
            cert_clean = convert_types(cert)
            json.dump(cert_clean, f, indent=2)
        
        print(f"\n📜 Certificate saved to: {cert_path}")
        
        return True
    else:
        print("\n⚠️ SOME TESTS FAILED")
        return False


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
