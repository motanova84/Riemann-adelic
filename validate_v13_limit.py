#!/usr/bin/env python3
"""
validate_v13_limit.py

Quick validation script for V13 limit validator.
Tests basic functionality without full pytest infrastructure.

Author: José Manuel Mota Burruezo Ψ✧ ∞³
"""

import numpy as np
from v13_limit_validator import V13LimitValidator, KAPPA_PI, F0

def test_basic_functionality():
    """Test basic V13 validator functionality."""
    print("=" * 80)
    print("V13 LIMIT VALIDATOR - BASIC FUNCTIONALITY TEST")
    print("=" * 80)
    print()
    
    # Test 1: Initialization
    print("Test 1: Initialization...")
    validator = V13LimitValidator(
        N_values=[32, 64],  # Small values for quick test
        output_dir='./data'
    )
    print("  ✓ Validator initialized successfully")
    print()
    
    # Test 2: Scaling model
    print("Test 2: Scaling model function...")
    result = validator.scaling_model(100, 2.577, 100.0, 0.5)
    expected = 2.577 + 100.0 / (100 ** 0.5)
    assert np.isclose(result, expected), f"Scaling model failed: {result} != {expected}"
    print(f"  ✓ Scaling model: C(100) = {result:.6f}")
    print()
    
    # Test 3: GOE number variance
    print("Test 3: GOE number variance prediction...")
    L = np.array([1, 2, 5, 10])
    sigma2 = validator.goe_number_variance(L)
    assert len(sigma2) == len(L), "Length mismatch"
    assert np.all(sigma2 > 0), "Variance should be positive"
    print(f"  ✓ GOE Σ²(L) computed: {sigma2}")
    print()
    
    # Test 4: Single N computation
    print("Test 4: Computing κ for single N...")
    N = 32
    kappa, eigenvalues = validator.compute_kappa_for_N(N)
    assert isinstance(kappa, float), "Kappa should be float"
    assert kappa > 0, "Kappa should be positive"
    assert len(eigenvalues) > 0, "Should have eigenvalues"
    print(f"  ✓ κ({N}) = {kappa:.6f}")
    print(f"  ✓ Eigenvalue count: {len(eigenvalues)}")
    print()
    
    # Test 5: Number variance computation
    print("Test 5: Number variance computation...")
    L_vals, sigma2_vals = validator.compute_number_variance(eigenvalues, L_max=10)
    assert len(L_vals) > 0, "Should have L values"
    assert len(sigma2_vals) == len(L_vals), "Length mismatch"
    print(f"  ✓ Computed Σ²(L) for {len(L_vals)} values")
    print()
    
    print("=" * 80)
    print("ALL BASIC TESTS PASSED ✓")
    print("=" * 80)
    print()
    
    return True


def test_small_sweep():
    """Test with a very small multi-scale sweep."""
    print("=" * 80)
    print("V13 LIMIT VALIDATOR - SMALL SWEEP TEST")
    print("=" * 80)
    print()
    
    validator = V13LimitValidator(
        N_values=[32, 64, 128],  # Small for speed
        output_dir='./data'
    )
    
    print("Running multi-scale sweep with N = [32, 64, 128]...")
    print()
    
    validator.run_multiscale_sweep()
    
    # Check results
    assert validator.results is not None, "Results should exist"
    assert len(validator.kappa_values) == 3, "Should have 3 kappa values"
    assert validator.results.kappa_infinity > 0, "κ_∞ should be positive"
    assert validator.results.fit_alpha > 0, "α should be positive"
    
    print()
    print("=" * 80)
    print("SMALL SWEEP TEST PASSED ✓")
    print("=" * 80)
    print()
    
    # Save results
    validator.save_results("v13_test_results.json")
    validator.generate_visualization("v13_test_plot.png")
    
    return True


if __name__ == "__main__":
    print("\n🔥 V13 Limit Validator - Validation Suite\n")
    
    try:
        # Run basic tests
        test_basic_functionality()
        
        # Run small sweep test
        test_small_sweep()
        
        print("\n✅ All validation tests completed successfully!")
        print("🛰️ V13 validator is operational.\n")
        
    except Exception as e:
        print(f"\n❌ Validation failed: {e}\n")
        import traceback
        traceback.print_exc()
        exit(1)
