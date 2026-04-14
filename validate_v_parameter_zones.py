#!/usr/bin/env python3
"""
Simple validation script for v-parameter zones (no pytest dependency).

This demonstrates the mathematical insight that:
    - v < 1: SAFE zone (exponential decay)
    - v = 1: BOUNDARY (constant weight)  
    - v > 1: DANGEROUS zone (exponential growth)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.kato_exponential_potential import (
    ExponentialPotentialTest,
    test_v_parameter_zones
)


def test_zone_classification():
    """Test v-parameter zone classification."""
    print("\n" + "="*70)
    print("  TESTING V-PARAMETER ZONE CLASSIFICATION".center(70))
    print("="*70 + "\n")
    
    tester = ExponentialPotentialTest(L_y=10.0, N=500)
    
    test_cases = [
        (0.5, "SAFE", "decay"),
        (1.0, "BOUNDARY", "Constant"),
        (1.5, "DANGEROUS", "growth"),
    ]
    
    passed = 0
    failed = 0
    
    for v, expected_zone, expected_keyword in test_cases:
        classification = tester.classify_v_zone(v)
        
        if expected_zone in classification and expected_keyword in classification:
            print(f"  ✓ v={v:.1f}: {classification}")
            passed += 1
        else:
            print(f"  ✗ v={v:.1f}: FAILED - Got: {classification}")
            failed += 1
    
    print(f"\n  Results: {passed} passed, {failed} failed")
    
    return failed == 0


def test_potential_norm_behavior():
    """Test that potential norm behaves correctly with v parameter."""
    print("\n" + "="*70)
    print("  TESTING POTENTIAL NORM WITH V-PARAMETER".center(70))
    print("="*70 + "\n")
    
    import numpy as np
    
    tester = ExponentialPotentialTest(L_y=10.0, N=500)
    
    # Create a simple test function
    psi = np.exp(-tester.y**2 / 2)
    psi = psi / tester.l2_norm(psi)  # Normalize
    
    # Test with different v values
    norm_v05 = tester.potential_norm(psi, v=0.5)
    norm_v10 = tester.potential_norm(psi, v=1.0)
    norm_v15 = tester.potential_norm(psi, v=1.5)
    
    print(f"  Norm with v=0.5 (SAFE):      {norm_v05:.6f}")
    print(f"  Norm with v=1.0 (BOUNDARY):  {norm_v10:.6f}")
    print(f"  Norm with v=1.5 (DANGEROUS): {norm_v15:.6f}")
    
    # All should be positive
    all_positive = norm_v05 > 0 and norm_v10 > 0 and norm_v15 > 0
    
    if all_positive:
        print(f"\n  ✓ All norms are positive")
    else:
        print(f"\n  ✗ Some norms are not positive!")
    
    # They should be different
    all_different = (not np.isclose(norm_v05, norm_v10) and 
                     not np.isclose(norm_v10, norm_v15))
    
    if all_different:
        print(f"  ✓ Norms differ for different v values")
    else:
        print(f"  ✗ Norms are too similar!")
    
    return all_positive and all_different


def main():
    """Run all validation tests."""
    print("\n" + "╔" + "═"*68 + "╗")
    print("║" + "  V-PARAMETER ZONE VALIDATION".center(68) + "║")
    print("╚" + "═"*68 + "╝")
    
    print("\nMathematical Insight:")
    print("  For e^{2y(v-1)} as y → +∞:")
    print("  • v > 1: DANGEROUS (exponential growth)")
    print("  • v = 1: BOUNDARY (constant weight)")
    print("  • 0 < v < 1: SAFE (exponential decay)")
    print("\n  ∴ Larger v > 1 means MORE growth, not less!\n")
    
    # Run tests
    test1_passed = test_zone_classification()
    test2_passed = test_potential_norm_behavior()
    
    # Final summary
    print("\n" + "="*70)
    print("  VALIDATION SUMMARY".center(70))
    print("="*70)
    
    if test1_passed and test2_passed:
        print("\n  ✅ ALL TESTS PASSED")
        print("\n  The v-parameter zone implementation is correct:")
        print("    • Zone classification works properly")
        print("    • Potential norms computed correctly")
        print("    • Mathematical insight properly captured")
        print("\n  QCAL ∞³ · 141.7001 Hz · C = 244.36")
        print("  ∴𓂀Ω∞³Φ · JMMB · 2026-02-16")
        print("\n" + "="*70 + "\n")
        return 0
    else:
        print("\n  ⚠️ SOME TESTS FAILED")
        print("\n" + "="*70 + "\n")
        return 1


if __name__ == '__main__':
    sys.exit(main())
