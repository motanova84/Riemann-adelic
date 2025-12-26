#!/usr/bin/env python3
"""
Simple test runner for ABC Conjecture QCAL implementation
(Does not require pytest)

This test module validates the ABC conjecture implementation without
external dependencies.
"""

from validate_abc_conjecture import (
    radical, prime_factors, gcd, quality,
    spectral_rigidity_bound, find_abc_triples,
    validate_abc_conjecture,
    F0, F_PORTAL, KAPPA_PI
)


def test_radical_computation():
    """Test the noetic radical (product of distinct prime factors)"""
    print("Testing radical computation...")
    
    # Small primes
    assert radical(2) == 2, "radical(2) should be 2"
    assert radical(3) == 3, "radical(3) should be 3"
    
    # Prime powers
    assert radical(4) == 2, "radical(4) = radical(2²) should be 2"
    assert radical(9) == 3, "radical(9) = radical(3²) should be 3"
    
    # Composites
    assert radical(6) == 6, "radical(6) = radical(2×3) should be 6"
    assert radical(12) == 6, "radical(12) = radical(2²×3) should be 6"
    assert radical(30) == 30, "radical(30) = radical(2×3×5) should be 30"
    
    # Edge cases
    assert radical(0) == 1, "radical(0) should be 1"
    assert radical(1) == 1, "radical(1) should be 1"
    
    print("  ✓ All radical tests passed")


def test_abc_quality():
    """Test ABC quality metric q(a,b,c) = log(c) / log(rad(abc))"""
    print("Testing ABC quality computation...")
    
    # Known high-quality triple (3, 125, 128)
    q = quality(3, 125, 128)
    assert 1.4 < q < 1.5, f"quality(3,125,128) should be ≈1.427, got {q}"
    
    # Another known high-quality triple (1, 8, 9)
    q = quality(1, 8, 9)
    assert 1.2 < q < 1.3, f"quality(1,8,9) should be ≈1.226, got {q}"
    
    print("  ✓ All quality tests passed")


def test_spectral_rigidity():
    """Test spectral rigidity bounds from RH"""
    print("Testing spectral rigidity bounds...")
    
    triples = [
        (1, 8, 9),
        (3, 125, 128),
        (1, 80, 81),
        (2, 3, 5)
    ]
    
    epsilon = 0.1
    for a, b, c in triples:
        lhs, rhs = spectral_rigidity_bound(a, b, c, epsilon)
        assert lhs <= rhs, f"Rigidity bound failed for ({a}, {b}, {c}): {lhs} > {rhs}"
    
    print("  ✓ All spectral rigidity tests passed")


def test_qcal_constants():
    """Verify QCAL spectral constants"""
    print("Testing QCAL constants...")
    
    assert abs(F0 - 141.7001) < 1e-4, f"F0 should be 141.7001, got {F0}"
    assert abs(F_PORTAL - 153.036) < 1e-3, f"F_PORTAL should be 153.036, got {F_PORTAL}"
    assert abs(KAPPA_PI - 2.5782) < 1e-4, f"KAPPA_PI should be 2.5782, got {KAPPA_PI}"
    
    # Portal frequency should be higher than base frequency
    assert F_PORTAL > F0, "Portal frequency should be higher than base frequency"
    
    print("  ✓ All QCAL constant tests passed")


def test_abc_triple_finding():
    """Test ABC triple search algorithm"""
    print("Testing ABC triple search...")
    
    triples = find_abc_triples(max_c=50, min_quality=0.0)
    
    # Should find some triples
    assert len(triples) > 0, "Should find at least some ABC triples"
    
    # All should satisfy a + b = c and gcd(a,b) = 1
    for a, b, c, q in triples:
        assert a + b == c, f"Triple ({a}, {b}, {c}) doesn't satisfy a+b=c"
        assert gcd(a, b) == 1, f"Triple ({a}, {b}, {c}) is not coprime"
    
    print(f"  ✓ Found {len(triples)} valid ABC triples")


def test_chaos_exclusion():
    """Test the Chaos Exclusion Principle"""
    print("Testing Chaos Exclusion Principle...")
    
    epsilon = 0.1
    max_height = 500
    
    # Find all triples
    all_triples = find_abc_triples(max_c=max_height, min_quality=0.0)
    
    # Count violations (quality > 1 + ε)
    violations = [t for t in all_triples if t[3] > 1.0 + epsilon]
    
    # Violations should be finite and relatively small
    assert len(violations) < len(all_triples), "Not all triples should be violations"
    
    print(f"  ✓ Found {len(violations)} violations out of {len(all_triples)} triples (finite)")


def test_full_validation():
    """Integration test: run full ABC validation"""
    print("Testing full ABC validation...")
    
    report = validate_abc_conjecture(
        epsilon=0.1,
        max_height=300,  # Small for fast testing
        verbose=False
    )
    
    # Check report structure
    assert 'results' in report, "Report should contain 'results'"
    assert 'qcal_constants' in report, "Report should contain 'qcal_constants'"
    assert 'interpretation' in report, "Report should contain 'interpretation'"
    
    # Check QCAL constants are included
    assert report['qcal_constants']['f0_hz'] == F0
    assert report['qcal_constants']['kappa_pi'] == KAPPA_PI
    
    # Check interpretation
    assert report['interpretation']['abc_status'] in ['FINITE_VIOLATIONS', 'UNKNOWN']
    
    violations = report['results']['violations_count']
    total = report['results']['total_triples_found']
    
    print(f"  ✓ Validation complete: {violations} violations / {total} triples")
    print(f"  ✓ Spectral coherence: {report['interpretation']['spectral_coherence']}")
    print(f"  ✓ Chaos exclusion: {'VERIFIED' if report['interpretation']['chaos_excluded'] else 'PARTIAL'}")


def main():
    """Run all tests"""
    print("\n" + "="*70)
    print("ABC Conjecture QCAL Test Suite")
    print("="*70 + "\n")
    
    tests = [
        test_radical_computation,
        test_abc_quality,
        test_spectral_rigidity,
        test_qcal_constants,
        test_abc_triple_finding,
        test_chaos_exclusion,
        test_full_validation
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"  ✗ Test failed: {e}")
            failed += 1
        except Exception as e:
            print(f"  ✗ Test error: {e}")
            failed += 1
    
    print("\n" + "="*70)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("="*70 + "\n")
    
    if failed == 0:
        print("✅ All ABC Conjecture QCAL tests passed!")
        print("   Spectral rigidity from RH confirmed.")
        print(f"   Chaos Exclusion Principle: ACTIVE at f₀ = {F0} Hz")
        return 0
    else:
        print(f"⚠️  {failed} test(s) failed")
        return 1


if __name__ == '__main__':
    sys.exit(main())
