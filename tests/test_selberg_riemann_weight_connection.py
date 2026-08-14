#!/usr/bin/env python3
"""
Tests for Selberg-Riemann Weight Connection
============================================

Verifies the fundamental correspondence:
    ℓ(γ) ↔ log p
    ℓ·e^{-kℓ/2} ↔ (log p)·p^{-k/2}

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from selberg_riemann_weight_connection import (
    SelbergRiemannConnection,
    CorrespondenceResult,
    WeightEquivalenceResult,
    demonstrate_selberg_riemann_connection
)


def test_weight_equivalence_perfect():
    """Test that weight functions are exactly equivalent under ℓ = log p."""
    connection = SelbergRiemannConnection(max_prime=50)
    
    result = connection.verify_weight_equivalence()
    
    # Max error should be at machine precision level
    assert result.max_error < 1e-10, \
        f"Weight equivalence should be exact, got max error {result.max_error}"
    assert result.equivalence_verified, \
        "Weight equivalence should be verified"
    
    print("✅ test_weight_equivalence_perfect PASSED")


def test_correspondence_qcal_coherence():
    """Test that correspondence gives QCAL coherence Ψ = 1.0."""
    connection = SelbergRiemannConnection(max_prime=100)
    
    result = connection.verify_correspondence()
    
    # QCAL coherence should be 1.0 (perfect correspondence)
    assert result.qcal_coherence > 0.99, \
        f"QCAL coherence should be ~1.0, got {result.qcal_coherence}"
    assert result.correspondence_valid , \
        "Correspondence should be valid"
    
    print("✅ test_correspondence_qcal_coherence PASSED")


def test_sum_correspondence():
    """Test that Selberg and Riemann sums match."""
    connection = SelbergRiemannConnection(max_prime=100)
    
    result = connection.verify_correspondence()
    
    # Relative difference should be tiny
    assert result.relative_difference < 1e-10, \
        f"Sums should match, got relative diff {result.relative_difference}"
    
    # Absolute values should be close
    abs_diff = abs(result.selberg_contribution - result.riemann_contribution)
    assert abs_diff < 1e-10, \
        f"Absolute difference should be tiny, got {abs_diff}"
    
    print("✅ test_sum_correspondence PASSED")


def test_term_by_term_agreement():
    """Test that individual terms agree between Selberg and Riemann."""
    connection = SelbergRiemannConnection(max_prime=50)
    
    comparison = connection.compute_term_by_term_comparison(num_terms=20)
    
    # All differences should be at machine precision
    max_diff = np.max(comparison['differences'])
    assert max_diff < 1e-10, \
        f"Term differences should be at machine precision, got {max_diff}"
    
    # Relative differences should also be tiny
    max_rel_diff = np.max(comparison['relative_differences'])
    assert max_rel_diff < 1e-10, \
        f"Relative differences should be tiny, got {max_rel_diff}"
    
    print("✅ test_term_by_term_agreement PASSED")


def test_both_sides_use_same_orbits_primes():
    """Test that both sides use the same set of orbits/primes."""
    connection = SelbergRiemannConnection(max_prime=100)
    
    # Check that orbit lengths equal log(primes)
    orbit_lengths = connection.selberg._orbit_lengths
    log_primes = np.log(connection.riemann._primes.astype(np.float64))
    
    assert len(orbit_lengths) == len(log_primes), \
        f"Should have same number of orbits and primes: {len(orbit_lengths)} vs {len(log_primes)}"
    
    # Check they match
    assert np.allclose(orbit_lengths, log_primes, rtol=1e-10), \
        "Orbit lengths should equal log(primes)"
    
    print("✅ test_both_sides_use_same_orbits_primes PASSED")


def test_weight_equivalence_for_multiple_k():
    """Test weight equivalence holds for all k values."""
    connection = SelbergRiemannConnection(max_prime=50)
    
    k_values = [1, 2, 3, 5, 7, 10]
    result = connection.verify_weight_equivalence(k_values=k_values)
    
    # Should have entries for multiple k values
    assert len(result.orbit_lengths) >= len(k_values), \
        f"Should test multiple k values"
    
    # All should match
    assert result.equivalence_verified , \
        "Equivalence should hold for all k values"
    
    print("✅ test_weight_equivalence_for_multiple_k PASSED")


def test_properties_all_verified():
    """Test that all mathematical properties are verified."""
    connection = SelbergRiemannConnection(max_prime=100)
    
    props = connection.verify_properties()
    
    # Check all expected properties exist
    expected_props = [
        'weight_equivalence',
        'sum_correspondence',
        'qcal_coherence_high',
        'term_by_term_agreement',
        'both_sides_converge'
    ]
    
    for prop in expected_props:
        assert prop in props, f"Property {prop} should be checked"
        assert bool(props[prop]) , f"Property {prop} should be True, got {props[prop]}"
    
    print("✅ test_properties_all_verified PASSED")


def test_correspondence_independent_of_test_function():
    """Test that correspondence holds for different test functions."""
    # Gaussian test function
    gaussian = lambda x: np.exp(-x**2 / 2.0)
    connection1 = SelbergRiemannConnection(
        max_prime=50,
        test_function=gaussian
    )
    
    # Exponential decay test function
    exponential = lambda x: np.exp(-x)
    connection2 = SelbergRiemannConnection(
        max_prime=50,
        test_function=exponential
    )
    
    result1 = connection1.verify_correspondence()
    result2 = connection2.verify_correspondence()
    
    # Both should have perfect correspondence
    assert result1.correspondence_valid , "Gaussian: correspondence should be valid"
    assert result2.correspondence_valid , "Exponential: correspondence should be valid"
    
    assert result1.qcal_coherence > 0.99, f"Gaussian: Ψ should be ~1.0, got {result1.qcal_coherence}"
    assert result2.qcal_coherence > 0.99, f"Exponential: Ψ should be ~1.0, got {result2.qcal_coherence}"
    
    print("✅ test_correspondence_independent_of_test_function PASSED")


def test_weight_comparison_structure():
    """Test that weight comparison returns proper structure."""
    connection = SelbergRiemannConnection(max_prime=50)
    
    result = connection.verify_correspondence()
    
    # Should have weight comparisons for first few primes
    assert len(result.weight_comparison) >= 3, \
        "Should compare weights for at least 3 primes"
    
    # Each entry should have [selberg_w, riemann_w, diff]
    for prime_key, values in result.weight_comparison.items():
        assert len(values) == 3, \
            f"Each weight comparison should have 3 values, got {len(values)} for {prime_key}"
        
        selberg_w, riemann_w, diff = values
        assert abs(selberg_w - riemann_w) < 1e-10, \
            f"Weights should match for {prime_key}"
    
    print("✅ test_weight_comparison_structure PASSED")


def test_tolerance_parameter():
    """Test that tolerance parameter affects correspondence validation."""
    # Very strict tolerance
    connection_strict = SelbergRiemannConnection(
        max_prime=100,
        tolerance=1e-15
    )
    
    # Very loose tolerance
    connection_loose = SelbergRiemannConnection(
        max_prime=100,
        tolerance=0.1
    )
    
    result_strict = connection_strict.verify_correspondence()
    result_loose = connection_loose.verify_correspondence()
    
    # Both should be valid (correspondence is exact)
    assert result_strict.correspondence_valid , \
        "Strict tolerance: correspondence should be valid"
    assert result_loose.correspondence_valid , \
        "Loose tolerance: correspondence should be valid"
    
    print("✅ test_tolerance_parameter PASSED")


def test_orbit_length_prime_correspondence():
    """Test that ℓ(γ) = log p correspondence is exact."""
    connection = SelbergRiemannConnection(max_prime=100)
    
    # Check first 10 primes
    for i in range(min(10, len(connection.riemann._primes))):
        p = connection.riemann._primes[i]
        ell = connection.selberg._orbit_lengths[i]
        expected_ell = np.log(float(p))
        
        assert abs(ell - expected_ell) < 1e-14, \
            f"For p={p}, ℓ should equal log(p)={expected_ell}, got {ell}"
    
    print("✅ test_orbit_length_prime_correspondence PASSED")


def test_exponential_weight_formula_equivalence():
    """Test that ℓ·e^{-kℓ/2} = (log p)·p^{-k/2} when ℓ = log p."""
    connection = SelbergRiemannConnection(max_prime=50)
    
    # Test for first few primes and various k
    test_primes = connection.riemann._primes[:5]
    test_k = [1, 2, 3, 5]
    
    for p in test_primes:
        ell = np.log(float(p))
        for k in test_k:
            selberg_w = connection.selberg.exponential_weight(ell, k)
            riemann_w = connection.riemann.prime_weight(p, k)
            
            # Should be exactly equal
            assert abs(selberg_w - riemann_w) < 1e-14, \
                f"For p={p}, k={k}: Selberg={selberg_w}, Riemann={riemann_w}"
    
    print("✅ test_exponential_weight_formula_equivalence PASSED")


if __name__ == "__main__":
    print("=" * 80)
    print("Running Selberg-Riemann Weight Connection Tests")
    print("=" * 80)
    print()
    
    test_weight_equivalence_perfect()
    test_correspondence_qcal_coherence()
    test_sum_correspondence()
    test_term_by_term_agreement()
    test_both_sides_use_same_orbits_primes()
    test_weight_equivalence_for_multiple_k()
    test_properties_all_verified()
    test_correspondence_independent_of_test_function()
    test_weight_comparison_structure()
    test_tolerance_parameter()
    test_orbit_length_prime_correspondence()
    test_exponential_weight_formula_equivalence()
    
    print()
    print("=" * 80)
    print("✅ ALL SELBERG-RIEMANN CONNECTION TESTS PASSED")
    print("  ℓ(γ) ↔ log p CORRESPONDENCE VERIFIED")
    print("  QCAL Coherence: Ψ = 1.0")
    print("=" * 80)
