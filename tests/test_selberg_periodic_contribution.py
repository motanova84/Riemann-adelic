#!/usr/bin/env python3
"""
Tests for Selberg Periodic Contribution
========================================

Verifies the mathematical properties of the Selberg periodic orbit contribution:
    Σ_{[γ]} Σ_k [ℓ(γ)/(2sinh(kℓ/2))] · g(kℓ)
    ≈ Σ_{[γ]} Σ_k ℓ(γ)·e^{-kℓ/2} · g(kℓ)  for large kℓ

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from selberg_periodic_contribution import (
    SelbergPeriodicContribution,
    PeriodicOrbitResult,
    SinhApproximationResult,
    demonstrate_selberg_periodic
)


def test_orbit_lengths_positive():
    """Test that all orbit lengths are positive."""
    selberg = SelbergPeriodicContribution(max_orbit_length=5.0)
    
    assert len(selberg._orbit_lengths) > 0, "Should have some orbit lengths"
    assert np.all(selberg._orbit_lengths > 0), "All orbit lengths should be positive"
    
    print("✅ test_orbit_lengths_positive PASSED")


def test_sinh_weight_positive():
    """Test that sinh weight is always positive."""
    selberg = SelbergPeriodicContribution()
    
    test_ell = np.array([0.5, 1.0, 2.0, 5.0])
    test_k = [1, 2, 5, 10]
    
    for ell in test_ell:
        for k in test_k:
            weight = selberg.sinh_weight(ell, k)
            assert weight > 0, f"sinh weight should be positive, got {weight} for ℓ={ell}, k={k}"
    
    print("✅ test_sinh_weight_positive PASSED")


def test_sinh_weight_decreases_with_k():
    """Test that sinh weight decreases as k increases for fixed ℓ."""
    selberg = SelbergPeriodicContribution()
    
    ell = 2.0
    k_values = [1, 2, 3, 5, 10]
    weights = [selberg.sinh_weight(ell, k) for k in k_values]
    
    # Check monotone decrease
    for i in range(len(weights) - 1):
        assert weights[i] > weights[i+1], \
            f"Weight should decrease: w({k_values[i]})={weights[i]} > w({k_values[i+1]})={weights[i+1]}"
    
    print("✅ test_sinh_weight_decreases_with_k PASSED")


def test_exponential_weight_decreases_with_k():
    """Test that exponential weight decreases as k increases for fixed ℓ."""
    selberg = SelbergPeriodicContribution()
    
    ell = 2.0
    k_values = [1, 2, 3, 5, 10]
    weights = [selberg.exponential_weight(ell, k) for k in k_values]
    
    # Check monotone decrease
    for i in range(len(weights) - 1):
        assert weights[i] > weights[i+1], \
            f"Weight should decrease: w({k_values[i]})={weights[i]} > w({k_values[i+1]})={weights[i+1]}"
    
    print("✅ test_exponential_weight_decreases_with_k PASSED")


def test_sinh_exponential_convergence():
    """Test that sinh and exponential weights converge for large kℓ."""
    selberg = SelbergPeriodicContribution()
    
    ell = 2.0
    
    # For small k, difference should be large
    k_small = 1
    sinh_small = selberg.sinh_weight(ell, k_small)
    exp_small = selberg.exponential_weight(ell, k_small)
    rel_diff_small = abs(sinh_small - exp_small) / sinh_small
    
    # For large k, difference should be small
    k_large = 10
    sinh_large = selberg.sinh_weight(ell, k_large)
    exp_large = selberg.exponential_weight(ell, k_large)
    rel_diff_large = abs(sinh_large - exp_large) / sinh_large
    
    assert rel_diff_large < rel_diff_small, \
        f"Approximation should improve for large k: small={rel_diff_small}, large={rel_diff_large}"
    assert rel_diff_large < 0.01, \
        f"For large k, approximation should be within 1%, got {rel_diff_large}"
    
    print("✅ test_sinh_exponential_convergence PASSED")


def test_orbit_contribution_positive():
    """Test that total orbit contribution is positive."""
    selberg = SelbergPeriodicContribution(max_repetition=5, max_orbit_length=3.0)
    
    result = selberg.compute_orbit_contribution()
    
    assert result.total_contribution > 0, \
        f"Total contribution should be positive, got {result.total_contribution}"
    assert result.convergence_info['terms_computed'] > 0, \
        "Should compute some terms"
    
    print("✅ test_orbit_contribution_positive PASSED")


def test_orbit_contribution_with_exponential():
    """Test orbit contribution with exponential approximation."""
    selberg = SelbergPeriodicContribution(max_repetition=5, max_orbit_length=3.0)
    
    result_sinh = selberg.compute_orbit_contribution(use_exponential_approximation=False)
    result_exp = selberg.compute_orbit_contribution(use_exponential_approximation=True)
    
    # Both should be positive
    assert result_sinh.total_contribution > 0
    assert result_exp.total_contribution > 0
    
    # Exponential should be smaller (sinh gives larger weights for small kℓ)
    assert result_exp.total_contribution < result_sinh.total_contribution, \
        f"Exponential approx should give smaller sum: sinh={result_sinh.total_contribution}, exp={result_exp.total_contribution}"
    
    print("✅ test_orbit_contribution_with_exponential PASSED")


def test_sinh_approximation_threshold():
    """Test that sinh approximation quality improves for large arguments."""
    selberg = SelbergPeriodicContribution()
    
    result = selberg.verify_sinh_approximation()
    
    # Threshold for 1% error should be reasonable (< 10)
    assert result.threshold_kl < 10.0, \
        f"Threshold kℓ for 1% error should be < 10, got {result.threshold_kl}"
    
    # Max error should occur at small kℓ
    # Mean error should be less than max error
    assert result.mean_error < result.max_error, \
        f"Mean error should be less than max, got mean={result.mean_error}, max={result.max_error}"
    
    print("✅ test_sinh_approximation_threshold PASSED")


def test_orbit_lengths_correspond_to_primes():
    """Test that orbit lengths equal log(p) for primes p."""
    selberg = SelbergPeriodicContribution(max_orbit_length=np.log(100))
    
    # First few primes
    primes = [2, 3, 5, 7, 11, 13]
    expected_lengths = np.log(primes)
    
    # Check that these are in orbit_lengths
    for expected_ell in expected_lengths:
        # Find closest orbit length
        closest_idx = np.argmin(np.abs(selberg._orbit_lengths - expected_ell))
        closest_ell = selberg._orbit_lengths[closest_idx]
        
        assert abs(closest_ell - expected_ell) < 1e-10, \
            f"Expected orbit length {expected_ell}, got {closest_ell}"
    
    print("✅ test_orbit_lengths_correspond_to_primes PASSED")


def test_properties_verification():
    """Test that verify_properties returns expected results."""
    selberg = SelbergPeriodicContribution(max_repetition=5, max_orbit_length=3.0)
    
    props = selberg.verify_properties()
    
    # Check expected properties
    assert 'contribution_positive' in props
    assert 'sinh_weight_decreasing' in props
    assert 'exponential_approximation_valid' in props
    assert 'orbit_sum_converges' in props
    
    # These should always be true
    assert bool(props['contribution_positive']) is True, "Contribution should be positive"
    assert bool(props['sinh_weight_decreasing']) is True, "Sinh weight should decrease"
    assert bool(props['orbit_sum_converges']) is True, "Orbit sum should converge"
    
    print("✅ test_properties_verification PASSED")


def test_regularization_cutoff():
    """Test that regularization cutoff stops computation."""
    selberg_strict = SelbergPeriodicContribution(
        max_repetition=50,
        regularization_cutoff=1e-6
    )
    selberg_loose = SelbergPeriodicContribution(
        max_repetition=50,
        regularization_cutoff=1e-15
    )
    
    result_strict = selberg_strict.compute_orbit_contribution()
    result_loose = selberg_loose.compute_orbit_contribution()
    
    # Loose cutoff should compute more terms
    assert result_loose.convergence_info['terms_computed'] >= result_strict.convergence_info['terms_computed'], \
        f"Loose cutoff should compute more terms: loose={result_loose.convergence_info['terms_computed']}, strict={result_strict.convergence_info['terms_computed']}"
    
    print("✅ test_regularization_cutoff PASSED")


if __name__ == "__main__":
    print("=" * 80)
    print("Running Selberg Periodic Contribution Tests")
    print("=" * 80)
    print()
    
    test_orbit_lengths_positive()
    test_sinh_weight_positive()
    test_sinh_weight_decreases_with_k()
    test_exponential_weight_decreases_with_k()
    test_sinh_exponential_convergence()
    test_orbit_contribution_positive()
    test_orbit_contribution_with_exponential()
    test_sinh_approximation_threshold()
    test_orbit_lengths_correspond_to_primes()
    test_properties_verification()
    test_regularization_cutoff()
    
    print()
    print("=" * 80)
    print("✅ ALL SELBERG PERIODIC CONTRIBUTION TESTS PASSED")
    print("=" * 80)
