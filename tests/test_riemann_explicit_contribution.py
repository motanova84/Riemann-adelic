#!/usr/bin/env python3
"""
Tests for Riemann Explicit Contribution
========================================

Verifies the mathematical properties of the Riemann explicit formula contribution:
    Σ_p Σ_k (log p) · p^{-k/2} · g(k log p)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_explicit_contribution import (
    RiemannExplicitContribution,
    PrimeContributionResult,
    VonMangoldtResult,
    demonstrate_riemann_explicit
)


def test_primes_generation():
    """Test that prime generation works correctly."""
    riemann = RiemannExplicitContribution(max_prime=100)
    
    assert len(riemann._primes) > 0, "Should have some primes"
    assert riemann._primes[0] == 2, "First prime should be 2"
    assert riemann._primes[1] == 3, "Second prime should be 3"
    assert riemann._primes[2] == 5, "Third prime should be 5"
    
    # Check all are prime
    for p in riemann._primes[:10]:
        assert p > 1, f"Prime {p} should be > 1"
        # Simple primality check
        for d in range(2, int(np.sqrt(p)) + 1):
            assert p % d != 0, f"{p} should be prime but divisible by {d}"
    
    print("✅ test_primes_generation PASSED")


def test_prime_weight_positive():
    """Test that prime weight is always positive."""
    riemann = RiemannExplicitContribution(max_prime=50)
    
    for p in riemann._primes[:5]:
        for k in [1, 2, 3, 5]:
            weight = riemann.prime_weight(p, k)
            assert weight > 0, f"Prime weight should be positive, got {weight} for p={p}, k={k}"
    
    print("✅ test_prime_weight_positive PASSED")


def test_prime_weight_decreases_with_k():
    """Test that prime weight decreases as k increases for fixed p."""
    riemann = RiemannExplicitContribution()
    
    p = 7
    k_values = [1, 2, 3, 5, 10]
    weights = [riemann.prime_weight(p, k) for k in k_values]
    
    # Check monotone decrease
    for i in range(len(weights) - 1):
        assert weights[i] > weights[i+1], \
            f"Weight should decrease: w({k_values[i]})={weights[i]} > w({k_values[i+1]})={weights[i+1]}"
    
    print("✅ test_prime_weight_decreases_with_k PASSED")


def test_prime_weight_formula():
    """Test that prime weight matches formula (log p) / p^{k/2}."""
    riemann = RiemannExplicitContribution()
    
    p = 5
    k = 2
    
    weight = riemann.prime_weight(p, k)
    expected = np.log(float(p)) / (p ** (k / 2.0))
    
    assert abs(weight - expected) < 1e-10, \
        f"Weight should match formula: got {weight}, expected {expected}"
    
    print("✅ test_prime_weight_formula PASSED")


def test_von_mangoldt_for_primes():
    """Test that von Mangoldt function equals log p for primes."""
    riemann = RiemannExplicitContribution(max_prime=50)
    
    test_primes = [2, 3, 5, 7, 11]
    for p in test_primes:
        lambda_p = riemann.von_mangoldt(p)
        expected = np.log(float(p))
        
        assert abs(lambda_p - expected) < 1e-10, \
            f"Λ({p}) should be log({p})={expected}, got {lambda_p}"
    
    print("✅ test_von_mangoldt_for_primes PASSED")


def test_von_mangoldt_for_prime_powers():
    """Test that von Mangoldt function equals log p for prime powers."""
    riemann = RiemannExplicitContribution(max_prime=50)
    
    # Test prime powers
    test_cases = [
        (4, 2),   # 4 = 2^2, Λ(4) = log 2
        (8, 2),   # 8 = 2^3, Λ(8) = log 2
        (9, 3),   # 9 = 3^2, Λ(9) = log 3
        (27, 3),  # 27 = 3^3, Λ(27) = log 3
    ]
    
    for n, p in test_cases:
        lambda_n = riemann.von_mangoldt(n)
        expected = np.log(float(p))
        
        assert abs(lambda_n - expected) < 1e-10, \
            f"Λ({n}) should be log({p})={expected}, got {lambda_n}"
    
    print("✅ test_von_mangoldt_for_prime_powers PASSED")


def test_von_mangoldt_for_non_prime_powers():
    """Test that von Mangoldt function equals 0 for non-prime-powers."""
    riemann = RiemannExplicitContribution(max_prime=50)
    
    # Test non-prime-powers
    test_values = [1, 6, 10, 12, 15, 20, 21]
    
    for n in test_values:
        lambda_n = riemann.von_mangoldt(n)
        
        assert abs(lambda_n) < 1e-10, \
            f"Λ({n}) should be 0, got {lambda_n}"
    
    print("✅ test_von_mangoldt_for_non_prime_powers PASSED")


def test_prime_contribution_positive():
    """Test that total prime contribution is positive."""
    riemann = RiemannExplicitContribution(max_power=5, max_prime=50)
    
    result = riemann.compute_prime_contribution()
    
    assert result.total_contribution > 0, \
        f"Total contribution should be positive, got {result.total_contribution}"
    assert result.convergence_info['terms_computed'] > 0, \
        "Should compute some terms"
    
    print("✅ test_prime_contribution_positive PASSED")


def test_prime_contribution_convergence():
    """Test that prime contribution converges with more terms."""
    riemann_small = RiemannExplicitContribution(max_power=3, max_prime=20)
    riemann_large = RiemannExplicitContribution(max_power=10, max_prime=100)
    
    result_small = riemann_small.compute_prime_contribution()
    result_large = riemann_large.compute_prime_contribution()
    
    # More terms should give larger sum (all terms are positive)
    assert result_large.total_contribution >= result_small.total_contribution, \
        f"Larger computation should give >= sum: small={result_small.total_contribution}, large={result_large.total_contribution}"
    
    print("✅ test_prime_contribution_convergence PASSED")


def test_von_mangoldt_array():
    """Test von Mangoldt array computation."""
    riemann = RiemannExplicitContribution(max_prime=20)
    
    result = riemann.compute_von_mangoldt_array(n_max=20)
    
    assert len(result.n_values) == 20
    assert len(result.lambda_values) == 20
    
    # Check specific values
    # Λ(1) = 0 (index 0)
    # Λ(2) = log(2) > 0 (index 1)
    assert abs(result.lambda_values[0]) < 1e-10, "Λ(1) should be 0"
    assert result.lambda_values[1] > 0, "Λ(2) should be non-zero (log 2)"
    
    # All values should be non-negative
    assert np.all(result.lambda_values >= 0), "All Λ(n) should be non-negative"
    
    print("✅ test_von_mangoldt_array PASSED")


def test_properties_verification():
    """Test that verify_properties returns expected results."""
    riemann = RiemannExplicitContribution(max_power=5, max_prime=50)
    
    props = riemann.verify_properties()
    
    # Check expected properties
    assert 'contribution_positive' in props
    assert 'prime_weight_decreasing' in props
    assert 'von_mangoldt_nonnegative' in props
    assert 'prime_sum_converges' in props
    assert 'von_mangoldt_correct_for_primes' in props
    
    # These should all be true
    assert bool(props['contribution_positive']) is True
    assert bool(props['prime_weight_decreasing']) is True
    assert bool(props['von_mangoldt_nonnegative']) is True
    assert bool(props['prime_sum_converges']) is True
    assert bool(props['von_mangoldt_correct_for_primes']) is True
    
    print("✅ test_properties_verification PASSED")


def test_regularization_cutoff():
    """Test that regularization cutoff stops computation."""
    riemann_strict = RiemannExplicitContribution(
        max_power=50,
        regularization_cutoff=1e-6
    )
    riemann_loose = RiemannExplicitContribution(
        max_power=50,
        regularization_cutoff=1e-15
    )
    
    result_strict = riemann_strict.compute_prime_contribution()
    result_loose = riemann_loose.compute_prime_contribution()
    
    # Loose cutoff should compute more or equal terms
    assert result_loose.convergence_info['terms_computed'] >= result_strict.convergence_info['terms_computed'], \
        f"Loose cutoff should compute >= terms: loose={result_loose.convergence_info['terms_computed']}, strict={result_strict.convergence_info['terms_computed']}"
    
    print("✅ test_regularization_cutoff PASSED")


def test_prime_weight_exponential_form():
    """Test that prime weight matches exponential form (log p)·p^{-k/2} = (log p)·e^{-k·log(p)/2}."""
    riemann = RiemannExplicitContribution()
    
    p = 7
    k = 3
    
    weight = riemann.prime_weight(p, k)
    
    # Alternative formula using exponential
    log_p = np.log(float(p))
    weight_exp = log_p * np.exp(-k * log_p / 2.0)
    
    assert abs(weight - weight_exp) < 1e-10, \
        f"Weight formulas should match: p^{{-k/2}}={weight}, exp form={weight_exp}"
    
    print("✅ test_prime_weight_exponential_form PASSED")


if __name__ == "__main__":
    print("=" * 80)
    print("Running Riemann Explicit Contribution Tests")
    print("=" * 80)
    print()
    
    test_primes_generation()
    test_prime_weight_positive()
    test_prime_weight_decreases_with_k()
    test_prime_weight_formula()
    test_von_mangoldt_for_primes()
    test_von_mangoldt_for_prime_powers()
    test_von_mangoldt_for_non_prime_powers()
    test_prime_contribution_positive()
    test_prime_contribution_convergence()
    test_von_mangoldt_array()
    test_properties_verification()
    test_regularization_cutoff()
    test_prime_weight_exponential_form()
    
    print()
    print("=" * 80)
    print("✅ ALL RIEMANN EXPLICIT CONTRIBUTION TESTS PASSED")
    print("=" * 80)
