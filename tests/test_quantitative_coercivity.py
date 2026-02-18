#!/usr/bin/env python3
"""
Pytest Test Suite for Quantitative Coercivity Inequality

This module provides unit tests for the Vinogradov-Korobov bound and
quantitative coercivity implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from operators.vinogradov_korobov_bound import (
    VinogradovKorobovBound,
    RegularizedHeckeWeight,
    QuantitativeCoercivity,
    generate_primes_up_to,
)


class TestVinogradovKorobovBound:
    """Test suite for Vinogradov-Korobov exponential bounds."""
    
    def test_vk_bound_positive(self):
        """VK bound should always be positive."""
        vk = VinogradovKorobovBound()
        
        for X in [100, 1000, 10000]:
            for gamma in [10, 50, 100]:
                bound = vk.compute_vk_bound(X, gamma)
                assert bound > 0, f"VK bound should be positive for X={X}, gamma={gamma}"
    
    def test_vk_exponential_decay(self):
        """VK bound should show exponential decay (Bound < X)."""
        vk = VinogradovKorobovBound()
        
        test_cases = [
            (100, 10),
            (1000, 50),
            (10000, 100),
        ]
        
        for X, gamma in test_cases:
            bound = vk.compute_vk_bound(X, gamma)
            assert bound < X, f"Expected exponential decay: Bound={bound:.2e} < X={X}"
    
    def test_vk_decay_improves_with_X(self):
        """Decay ratio X/Bound should increase with X."""
        vk = VinogradovKorobovBound()
        gamma = 100
        
        ratios = []
        for X in [100, 1000, 10000]:
            bound = vk.compute_vk_bound(X, gamma)
            ratio = X / bound if bound > 0 else 0
            ratios.append(ratio)
        
        # Ratios should be increasing
        for i in range(len(ratios) - 1):
            assert ratios[i] < ratios[i+1], f"Decay should improve with larger X: {ratios}"
    
    def test_weighted_vk_error_positive(self):
        """Weighted VK error should be positive."""
        vk = VinogradovKorobovBound()
        
        for X in [100, 1000]:
            for gamma in [50, 100]:
                error = vk.compute_weighted_vk_error(X, gamma, t=0.05)
                assert error >= 0, f"Error should be non-negative for X={X}, gamma={gamma}"


class TestRegularizedHeckeWeight:
    """Test suite for regularized Hecke weight."""
    
    def test_weight_non_negative(self):
        """W_reg should be non-negative (from cosine phase)."""
        hecke = RegularizedHeckeWeight(t=0.05)
        
        # Generate some primes
        primes, log_primes = generate_primes_up_to(100)
        
        for gamma in [10, 50, 100]:
            weight = hecke.compute_weight_direct(gamma, primes, log_primes)
            assert weight >= 0, f"W_reg should be non-negative for gamma={gamma}"
    
    def test_lower_bound_properties(self):
        """Lower bound should have correct properties."""
        hecke = RegularizedHeckeWeight(t=0.05)
        
        gamma = 100
        X = 1000
        
        lower = hecke.compute_weight_lower_bound(gamma, X, alpha=1.5)
        
        # Should be non-negative
        assert lower >= 0, "Lower bound should be non-negative"
    
    def test_power_law_verification(self):
        """Power law growth should be verified for large gamma."""
        hecke = RegularizedHeckeWeight(t=0.05)
        
        # For large gamma with X = gamma^1.5, we expect power law
        gamma = 500
        result = hecke.verify_power_law_growth(gamma, alpha=1.5)
        
        assert 'delta' in result
        assert result['delta'] > 0, "Delta should be positive"
        assert 'W_reg_lower_bound' in result
        assert 'power_law_verified' in result


class TestQuantitativeCoercivity:
    """Test suite for quantitative coercivity."""
    
    def test_sobolev_norm_positive(self):
        """Sobolev norm should be positive for non-zero function."""
        coercivity = QuantitativeCoercivity(t=0.05, alpha=1.5)
        
        gammas = np.array([10.0, 50.0, 100.0])
        f_hat = np.array([1.0, 0.5, 0.3])
        
        norm_sq = coercivity.compute_sobolev_norm(gammas, f_hat)
        assert norm_sq > 0, "Sobolev norm should be positive for non-zero function"
    
    def test_sobolev_norm_zero_for_zero_function(self):
        """Sobolev norm should be zero for zero function."""
        coercivity = QuantitativeCoercivity(t=0.05, alpha=1.5)
        
        gammas = np.array([10.0, 50.0, 100.0])
        f_hat = np.zeros(3)
        
        norm_sq = coercivity.compute_sobolev_norm(gammas, f_hat)
        assert norm_sq == 0, "Sobolev norm should be zero for zero function"
    
    def test_hecke_quadratic_form_non_negative(self):
        """Hecke quadratic form should be non-negative."""
        coercivity = QuantitativeCoercivity(t=0.05, alpha=1.5)
        
        gammas = np.array([50.0, 100.0, 200.0])
        f_hat = np.array([1.0, 0.7, 0.5])
        X = 1000
        
        Q_Ht = coercivity.compute_hecke_quadratic_form(gammas, f_hat, X)
        assert Q_Ht >= 0, "Hecke quadratic form should be non-negative"
    
    def test_coercivity_inequality_structure(self):
        """Coercivity inequality verification should return proper structure."""
        coercivity = QuantitativeCoercivity(t=0.05, alpha=1.5)
        
        gammas = np.linspace(50, 200, 10)
        f_hat = np.exp(-(gammas - 100)**2 / 5000)
        f_hat = f_hat / np.linalg.norm(f_hat)
        
        result = coercivity.verify_coercivity_inequality(gammas, f_hat)
        
        # Check all required keys are present
        required_keys = ['delta', 't', 'alpha', 'Q_Ht', 'sobolev_norm_H_delta',
                        'c_estimate', 'satisfied', 'compact_resolvent']
        for key in required_keys:
            assert key in result, f"Result should contain key '{key}'"
        
        # Check types
        assert result['delta'] > 0
        assert 'satisfied' in result
        assert 'compact_resolvent' in result


class TestPrimeGeneration:
    """Test suite for prime generation utility."""
    
    def test_primes_up_to_100(self):
        """Should generate correct primes up to 100."""
        primes, log_primes = generate_primes_up_to(100)
        
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
                          43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
        
        np.testing.assert_array_equal(primes, expected_primes,
                                     "Should generate correct primes up to 100")
        
        # Check log_primes
        expected_log_primes = np.log(expected_primes)
        np.testing.assert_array_almost_equal(log_primes, expected_log_primes,
                                            decimal=10,
                                            err_msg="log_primes should match")
    
    def test_no_primes_below_2(self):
        """Should return empty arrays for X < 2."""
        primes, log_primes = generate_primes_up_to(1)
        
        assert len(primes) == 0, "Should have no primes for X < 2"
        assert len(log_primes) == 0, "Should have no log_primes for X < 2"
    
    def test_prime_count_grows(self):
        """Prime count should grow with X."""
        counts = []
        for X in [10, 100, 1000]:
            primes, _ = generate_primes_up_to(X)
            counts.append(len(primes))
        
        # Counts should be increasing
        for i in range(len(counts) - 1):
            assert counts[i] < counts[i+1], f"Prime count should grow: {counts}"


class TestMathematicalProperties:
    """Test mathematical properties and consistency."""
    
    def test_delta_positive_for_small_t(self):
        """Delta should be positive when t < 1/2."""
        for t in [0.01, 0.05, 0.1, 0.2, 0.4]:
            for alpha in [0.5, 1.0, 1.5]:
                delta = alpha * (0.5 - t)
                assert delta > 0, f"Delta should be positive for t={t}, alpha={alpha}"
    
    def test_consistency_between_modules(self):
        """Different modules should use consistent parameters."""
        hecke = RegularizedHeckeWeight(t=0.05)
        coercivity = QuantitativeCoercivity(t=0.05, alpha=1.5)
        
        # Both should use same t
        assert hecke.t == coercivity.t, "Heat parameter should be consistent"
        
        # Delta calculation should match
        expected_delta = coercivity.alpha * (0.5 - coercivity.t)
        assert abs(coercivity.delta - expected_delta) < 1e-10, "Delta calculation should match"


# Parametrized tests for robustness
@pytest.mark.parametrize("X,gamma", [
    (100, 10),
    (1000, 50),
    (10000, 100),
])
def test_vk_bound_various_parameters(X, gamma):
    """Test VK bound with various parameter combinations."""
    vk = VinogradovKorobovBound()
    bound = vk.compute_vk_bound(X, gamma)
    
    # Basic sanity checks
    assert bound > 0, f"Bound should be positive"
    assert bound < 10 * X, f"Bound shouldn't be unreasonably large"


@pytest.mark.parametrize("t", [0.01, 0.05, 0.1, 0.2])
def test_regularized_weight_various_t(t):
    """Test regularized weight with various heat parameters."""
    hecke = RegularizedHeckeWeight(t=t)
    
    gamma = 100
    X = 1000
    
    lower = hecke.compute_weight_lower_bound(gamma, X, alpha=1.5)
    
    # Should be non-negative
    assert lower >= 0, f"Lower bound should be non-negative for t={t}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
