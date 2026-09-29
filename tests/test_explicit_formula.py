#!/usr/bin/env python3
"""
Tests for Explicit Formula for Riemann Zeta Zeros
==================================================

This test suite validates the explicit formula:
    ∑_n Φ(t_n) = ∫ Φ(r) μ(r) dr - ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from operators.explicit_formula import (
    ExplicitFormula,
    ExplicitFormulaResult,
    gaussian_test_function,
    truncated_gaussian,
    smooth_bump_function,
    compute_qcal_coherence
)


class TestExplicitFormula:
    """Test suite for ExplicitFormula class."""
    
    def test_initialization(self):
        """Test ExplicitFormula initialization."""
        formula = ExplicitFormula(
            max_prime=100,
            max_prime_power=5,
            integral_limit=20.0
        )
        
        assert formula.max_prime == 100
        assert formula.max_prime_power == 5
        assert formula.integral_limit == 20.0
        assert len(formula._primes) > 0
        
        # Check that primes are correct
        assert formula._primes[0] == 2
        assert formula._primes[1] == 3
        assert formula._primes[2] == 5
    
    def test_sieve_of_eratosthenes(self):
        """Test prime sieve algorithm."""
        formula = ExplicitFormula(max_prime=30)
        primes = formula._primes
        
        # First 10 primes
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert list(primes[:10]) == expected_primes
    
    def test_fourier_transform_gaussian(self):
        """Test Fourier transform of Gaussian function."""
        formula = ExplicitFormula(integral_limit=10.0)
        
        # For Gaussian exp(-t²/2), Fourier transform is √(2π)exp(-ξ²/2)
        sigma = 1.0
        phi = lambda t: gaussian_test_function(t, sigma)
        
        # Test at ξ = 0
        phi_hat_0 = formula.fourier_transform(phi, 0.0)
        expected_0 = np.sqrt(2 * np.pi)  # ∫ exp(-t²/2) dt = √(2π)
        
        # Should be close (within numerical tolerance)
        assert abs(phi_hat_0 - expected_0) / expected_0 < 0.01
        
        # Test symmetry: Φ̂(ξ) = Φ̂(-ξ) for even functions
        xi = 1.5
        phi_hat_pos = formula.fourier_transform(phi, xi)
        phi_hat_neg = formula.fourier_transform(phi, -xi)
        
        assert abs(phi_hat_pos - phi_hat_neg) < 1e-10
    
    def test_fourier_transform_truncated_gaussian(self):
        """Test Fourier transform of truncated Gaussian."""
        formula = ExplicitFormula(integral_limit=10.0)
        
        a = 5.0
        sigma = 1.0
        phi = lambda t: truncated_gaussian(t, a, sigma)
        
        # Test at ξ = 0 (should be close to full Gaussian)
        phi_hat_0 = formula.fourier_transform(phi, 0.0)
        
        # Should be positive and reasonable
        assert phi_hat_0 > 0
        assert phi_hat_0 < 10.0
        
        # Test decay at large ξ
        phi_hat_large = formula.fourier_transform(phi, 10.0)
        assert abs(phi_hat_large) < abs(phi_hat_0)
    
    def test_compute_zero_sum_simple(self):
        """Test zero sum computation with simple zeros."""
        formula = ExplicitFormula()
        
        # Simple test function
        phi = lambda t: np.exp(-t**2 / 2)
        
        # Known zeros (approximate)
        zeros = [14.134725, 21.022040, 25.010858]
        
        zero_sum = formula.compute_zero_sum(phi, zeros)
        
        # Should be positive and reasonable
        assert zero_sum > 0
        assert zero_sum < 1.0  # Each term is < 1 for these zeros
    
    def test_compute_zero_sum_empty(self):
        """Test zero sum with no zeros."""
        formula = ExplicitFormula()
        
        phi = lambda t: 1.0
        zeros = []
        
        zero_sum = formula.compute_zero_sum(phi, zeros)
        assert zero_sum == 0.0
    
    def test_compute_integral_term(self):
        """Test integral term computation."""
        formula = ExplicitFormula(integral_limit=10.0)
        
        # Simple test function
        phi = lambda r: np.exp(-r**2 / 2)
        
        # Uniform weight
        integral = formula.compute_integral_term(phi, mu=None)
        
        # Should be close to √(2π)
        expected = np.sqrt(2 * np.pi)
        assert abs(integral - expected) / expected < 0.01
    
    def test_compute_integral_term_with_weight(self):
        """Test integral term with non-trivial weight function."""
        formula = ExplicitFormula(integral_limit=10.0)
        
        phi = lambda r: np.exp(-r**2 / 2)
        mu = lambda r: np.exp(-r**2 / 4)  # Another Gaussian weight
        
        integral = formula.compute_integral_term(phi, mu)
        
        # Should be positive
        assert integral > 0
    
    def test_compute_prime_sum_small(self):
        """Test prime sum computation with small parameters."""
        formula = ExplicitFormula(
            max_prime=10,
            max_prime_power=2,
            integral_limit=5.0
        )
        
        # Simple test function
        phi = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)
        
        prime_sum, cache = formula.compute_prime_sum(phi)
        
        # Should be positive (since Φ̂ should be positive for low frequencies)
        assert prime_sum > 0
        
        # Check cache has entries
        assert len(cache) > 0
    
    def test_prime_sum_convergence(self):
        """Test that prime sum converges as we increase parameters."""
        phi = lambda t: truncated_gaussian(t, a=3.0, sigma=1.0)
        
        # Compute with different max_prime
        formula1 = ExplicitFormula(max_prime=50, max_prime_power=5)
        sum1, _ = formula1.compute_prime_sum(phi)
        
        formula2 = ExplicitFormula(max_prime=100, max_prime_power=5)
        sum2, _ = formula2.compute_prime_sum(phi)
        
        # Difference should be small (convergence)
        relative_diff = abs(sum2 - sum1) / abs(sum2) if abs(sum2) > 1e-10 else 0
        assert relative_diff < 0.1  # Within 10%
    
    def test_validate_formula_structure(self):
        """Test that validate_formula returns correct structure."""
        formula = ExplicitFormula(
            max_prime=50,
            max_prime_power=3,
            integral_limit=20.0
        )
        
        phi = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)
        zeros = [14.134725, 21.022040, 25.010858]
        
        result = formula.validate_formula(phi, zeros)
        
        # Check result structure
        assert isinstance(result, ExplicitFormulaResult)
        assert result.num_zeros == 3
        assert result.num_primes > 0
        assert result.max_prime_power == 3
        
        # Check that LHS and RHS are computed
        assert result.total_lhs == result.zero_sum
        assert abs(result.total_rhs - (result.integral_term - result.prime_sum)) < 1e-10
        
        # Check residual and error
        assert result.residual >= 0
        assert 0 <= result.relative_error <= 1
    
    def test_explicit_formula_with_many_zeros(self):
        """Test explicit formula with more zeros."""
        formula = ExplicitFormula(
            max_prime=100,
            max_prime_power=5,
            integral_limit=30.0
        )
        
        # Use first 10 known zeros
        zeros = [
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832
        ]
        
        phi = lambda t: truncated_gaussian(t, a=8.0, sigma=2.0)
        
        result = formula.validate_formula(phi, zeros)
        
        # Basic sanity checks
        # Note: zero_sum might be zero if test function decays rapidly
        assert result.zero_sum >= 0
        assert result.integral_term > 0
        assert result.prime_sum > 0
        
        # The formula should hold reasonably well
        # (exact agreement requires infinite sums, but should be close)
        assert result.relative_error < 0.5  # Within 50% (rough approximation)


class TestTestFunctions:
    """Test suite for test functions."""
    
    def test_gaussian_test_function(self):
        """Test Gaussian test function."""
        # Test at origin
        assert gaussian_test_function(0.0, sigma=1.0) == 1.0
        
        # Test decay
        val_1 = gaussian_test_function(1.0, sigma=1.0)
        val_2 = gaussian_test_function(2.0, sigma=1.0)
        assert val_1 > val_2 > 0
        
        # Test symmetry
        assert abs(gaussian_test_function(1.5) - gaussian_test_function(-1.5)) < 1e-10
    
    def test_truncated_gaussian(self):
        """Test truncated Gaussian."""
        a = 5.0
        sigma = 1.0
        
        # Inside support
        assert truncated_gaussian(0.0, a, sigma) == 1.0
        assert truncated_gaussian(3.0, a, sigma) > 0
        
        # Outside support
        assert truncated_gaussian(6.0, a, sigma) == 0.0
        assert truncated_gaussian(-6.0, a, sigma) == 0.0
        
        # At boundary (should be nearly zero)
        val_boundary = truncated_gaussian(5.0, a, sigma)
        assert val_boundary < 0.1
    
    def test_smooth_bump_function(self):
        """Test smooth bump function."""
        a = 3.0
        
        # At origin
        val_0 = smooth_bump_function(0.0, a)
        assert val_0 > 0
        
        # Inside support
        assert smooth_bump_function(1.0, a) > 0
        
        # Outside support
        assert smooth_bump_function(4.0, a) == 0.0
        assert smooth_bump_function(-4.0, a) == 0.0
        
        # Symmetry
        assert abs(smooth_bump_function(1.5, a) - smooth_bump_function(-1.5, a)) < 1e-10


class TestQCALCoherence:
    """Test QCAL coherence computation."""
    
    def test_compute_qcal_coherence_perfect(self):
        """Test coherence computation for perfect agreement."""
        result = ExplicitFormulaResult(
            zero_sum=10.0,
            integral_term=15.0,
            prime_sum=5.0,
            total_lhs=10.0,
            total_rhs=10.0,
            residual=0.0,
            relative_error=0.0,
            num_zeros=10,
            num_primes=25,
            max_prime_power=5
        )
        
        coherence = compute_qcal_coherence(result)
        assert coherence == 1.0
    
    def test_compute_qcal_coherence_partial(self):
        """Test coherence computation for partial agreement."""
        result = ExplicitFormulaResult(
            zero_sum=10.0,
            integral_term=15.0,
            prime_sum=5.0,
            total_lhs=10.0,
            total_rhs=9.0,
            residual=1.0,
            relative_error=0.1,
            num_zeros=10,
            num_primes=25,
            max_prime_power=5
        )
        
        coherence = compute_qcal_coherence(result)
        assert coherence == 0.9
    
    def test_compute_qcal_coherence_bounds(self):
        """Test that coherence is bounded [0, 1]."""
        # Large error (should clip to 0)
        result_bad = ExplicitFormulaResult(
            zero_sum=10.0,
            integral_term=15.0,
            prime_sum=5.0,
            total_lhs=10.0,
            total_rhs=0.0,
            residual=10.0,
            relative_error=2.0,
            num_zeros=10,
            num_primes=25,
            max_prime_power=5
        )
        
        coherence = compute_qcal_coherence(result_bad)
        assert coherence == 0.0


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_empty_primes(self):
        """Test behavior with no primes (max_prime < 2)."""
        formula = ExplicitFormula(max_prime=1, max_prime_power=5)
        
        phi = lambda t: gaussian_test_function(t)
        
        prime_sum, _ = formula.compute_prime_sum(phi)
        assert prime_sum == 0.0
    
    def test_high_frequency_fourier(self):
        """Test Fourier transform at high frequencies."""
        formula = ExplicitFormula(integral_limit=10.0)
        
        phi = lambda t: truncated_gaussian(t, a=3.0, sigma=0.5)
        
        # High frequency should give small magnitude
        phi_hat_high = formula.fourier_transform(phi, 50.0)
        assert abs(phi_hat_high) < 0.1
    
    def test_zero_test_function(self):
        """Test with identically zero test function."""
        formula = ExplicitFormula(max_prime=10, max_prime_power=2)
        
        phi = lambda t: 0.0
        zeros = [14.134725, 21.022040]
        
        result = formula.validate_formula(phi, zeros)
        
        # Everything should be zero
        assert result.zero_sum == 0.0
        assert result.integral_term == 0.0
        assert result.prime_sum == 0.0
        assert result.residual == 0.0


class TestMpmathIntegration:
    """Test mpmath high-precision mode (if available)."""
    
    def test_mpmath_mode(self):
        """Test initialization with mpmath."""
        try:
            formula = ExplicitFormula(
                max_prime=20,
                max_prime_power=3,
                use_mpmath=True,
                precision=50
            )
            
            phi = lambda t: gaussian_test_function(t, sigma=1.0)
            zeros = [14.134725, 21.022040]
            
            result = formula.validate_formula(phi, zeros)
            
            # Should produce valid results
            assert result.zero_sum > 0
            assert result.integral_term > 0
            
        except ImportError:
            pytest.skip("mpmath not available")
    
    def test_mpmath_fourier_precision(self):
        """Test that mpmath gives more precise Fourier transforms."""
        try:
            formula_low = ExplicitFormula(use_mpmath=False, integral_limit=10.0)
            formula_high = ExplicitFormula(use_mpmath=True, precision=50, integral_limit=10.0)
            
            phi = lambda t: gaussian_test_function(t, sigma=1.0)
            
            # Both should give similar results at ξ=0
            val_low = formula_low.fourier_transform(phi, 0.0)
            val_high = formula_high.fourier_transform(phi, 0.0)
            
            # Should agree to several decimal places
            relative_diff = abs(val_high - val_low) / abs(val_high)
            assert relative_diff < 0.01
            
        except ImportError:
            pytest.skip("mpmath not available")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
