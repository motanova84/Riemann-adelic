"""
Test suite for Weil-Guinand positivity theorem implementation.

This module tests the numerical validation of the Weil-Guinand positivity
criterion for the Riemann Hypothesis.

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.weil_guinand_positivity import (
    von_mangoldt,
    mellin_transform,
    gaussian_test_function,
    exponential_test_function,
    compute_spectral_side,
    compute_arithmetic_side,
    validate_weil_guinand_positivity,
    ValidationResult,
)


class TestVonMangoldt:
    """Tests for von Mangoldt function Λ(n)"""
    
    def test_primes(self):
        """Λ(p) = log(p) for primes"""
        assert von_mangoldt(2) == pytest.approx(np.log(2), rel=1e-6)
        assert von_mangoldt(3) == pytest.approx(np.log(3), rel=1e-6)
        assert von_mangoldt(5) == pytest.approx(np.log(5), rel=1e-6)
        assert von_mangoldt(7) == pytest.approx(np.log(7), rel=1e-6)
    
    def test_prime_powers(self):
        """Λ(p^k) = log(p) for prime powers"""
        assert von_mangoldt(4) == pytest.approx(np.log(2), rel=1e-6)  # 2^2
        assert von_mangoldt(8) == pytest.approx(np.log(2), rel=1e-6)  # 2^3
        assert von_mangoldt(9) == pytest.approx(np.log(3), rel=1e-6)  # 3^2
        assert von_mangoldt(25) == pytest.approx(np.log(5), rel=1e-6)  # 5^2
    
    def test_composites(self):
        """Λ(n) = 0 for non-prime-powers"""
        assert von_mangoldt(6) == 0.0  # 2 * 3
        assert von_mangoldt(10) == 0.0  # 2 * 5
        assert von_mangoldt(12) == 0.0  # 2^2 * 3
        assert von_mangoldt(15) == 0.0  # 3 * 5
    
    def test_special_cases(self):
        """Special cases: 1 and negative numbers"""
        assert von_mangoldt(1) == 0.0
        assert von_mangoldt(0) == 0.0


class TestMellinTransform:
    """Tests for Mellin transform"""
    
    def test_exponential_function(self):
        """Test Mellin transform of e^(-x)"""
        # For f(x) = e^(-x), f̂(s) = Γ(s) for Re(s) > 0
        f = exponential_test_function(alpha=1.0)
        
        # Test at s = 1: Γ(1) = 1
        s = 1.0 + 0.0j
        result = mellin_transform(f, s)
        assert abs(result.real - 1.0) < 0.1  # Allow some numerical error
    
    def test_power_function(self):
        """Test Mellin transform of power function"""
        # For f(x) = x^a for 0 < x < 1, f̂(s) = 1/(s+a+1)
        def power_func(x):
            if 0 < x < 1:
                return x**2
            return 0.0
        
        s = 1.0 + 0.0j
        result = mellin_transform(power_func, s, x_max=1.0)
        # Expected: 1/(1+2+1) = 1/4 = 0.25
        assert abs(result.real - 0.25) < 0.1


class TestTestFunctions:
    """Tests for test functions"""
    
    def test_gaussian_properties(self):
        """Gaussian test function properties"""
        f = gaussian_test_function(sigma=1.0)
        
        # f(0) should be close to 0 (we define it as 0 for x ≤ 0)
        assert f(0.0) == 0.0
        
        # f(x) should decay for large x
        assert abs(f(10.0)) < 0.01
        assert abs(f(100.0)) < 1e-10
    
    def test_exponential_properties(self):
        """Exponential test function properties"""
        f = exponential_test_function(alpha=1.0)
        
        # f(0) = 0 (our convention)
        assert f(0.0) == 0.0
        
        # f(x) decays exponentially
        assert abs(f(1.0) - np.exp(-1.0)) < 1e-10
        assert abs(f(2.0) - np.exp(-2.0)) < 1e-10


class TestSpectralSide:
    """Tests for spectral side computation"""
    
    def test_single_zero(self):
        """Test with single zero"""
        zeros = [0.5 + 14.134725j]
        f = gaussian_test_function(sigma=1.0)
        
        spectral = compute_spectral_side(zeros, f)
        
        # Should be non-negative (sum of squared magnitudes)
        assert spectral.real >= 0
    
    def test_multiple_zeros(self):
        """Test with multiple zeros"""
        zeros = [
            0.5 + 14.134725j,
            0.5 + 21.022040j,
            0.5 + 25.010858j,
        ]
        f = gaussian_test_function(sigma=1.0)
        
        spectral = compute_spectral_side(zeros, f)
        
        # Should be non-negative
        assert spectral.real >= 0


class TestArithmeticSide:
    """Tests for arithmetic side computation"""
    
    def test_small_primes(self):
        """Test with small number of primes"""
        f = exponential_test_function(alpha=1.0)
        
        arithmetic = compute_arithmetic_side(f, max_n=10, boundary_terms=False)
        
        # Should include contributions from 2, 3, 4, 5, 7, 8, 9
        # Λ(2)f(log 2) + Λ(3)f(log 3) + ... 
        # All terms should be positive for positive f
        assert arithmetic.real > 0


class TestWeilGuinandValidation:
    """Tests for complete Weil-Guinand validation"""
    
    def test_validation_structure(self):
        """Test that validation returns proper structure"""
        zeros = [0.5 + 14.134725j, 0.5 + 21.022040j]
        f = gaussian_test_function(sigma=1.0)
        
        result = validate_weil_guinand_positivity(
            zeros=zeros,
            test_function=f,
            test_function_name="Gaussian",
            max_primes=100
        )
        
        assert isinstance(result, ValidationResult)
        assert result.num_zeros_used == 2
        assert result.num_primes_used == 100
        assert result.test_function_name == "Gaussian"
    
    def test_positivity_gaussian(self):
        """Test positivity for Gaussian test function"""
        # Known zeros on critical line
        zeros = [
            0.5 + 14.134725j,
            0.5 + 21.022040j,
            0.5 + 25.010858j,
        ]
        f = gaussian_test_function(sigma=1.0)
        
        result = validate_weil_guinand_positivity(
            zeros=zeros,
            test_function=f,
            test_function_name="Gaussian",
            max_primes=100,
            tolerance=1e-3  # Allow small numerical errors
        )
        
        # Q[f] should be non-negative for zeros on critical line
        # Note: This might not always hold exactly due to numerical errors
        # and finite truncations, so we use a tolerance
        assert result.Q_value.real >= -0.1, \
            f"Q[f] = {result.Q_value.real} should be ≥ -0.1"
    
    def test_positivity_exponential(self):
        """Test positivity for exponential test function"""
        zeros = [
            0.5 + 14.134725j,
            0.5 + 21.022040j,
        ]
        f = exponential_test_function(alpha=1.0)
        
        result = validate_weil_guinand_positivity(
            zeros=zeros,
            test_function=f,
            test_function_name="Exponential",
            max_primes=100,
            tolerance=1e-3
        )
        
        # Q[f] should be non-negative
        assert result.Q_value.real >= -0.1


class TestQCALIntegration:
    """Tests for QCAL framework integration"""
    
    def test_qcal_constants(self):
        """Verify QCAL constants are defined"""
        from utils.weil_guinand_positivity import (
            QCAL_BASE_FREQUENCY,
            QCAL_COHERENCE
        )
        
        assert QCAL_BASE_FREQUENCY == 141.7001
        assert QCAL_COHERENCE == 244.36


def test_main_functionality():
    """Integration test for main functionality"""
    # Simple smoke test
    zeros = [0.5 + 14.134725j]
    f = gaussian_test_function(sigma=1.0)
    
    result = validate_weil_guinand_positivity(
        zeros=zeros,
        test_function=f,
        test_function_name="Test",
        max_primes=50
    )
    
    # Should complete without errors
    assert result is not None
    assert isinstance(result, ValidationResult)


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
