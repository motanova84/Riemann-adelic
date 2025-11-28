#!/usr/bin/env python3
"""
Tests for the Arithmetic Fractal Validation Module

This test suite validates the mathematical properties of the SABIO ∞³
arithmetic fractal identity, specifically:

1. The period of 68/81 is exactly 9 digits
2. The repeating pattern is "839506172"
3. Mathematical properties of 68 and 81
4. The f₀ constant structure

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: November 2025
"""

import pytest
from mpmath import mp

from utils.arithmetic_fractal_validation import (
    ArithmeticFractalValidator,
    ArithmeticFractalResult,
    validate_arithmetic_fractal,
)


class TestArithmeticFractalValidator:
    """Test suite for ArithmeticFractalValidator class."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.validator = ArithmeticFractalValidator(dps=300)
    
    def test_initialization(self):
        """Test that validator initializes correctly."""
        assert self.validator.dps == 300
        assert self.validator.EXPECTED_PERIOD == 9
        assert self.validator.EXPECTED_PATTERN == "839506172"
    
    def test_68_81_period_is_9(self):
        """
        Test that 68/81 has period exactly 9.
        
        Theory:
        The period of 1/q in base 10 (for gcd(q, 10) = 1) is the
        multiplicative order of 10 modulo q.
        
        For 81 = 3^4:
        - We need ord_81(10), i.e., smallest k such that 10^k ≡ 1 (mod 81)
        - This equals 9
        """
        period, pattern = self.validator.compute_period_of_rational(68, 81)
        
        assert period == 9, f"Expected period 9, got {period}"
        assert len(pattern) == 9, f"Pattern length should be 9, got {len(pattern)}"
    
    def test_repeating_pattern_839506172(self):
        """
        Test that the repeating pattern of 68/81 is "839506172".
        
        Verification:
        68/81 = 0.839506172839506172839506172...
        """
        period, pattern = self.validator.compute_period_of_rational(68, 81)
        
        assert pattern == "839506172", f"Expected pattern '839506172', got '{pattern}'"
    
    def test_period_verification_depth_10(self):
        """Test period verification with depth 10."""
        result = self.validator.verify_68_81_period(verification_depth=10)
        
        assert result.exact_match is True
        assert result.period == 9
        assert result.repeating_pattern == "839506172"
        assert result.verification_depth == 10
    
    def test_period_verification_depth_100(self):
        """Test period verification with depth 100."""
        result = self.validator.verify_68_81_period(verification_depth=100)
        
        assert result.exact_match is True
        assert result.period == 9
        assert result.repeating_pattern == "839506172"
    
    def test_68_factorization(self):
        """
        Test that 68 = 4 × 17.
        
        Mathematical significance:
        - 17 is prime (the golden position φ¹⁷)
        - 4 = 2² (power of smallest prime)
        """
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["68_factorization"]["is_4_times_17"] is True
        assert 68 == 4 * 17
    
    def test_17_is_prime(self):
        """Test that 17 is prime."""
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["17_is_prime"] is True
    
    def test_81_factorization(self):
        """
        Test that 81 = 3⁴.
        
        Mathematical significance:
        - 3 is the first odd prime
        - 4 is the exponent (3⁴ = 81)
        """
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["81_factorization"]["is_3_to_4"] is True
        assert props["81_factorization"]["base"] == 3
        assert props["81_factorization"]["exponent"] == 4
        assert 81 == 3**4
    
    def test_3_is_first_odd_prime(self):
        """Test that 3 is correctly identified as the first odd prime."""
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["3_is_first_odd_prime"] is True
    
    def test_multiplicative_order_10_mod_81_is_9(self):
        """
        Test that ord_81(10) = 9.
        
        Theory:
        The multiplicative order of 10 modulo 81 determines the period
        of rational numbers with denominator 81 in base 10.
        """
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["multiplicative_order_10_mod_81"]["order"] == 9
        assert props["multiplicative_order_10_mod_81"]["equals_period"] is True
    
    def test_period_structure_3_squared(self):
        """
        Test that period 9 = 3².
        
        This relates to 81 = 3⁴, as the period divides φ(81) = 54 = 2 × 27.
        """
        result = self.validator.verify_68_81_period()
        props = result.mathematical_properties
        
        assert props["period_structure"]["is_3_squared"] is True
        assert props["period_structure"]["period"] == 9
        assert 9 == 3**2
    
    def test_f0_structure_verified(self):
        """Test that f₀ structure contains the periodic pattern."""
        result = self.validator.verify_68_81_period()
        
        # The f₀ structure should be verified
        assert result.f0_structure_verified is True
    
    def test_validation_certificate_generation(self):
        """Test that validation certificate is generated correctly."""
        certificate = self.validator.generate_validation_certificate()
        
        assert "title" in certificate
        assert certificate["title"] == "Arithmetic Fractal Validation Certificate"
        assert "framework" in certificate
        assert certificate["framework"] == "SABIO ∞³"
        assert "validation_results" in certificate
        assert "mathematical_properties" in certificate
        assert "conclusion" in certificate
    
    def test_certificate_validation_results(self):
        """Test certificate validation results section."""
        certificate = self.validator.generate_validation_certificate()
        results = certificate["validation_results"]
        
        assert results["68_81_period"] == 9
        assert results["expected_period"] == 9
        assert results["period_correct"] is True
        assert results["repeating_pattern"] == "839506172"
        assert results["pattern_correct"] is True
    
    def test_multiplicative_order_helper(self):
        """Test the multiplicative order helper function."""
        # ord_81(10) = 9
        assert self.validator._multiplicative_order(10, 81) == 9
        
        # ord_9(10) = 1 (since 10 ≡ 1 mod 9)
        assert self.validator._multiplicative_order(10, 9) == 1
        
        # ord_7(10) = 6 (since 10^6 ≡ 1 mod 7)
        assert self.validator._multiplicative_order(10, 7) == 6
    
    def test_is_prime_helper(self):
        """Test the primality check helper function."""
        # Known primes
        for p in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
            assert self.validator._is_prime(p) is True, f"{p} should be prime"
        
        # Known composites
        for n in [4, 6, 8, 9, 10, 12, 15, 18, 21]:
            assert self.validator._is_prime(n) is False, f"{n} should not be prime"


class TestValidateArithmeticFractal:
    """Test the main validation function."""
    
    def test_validation_returns_dict(self):
        """Test that validation returns a dictionary."""
        result = validate_arithmetic_fractal(dps=100, verbose=False)
        
        assert isinstance(result, dict)
        assert "result" in result
        assert "certificate" in result
        assert "success" in result
    
    def test_validation_success(self):
        """Test that validation succeeds."""
        result = validate_arithmetic_fractal(dps=100, verbose=False)
        
        assert result["success"] is True
    
    def test_validation_result_type(self):
        """Test that result contains ArithmeticFractalResult."""
        result = validate_arithmetic_fractal(dps=100, verbose=False)
        
        assert isinstance(result["result"], ArithmeticFractalResult)


class TestHighPrecisionValidation:
    """Tests with higher precision to ensure numerical stability."""
    
    # Default precision to restore after tests
    DEFAULT_DPS = 15
    
    def teardown_method(self):
        """Reset precision after each test."""
        mp.dps = self.DEFAULT_DPS
    
    def test_period_at_500_dps(self):
        """Test period verification at 500 decimal places."""
        original_dps = mp.dps
        try:
            mp.dps = 500
            validator = ArithmeticFractalValidator(dps=500)
            result = validator.verify_68_81_period(verification_depth=50)
            
            assert result.exact_match is True
            assert result.period == 9
        finally:
            mp.dps = original_dps
    
    def test_direct_decimal_expansion(self):
        """Directly verify decimal expansion of 68/81."""
        original_dps = mp.dps
        try:
            mp.dps = 200
            
            ratio = mp.mpf(68) / mp.mpf(81)
            decimal_str = str(ratio)[2:]  # Remove "0."
            
            expected_pattern = "839506172"
            
            # Check first 20 periods
            for i in range(20):
                start = i * 9
                block = decimal_str[start:start + 9]
                assert block == expected_pattern, (
                    f"Period {i}: expected '{expected_pattern}', got '{block}'"
                )
        finally:
            mp.dps = original_dps


class TestArithmeticIdentity:
    """
    Tests for the complete arithmetic identity:
    f₀ = 141 + (non-periodic part) + 10^{-n} × (68/81)
    """
    
    def test_f0_integer_part(self):
        """Test that f₀ has integer part 141."""
        mp.dps = 300
        
        f0_str = ArithmeticFractalValidator.F0_CONSTANT
        f0 = mp.mpf(f0_str)
        
        integer_part = int(f0)
        assert integer_part == 141
    
    def test_f0_fractional_part_contains_periodic_pattern(self):
        """Test that f₀'s fractional part contains 839506172 pattern."""
        mp.dps = 300
        
        f0_str = ArithmeticFractalValidator.F0_CONSTANT
        f0 = mp.mpf(f0_str)
        
        fractional = f0 - 141
        frac_str = str(fractional)[2:]  # Remove "0."
        
        # The pattern should appear somewhere in the fractional part
        pattern = "839506172"
        assert pattern in frac_str, f"Pattern '{pattern}' not found in fractional part"
    
    def test_68_and_81_number_theory(self):
        """
        Test the number-theoretic significance of 68 and 81.
        
        - 68 = 4 × 17 = 2² × 17
        - 81 = 3⁴
        - gcd(68, 81) = 1 (coprime)
        - 17 is prime
        """
        from math import gcd
        
        assert 68 == 4 * 17
        assert 68 == 2**2 * 17
        assert 81 == 3**4
        assert gcd(68, 81) == 1
        
        # 17 is prime
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(n**0.5) + 1):
                if n % i == 0:
                    return False
            return True
        
        assert is_prime(17) is True
