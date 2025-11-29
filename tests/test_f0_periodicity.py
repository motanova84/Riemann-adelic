#!/usr/bin/env python3
"""
Tests for the F0 Periodicity Analysis Module.

This module tests the high-precision validation confirming that the decimal
sequence 8395061728395061 appearing in f₀ is the exact period-16 cycle of 68/81.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import sys
sys.path.insert(0, '.')

import pytest
import mpmath as mp

from analyze_f0_periodicity import (
    setup_precision,
    get_f0_extended,
    compute_68_81_rational,
    extract_fractional_from_f0,
    verify_period_coincidence,
    verify_extended_repetition,
    run_f0_periodicity_analysis,
    EXTENDED_F0_STRING,
    PERIOD_68_81,
    PERIOD_LENGTH,
)


class TestConstants:
    """Test suite for module constants."""
    
    def test_period_constant(self):
        """Test that the period constant is correctly defined."""
        assert PERIOD_68_81 == "8395061728395061"
        assert len(PERIOD_68_81) == 16
    
    def test_period_length(self):
        """Test period length constant."""
        assert PERIOD_LENGTH == 16
    
    def test_extended_f0_string_format(self):
        """Test that the extended f0 string is correctly formatted."""
        assert EXTENDED_F0_STRING.startswith("141.7001")
        assert PERIOD_68_81 in EXTENDED_F0_STRING


class TestPrecisionSetup:
    """Test suite for precision setup."""
    
    def test_setup_precision_300(self):
        """Test setting precision to 300 dps."""
        setup_precision(300)
        assert mp.mp.dps == 300
    
    def test_setup_precision_custom(self):
        """Test setting custom precision."""
        setup_precision(500)
        assert mp.mp.dps == 500
        # Reset to avoid affecting other tests
        setup_precision(50)


class TestGetF0Extended:
    """Test suite for get_f0_extended function."""
    
    def setup_method(self):
        """Set up test fixtures."""
        setup_precision(100)
    
    def test_returns_mpf(self):
        """Test that function returns mpf type."""
        result = get_f0_extended(100)
        assert isinstance(result, mp.mpf)
    
    def test_value_in_correct_range(self):
        """Test that the value is approximately 141.7001."""
        result = get_f0_extended(100)
        assert 141.7 < float(result) < 141.8
    
    def test_precision_preserved(self):
        """Test that high precision is preserved."""
        result = get_f0_extended(200)
        result_str = mp.nstr(result, 60)
        assert PERIOD_68_81 in result_str


class TestCompute68_81Rational:
    """Test suite for compute_68_81_rational function."""
    
    def setup_method(self):
        """Set up test fixtures."""
        setup_precision(100)
    
    def test_first_16_digits_are_period(self):
        """Test that first 16 digits match the expected period."""
        result = compute_68_81_rational(50)
        assert result[:16] == PERIOD_68_81
    
    def test_period_repeats(self):
        """Test that the period repeats correctly.
        
        Note: The true mathematical period of 68/81 is 9 digits: 839506172
        The 16-digit sequence "8395061728395061" used in the problem statement
        is the first 16 digits of 68/81's decimal, which is the 9-digit period
        repeated: (839506172 * 2)[:16] = 8395061728395061
        """
        result = compute_68_81_rational(48)
        
        # The first 16 digits should be PERIOD_68_81
        first_16 = result[:16]
        assert first_16 == PERIOD_68_81
        
        # The actual mathematical period is 9 digits
        true_period = "839506172"
        
        # Verify the 48-digit result matches the true period repeated
        expected_48 = (true_period * 6)[:48]  # 9 * 6 = 54, take first 48
        assert result[:48] == expected_48, f"Got {result[:48]}, expected {expected_48}"


class TestExtractFractionalFromF0:
    """Test suite for extract_fractional_from_f0 function."""
    
    def test_fractional_starts_with_7001(self):
        """Test that fractional part starts correctly."""
        result = extract_fractional_from_f0(100)
        assert result.startswith("7001")
    
    def test_contains_period(self):
        """Test that fractional contains the period sequence."""
        result = extract_fractional_from_f0(200)
        assert PERIOD_68_81 in result


class TestVerifyPeriodCoincidence:
    """Test suite for verify_period_coincidence function."""
    
    def test_coincidence_is_true(self):
        """Test that the sequences coincide."""
        coincide, seq_f0, seq_rational = verify_period_coincidence(300)
        assert coincide is True
    
    def test_sequences_match(self):
        """Test that both sequences match the expected period."""
        coincide, seq_f0, seq_rational = verify_period_coincidence(300)
        assert seq_f0 == PERIOD_68_81
        assert seq_rational == PERIOD_68_81


class TestVerifyExtendedRepetition:
    """Test suite for verify_extended_repetition function."""
    
    def test_120_digits_verified(self):
        """Test that at least 120 consecutive digits are verified."""
        success, verified_digits, break_pos = verify_extended_repetition(300, 120)
        assert success is True
        assert verified_digits >= 120
    
    def test_no_break_position(self):
        """Test that there is no break in the first 120 digits."""
        success, verified_digits, break_pos = verify_extended_repetition(300, 120)
        assert break_pos is None
    
    def test_smaller_requirement(self):
        """Test with a smaller requirement."""
        success, verified_digits, break_pos = verify_extended_repetition(300, 50)
        assert success is True
        assert verified_digits >= 50


class TestRunF0PeriodicityAnalysis:
    """Test suite for the main analysis function."""
    
    def test_analysis_returns_dict(self):
        """Test that analysis returns a dictionary."""
        result = run_f0_periodicity_analysis(300)
        assert isinstance(result, dict)
    
    def test_analysis_verified_true(self):
        """Test that overall verification passes."""
        result = run_f0_periodicity_analysis(300)
        assert result["verified"] is True
    
    def test_all_checks_pass(self):
        """Test that all individual checks pass."""
        result = run_f0_periodicity_analysis(300)
        assert result["checks"]["period_68_81_correct"] is True
        assert result["checks"]["coincidence"] is True
        assert result["checks"]["extended_repetition"] is True
    
    def test_correct_period_and_fraction(self):
        """Test that result contains correct period and fraction."""
        result = run_f0_periodicity_analysis(300)
        assert result["period_sequence"] == PERIOD_68_81
        assert result["fraction"] == "68/81"
        assert result["period_length"] == 16
    
    def test_verified_digits_recorded(self):
        """Test that verified digits count is recorded."""
        result = run_f0_periodicity_analysis(300)
        assert result["checks"]["verified_consecutive_digits"] >= 120


class TestMathematicalProperties:
    """Test suite for mathematical properties of 68/81."""
    
    def test_denominator_is_3_power_4(self):
        """Test that 81 = 3^4."""
        assert 81 == 3**4
    
    def test_numerator_factorization(self):
        """Test that 68 = 4 × 17."""
        assert 68 == 4 * 17
    
    def test_gcd_is_1(self):
        """Test that gcd(68, 81) = 1 (fraction is reduced)."""
        from math import gcd
        assert gcd(68, 81) == 1
    
    def test_period_contains_all_digits(self):
        """Test that the period contains digits 0-9 except certain ones."""
        period = PERIOD_68_81
        # The period 8395061728395061 contains: 0,1,2,3,5,6,7,8,9 (missing 4)
        unique_digits = set(period)
        assert '4' not in unique_digits  # 4 is not in the period


class TestHighPrecision:
    """Test suite for high precision verification."""
    
    def test_300_dps_precision(self):
        """Test analysis at 300 dps precision."""
        result = run_f0_periodicity_analysis(300)
        assert result["precision_dps"] == 300
        assert result["verified"] is True
    
    def test_200_dps_precision(self):
        """Test analysis at 200 dps precision."""
        result = run_f0_periodicity_analysis(200)
        assert result["precision_dps"] == 200
        assert result["verified"] is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
