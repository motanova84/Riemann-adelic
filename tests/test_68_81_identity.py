#!/usr/bin/env python3
"""
Tests for the 68/81 identity verification module.

Tests the mathematical properties of 68/81 and its connection
to the Riemann zeta function derivative ζ'(1/2).
"""

import pytest
import sys
import os

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from utils.verify_68_81_identity import (
    verify_68_81_identity,
    analyze_decimal_expansion,
    analyze_geometric_series,
    find_singularity,
    get_zeta_prime_half
)


class TestDecimalExpansion:
    """Tests for decimal expansion analysis."""

    def test_period_length(self):
        """Test that 68/81 has period 9."""
        result = analyze_decimal_expansion(68, 81)
        assert result['period_length'] == 9

    def test_period_digits(self):
        """Test that the period is 839506172."""
        result = analyze_decimal_expansion(68, 81)
        assert result['period_digits'] == '839506172'

    def test_is_periodic(self):
        """Test that 68/81 is detected as periodic."""
        result = analyze_decimal_expansion(68, 81)
        assert result['is_periodic'] is True

    def test_decimal_starts_correctly(self):
        """Test that decimal expansion starts with correct digits."""
        result = analyze_decimal_expansion(68, 81)
        assert result['decimal_expansion'].startswith('0.839506172')


class TestGeometricSeries:
    """Tests for geometric series analysis."""

    def test_converges_inside_radius(self):
        """Test convergence inside radius of convergence."""
        result = analyze_geometric_series(0.5)
        assert result['converges'] is True

    def test_converges_at_68_81(self):
        """Test convergence at x = 68/81."""
        result = analyze_geometric_series(68 / 81)
        assert result['converges'] is True

    def test_convergence_ratio_less_than_one(self):
        """Test that convergence ratio < 1 for convergent case."""
        result = analyze_geometric_series(0.5)
        assert result['convergence_ratio'] < 1

    def test_series_sum_positive(self):
        """Test that series sum is positive."""
        result = analyze_geometric_series(0.5)
        assert result['series_sum'] > 0


class TestSingularity:
    """Tests for singularity location."""

    def test_singularity_value(self):
        """Test that singularity is at 81/68."""
        exact, decimal = find_singularity()
        assert abs(exact - 81 / 68) < 1e-10

    def test_singularity_greater_than_one(self):
        """Test that singularity is > 1."""
        exact, decimal = find_singularity()
        assert exact > 1

    def test_product_is_one(self):
        """Test that 68/81 * 81/68 = 1."""
        exact, _ = find_singularity()
        product = (68 / 81) * exact
        assert abs(product - 1.0) < 1e-10


class TestZetaDerivative:
    """Tests for zeta derivative calculation."""

    def test_zeta_prime_negative(self):
        """Test that ζ'(1/2) is negative."""
        zp = get_zeta_prime_half(30)
        assert float(zp) < 0

    def test_zeta_prime_approximate_value(self):
        """Test approximate value of ζ'(1/2)."""
        zp = get_zeta_prime_half(30)
        # ζ'(1/2) ≈ -3.9226...
        assert abs(float(zp) - (-3.9226)) < 0.01


class TestIdentityVerification:
    """Tests for the main identity verification."""

    def test_returns_dict(self):
        """Test that verify_68_81_identity returns a dict."""
        result = verify_68_81_identity(30)
        assert isinstance(result, dict)

    def test_contains_expected_keys(self):
        """Test that result contains expected keys."""
        result = verify_68_81_identity(30)
        expected_keys = [
            'zeta_prime_half',
            'exp_ratio',
            'fraction_68_81',
            'difference',
            'relative_error',
            'precision_digits'
        ]
        for key in expected_keys:
            assert key in result

    def test_fraction_value_correct(self):
        """Test that 68/81 value is correct."""
        result = verify_68_81_identity(30)
        assert abs(result['fraction_68_81'] - 0.839506172839506) < 1e-10

    def test_precision_stored(self):
        """Test that precision is correctly stored."""
        result = verify_68_81_identity(25)
        assert result['precision_digits'] == 25


class TestMathematicalProperties:
    """Tests for mathematical properties of 68/81."""

    def test_68_factorization(self):
        """Test that 68 = 4 * 17."""
        assert 68 == 4 * 17

    def test_81_is_power_of_3(self):
        """Test that 81 = 3^4."""
        assert 81 == 3 ** 4

    def test_fraction_less_than_one(self):
        """Test that 68/81 < 1."""
        assert 68 / 81 < 1

    def test_reciprocal_greater_than_one(self):
        """Test that 81/68 > 1."""
        assert 81 / 68 > 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
