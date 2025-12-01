#!/usr/bin/env python3
"""
Tests for the Fractal Well (Pozo Fractal) Module

This test suite validates the mathematical properties of the fractal well
structure at x = 68/81, including:

1. The function P(x) = 1/(1 - (68/81)*x)
2. Singularity at x = 81/68
3. Self-referential recursive structure
4. The "well" where the number encounters itself

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: December 2025
"""

import pytest
from mpmath import mp, mpf

from utils.arithmetic_fractal_validation import (
    FractalWell,
    FractalWellResult,
    validate_fractal_well,
)

# Constants for tests (computed from base values)
NUMERATOR = 68
DENOMINATOR = 81
P_AT_WELL_NUMERATOR = DENOMINATOR ** 2  # 6561
P_AT_WELL_DENOMINATOR = DENOMINATOR ** 2 - NUMERATOR ** 2  # 1937
P_AT_WELL_EXACT = P_AT_WELL_NUMERATOR / P_AT_WELL_DENOMINATOR  # ≈ 3.387196...


class TestFractalWellInitialization:
    """Test suite for FractalWell initialization."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=100)
    
    def test_initialization(self):
        """Test that FractalWell initializes correctly."""
        assert self.well.dps == 100
        assert self.well.NUMERATOR == 68
        assert self.well.DENOMINATOR == 81
        assert self.well.PERIOD == 9
        assert self.well.PATTERN == "839506172"
    
    def test_ratio_values(self):
        """Test that ratio values are correct."""
        expected_68_81 = mpf(68) / mpf(81)
        expected_81_68 = mpf(81) / mpf(68)
        
        assert abs(self.well.ratio_68_81 - expected_68_81) < mpf(10) ** (-90)
        assert abs(self.well.ratio_81_68 - expected_81_68) < mpf(10) ** (-90)


class TestPFunction:
    """Test suite for P(x) = 1/(1 - (68/81)*x)."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=100)
    
    def test_p_at_zero(self):
        """Test P(0) = 1."""
        result = self.well.P(mpf(0))
        assert abs(result - 1) < mpf(10) ** (-90)
    
    def test_p_at_one(self):
        """Test P(1) = 1/(1 - 68/81) = 81/13."""
        result = self.well.P(mpf(1))
        expected = mpf(81) / mpf(13)
        assert abs(result - expected) < mpf(10) ** (-90)
    
    def test_p_at_well_position(self):
        """
        Test P(68/81) = 81²/(81² - 68²) = 6561/1937.
        
        This is the value at the "well" position.
        """
        result = self.well.evaluate_at_well()
        expected = mpf(P_AT_WELL_NUMERATOR) / mpf(P_AT_WELL_DENOMINATOR)
        assert abs(result - expected) < mpf(10) ** (-50)
    
    def test_p_exact_formula(self):
        """Verify P(68/81) = 81²/(81² - 68²)."""
        p_value = self.well.evaluate_at_well()
        
        expected = mpf(P_AT_WELL_NUMERATOR) / mpf(P_AT_WELL_DENOMINATOR)
        
        assert abs(p_value - expected) < mpf(10) ** (-50)
    
    def test_p_singularity_raises_error(self):
        """Test that P diverges near singularity x = 81/68."""
        # At a moderate distance from singularity, P should be large
        x_near_singularity = self.well.ratio_81_68 - mpf(10) ** (-5)
        
        result = self.well.P(x_near_singularity)
        assert abs(result) > 1e4  # Large value near singularity
        
        # Very close to singularity raises ZeroDivisionError
        x_very_near = self.well.ratio_81_68 - mpf(10) ** (-95)
        with pytest.raises(ZeroDivisionError):
            self.well.P(x_very_near)


class TestSingularityVerification:
    """Test suite for singularity verification at x = 81/68."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=100)
    
    def test_singularity_position(self):
        """Test that singularity is at x = 81/68."""
        expected = mpf(81) / mpf(68)
        assert abs(self.well.ratio_81_68 - expected) < mpf(10) ** (-90)
    
    def test_singularity_decimal(self):
        """Test singularity decimal value: 81/68 ≈ 1.191176..."""
        singularity = float(self.well.ratio_81_68)
        assert 1.1911 < singularity < 1.1912
    
    def test_verify_singularity_returns_dict(self):
        """Test that verify_singularity returns proper structure."""
        result = self.well.verify_singularity(epsilon_power=5)
        
        assert "singularity_position" in result
        assert result["singularity_position"] == "81/68"
        assert "tests" in result
        assert len(result["tests"]) == 5
    
    def test_singularity_divergence(self):
        """Test that P diverges as x → 81/68."""
        result = self.well.verify_singularity(epsilon_power=10)
        
        # Near singularity, values should be large
        for test in result["tests"]:
            # At least some tests should show divergence
            if "diverging" in test:
                # Check structure
                assert "P(x - ε)" in test
                assert "P(x + ε)" in test
    
    def test_singularity_verified(self):
        """Test that singularity is verified."""
        result = self.well.verify_singularity(epsilon_power=10)
        assert result["singularity_verified"] is True


class TestRecursiveStructure:
    """Test suite for recursive/self-referential structure analysis."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=300)
    
    def test_analyze_recursive_structure_returns_dict(self):
        """Test that analysis returns proper structure."""
        result = self.well.analyze_recursive_structure(depth=5)
        
        assert "well_value" in result
        assert result["well_value"] == "68/81"
        assert "period" in result
        assert result["period"] == 9
        assert "pattern" in result
        assert result["pattern"] == "839506172"
        assert "recursive_levels" in result
    
    def test_recursive_levels_count(self):
        """Test that correct number of levels are analyzed."""
        result = self.well.analyze_recursive_structure(depth=10)
        assert len(result["recursive_levels"]) == 10
    
    def test_all_blocks_match_pattern(self):
        """Test that all 9-digit blocks match the pattern 839506172."""
        result = self.well.analyze_recursive_structure(depth=20)
        
        for level in result["recursive_levels"]:
            assert level["matches_pattern"] is True
            assert level["block"] == "839506172"
    
    def test_self_referential_property(self):
        """Test that the structure is self-referential."""
        result = self.well.analyze_recursive_structure(depth=20)
        assert result["self_referential"] is True
    
    def test_decimal_expansion_contains_pattern(self):
        """Test that decimal expansion contains the repeating pattern."""
        result = self.well.analyze_recursive_structure(depth=5)
        assert "839506172" in result["decimal_expansion"]


class TestSymbolicRepresentation:
    """Test suite for symbolic representation."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=100)
    
    def test_generate_symbolic_representation(self):
        """Test that symbolic representation is generated."""
        representation = self.well.generate_symbolic_representation()
        
        assert isinstance(representation, str)
        assert len(representation) > 100
    
    def test_representation_contains_key_elements(self):
        """Test that representation contains key mathematical elements."""
        representation = self.well.generate_symbolic_representation()
        
        assert "68/81" in representation
        assert "839506172" in representation
        assert "POZO" in representation
        assert "P(x)" in representation
        assert "Singularity" in representation


class TestVerifyWell:
    """Test suite for complete well verification."""
    
    def setup_method(self):
        """Setup for each test method."""
        self.well = FractalWell(dps=200)
    
    def test_verify_well_returns_result(self):
        """Test that verify_well returns FractalWellResult."""
        result = self.well.verify_well()
        assert isinstance(result, FractalWellResult)
    
    def test_verify_well_positions(self):
        """Test well and singularity positions."""
        result = self.well.verify_well()
        
        assert result.well_position == "68/81"
        assert result.singularity_position == "81/68"
    
    def test_verify_well_period(self):
        """Test period and pattern."""
        result = self.well.verify_well()
        
        assert result.period_digits == 9
        assert result.repeating_pattern == "839506172"
    
    def test_verify_well_self_referential(self):
        """Test self-referential property."""
        result = self.well.verify_well()
        assert result.self_referential is True
    
    def test_verify_well_convergence(self):
        """Test convergence verification."""
        result = self.well.verify_well()
        assert result.convergence_verified is True
    
    def test_verify_well_math_properties(self):
        """Test mathematical properties in result."""
        result = self.well.verify_well()
        props = result.mathematical_properties
        
        assert "P_at_well" in props
        expected_exact = f"{P_AT_WELL_NUMERATOR}/{P_AT_WELL_DENOMINATOR}"
        assert props["P_at_well"]["exact"] == expected_exact
        
        assert "number_theory" in props
        assert props["number_theory"]["68"]["is_2_squared_times_17"] is True
        assert props["number_theory"]["81"]["is_3_to_4"] is True


class TestValidateFractalWell:
    """Test suite for the main validation function."""
    
    def test_validate_returns_dict(self):
        """Test that validation returns a dictionary."""
        result = validate_fractal_well(dps=100, verbose=False)
        assert isinstance(result, dict)
        assert "result" in result
        assert "success" in result
    
    def test_validate_success(self):
        """Test that validation succeeds."""
        result = validate_fractal_well(dps=100, verbose=False)
        assert result["success"] is True
    
    def test_validate_result_type(self):
        """Test that result contains FractalWellResult."""
        result = validate_fractal_well(dps=100, verbose=False)
        assert isinstance(result["result"], FractalWellResult)


class TestMathematicalIdentities:
    """Test suite for mathematical identities."""
    
    def test_68_equals_4_times_17(self):
        """Test 68 = 4 × 17."""
        assert 68 == 4 * 17
    
    def test_68_equals_2_squared_times_17(self):
        """Test 68 = 2² × 17."""
        assert 68 == 2**2 * 17
    
    def test_81_equals_3_to_4(self):
        """Test 81 = 3⁴."""
        assert 81 == 3**4
    
    def test_period_9_equals_3_squared(self):
        """Test period 9 = 3²."""
        assert 9 == 3**2
    
    def test_gcd_68_81_is_1(self):
        """Test gcd(68, 81) = 1 (coprime)."""
        from math import gcd
        assert gcd(68, 81) == 1
    
    def test_singularity_denominator(self):
        """Test 81² - 68² = 1937."""
        assert DENOMINATOR**2 - NUMERATOR**2 == P_AT_WELL_DENOMINATOR
        assert P_AT_WELL_DENOMINATOR == 1937
    
    def test_p_at_well_exact(self):
        """Test P(68/81) exact value."""
        # P(68/81) = 6561/1937
        assert P_AT_WELL_NUMERATOR == DENOMINATOR**2
        assert P_AT_WELL_NUMERATOR == 6561
        
        # Verify computed exact value
        expected = P_AT_WELL_NUMERATOR / P_AT_WELL_DENOMINATOR
        assert abs(expected - P_AT_WELL_EXACT) < 1e-15


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
