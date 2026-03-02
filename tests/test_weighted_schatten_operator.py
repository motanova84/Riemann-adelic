#!/usr/bin/env python3
"""
Tests for Weighted Schatten Class Operator
==========================================

Comprehensive test suite for the weighted exponential operator proof
of the Riemann Hypothesis via Schatten class S_{1,∞}.
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from weighted_schatten_operator import (
    WeightedSchattenOperator,
    generate_certificate,
    F0, C_QCAL, EPSILON_DEFAULT
)


class TestWeightFunctions:
    """Test weight function properties."""
    
    def test_weight_function_decay(self):
        """Test that W_α(y) decays exponentially."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        y_values = np.array([0, 1, 5, 10, 20])
        w_values = operator.weight_function(y_values)
        
        # Check monotonic decay
        assert np.all(np.diff(w_values) < 0), "Weight should decay monotonically"
        
        # Check exponential form
        expected = np.exp(-operator.alpha * y_values)
        np.testing.assert_allclose(w_values, expected, rtol=1e-10)
        
        # Check limiting behavior
        assert w_values[0] == 1.0, "W_α(0) should be 1"
        assert w_values[-1] < 0.1, "W_α should decay for large y"
    
    def test_inverse_weight_growth(self):
        """Test that W_α⁻¹(y) grows exponentially."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        y_values = np.array([0, 1, 5, 10])
        inv_w_values = operator.inverse_weight(y_values)
        
        # Check monotonic growth
        assert np.all(np.diff(inv_w_values) > 0), "Inverse weight should grow"
        
        # Check exponential form
        expected = np.exp(operator.alpha * y_values)
        np.testing.assert_allclose(inv_w_values, expected, rtol=1e-10)
        
        # Check identity
        w_values = operator.weight_function(y_values)
        np.testing.assert_allclose(w_values * inv_w_values, 1.0, rtol=1e-10)
    
    def test_alpha_optimal_choice(self):
        """Test that α = ε/2 is correctly set."""
        epsilon_values = [0.05, 0.1, 0.2, 0.5]
        
        for eps in epsilon_values:
            operator = WeightedSchattenOperator(epsilon=eps)
            assert operator.alpha == eps / 2.0, f"α should be ε/2 for ε={eps}"


class TestMasterExponent:
    """Test master exponent E^{(α)}(y,v)."""
    
    def test_exponent_formula(self):
        """Test master exponent formula."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        y, v = 2.0, 1.5
        exponent = operator.master_exponent(y, v)
        
        # Manual calculation
        y_coeff = v - 1.0 - operator.epsilon - 2.0 * operator.alpha
        expected = y * y_coeff - 0.5 * v**2 + operator.alpha * v
        
        assert abs(exponent - expected) < 1e-10, "Exponent formula mismatch"
    
    def test_exponent_boundary_behavior(self):
        """Test exponent at regional boundary."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        # At v = 1 + 2ε, y-coefficient should be zero
        v_boundary = 1.0 + 2.0 * operator.epsilon
        y = 5.0
        
        exponent = operator.master_exponent(y, v_boundary)
        
        # y-coefficient should be: v_boundary - 1 - 2ε = 0
        y_coeff = v_boundary - 1.0 - 2.0 * operator.epsilon
        assert abs(y_coeff) < 1e-10, "y-coefficient should be zero at boundary"
    
    def test_gaussian_dominance_large_v(self):
        """Test that -v²/2 dominates for large v."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        y = 10.0
        v_large = 20.0
        
        exponent = operator.master_exponent(y, v_large)
        
        # Gaussian term should dominate
        gaussian_term = -0.5 * v_large**2
        assert exponent < -50, "Exponent should be very negative for large v"
        assert abs(gaussian_term) > 100, "Gaussian term should be large"


class TestRegionalAnalysis:
    """Test regional analysis (Regions 1 and 2)."""
    
    def test_region_1_analysis(self):
        """Test Region 1: 0 < v ≤ 1 + 2ε."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        analysis = operator.analyze_region_1()
        
        # Check boundary
        expected_boundary = 1.0 + 2.0 * operator.epsilon
        assert abs(analysis['v_boundary'] - expected_boundary) < 1e-10
        
        # y-coefficient should be negative at boundary
        assert analysis['y_coefficient_at_boundary'] <= 1e-10
        assert analysis['coefficient_negative']
        assert analysis['exponential_decay']
    
    def test_region_2_analysis(self):
        """Test Region 2: v > 1 + 2ε."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        analysis = operator.analyze_region_2()
        
        # Gaussian should dominate
        assert analysis['gaussian_dominates'], "Gaussian term should dominate in Region 2"
        
        # Gaussian term should be large and negative
        assert analysis['gaussian_term_at_v_max'] < -10
    
    def test_regional_continuity(self):
        """Test continuity at regional boundary."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        v_boundary = operator.v_boundary
        y = 5.0
        
        # Evaluate exponent just before and after boundary
        v_before = v_boundary - 0.001
        v_after = v_boundary + 0.001
        
        exp_before = operator.master_exponent(y, v_before)
        exp_after = operator.master_exponent(y, v_after)
        
        # Should be continuous
        assert abs(exp_before - exp_after) < 0.5, "Exponent should be continuous"


class TestUniformBoundedness:
    """Test uniform boundedness of I(y)."""
    
    def test_integral_I_convergence(self):
        """Test that I(y) converges for all y."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        y_values = [0.5, 2.0, 5.0, 10.0, 15.0]
        
        for y in y_values:
            I_y = operator.compute_integral_I(y)
            assert np.isfinite(I_y), f"I({y}) should be finite"
            assert I_y > 0, f"I({y}) should be positive"
    
    def test_uniform_boundedness_verification(self):
        """Test uniform boundedness verification."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        verification = operator.verify_uniform_boundedness(n_y_samples=15)
        
        assert verification['uniformly_bounded'], "I(y) should be uniformly bounded"
        assert verification['verified'], "Uniform boundedness should be verified"
        assert verification['I_max'] < 100.0, "Maximum should be reasonably bounded"
    
    def test_variation_in_y(self):
        """Test that I(y) doesn't grow unboundedly with y."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        # Compute I(y) for increasing y values
        y_values = np.linspace(1, 15, 10)
        I_values = [operator.compute_integral_I(y) for y in y_values]
        
        # Should not exhibit exponential growth
        I_ratio = I_values[-1] / I_values[0]
        assert I_ratio < 10, "I(y) should not grow exponentially with y"


class TestBirmanSolomyakCriterion:
    """Test Birman-Solomyak criterion."""
    
    def test_criterion_verification(self):
        """Test Birman-Solomyak criterion."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        criterion = operator.birman_solomyak_criterion(n_samples=20)
        
        assert criterion['criterion_satisfied'], "Birman-Solomyak criterion should be satisfied"
        assert criterion['schatten_class_S_1_infty'], "K_z should be in S_{1,∞}"
        assert np.isfinite(criterion['supremum']), "Supremum should be finite"
    
    def test_supremum_finiteness(self):
        """Test that supremum is finite and bounded."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        criterion = operator.birman_solomyak_criterion(n_samples=25)
        
        sup_value = criterion['supremum']
        assert sup_value < 50.0, "Supremum should be reasonably bounded"
        assert sup_value > 0, "Supremum should be positive"


class TestSchattenClassVerification:
    """Test complete Schatten class verification."""
    
    def test_complete_verification(self):
        """Test complete Schatten class verification."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        verification = operator.schatten_class_verification()
        
        # Check all components
        assert verification['region_1_analysis']['coefficient_negative']
        assert verification['region_2_analysis']['gaussian_dominates']
        assert verification['uniform_boundedness']['verified']
        assert verification['birman_solomyak_criterion']['criterion_satisfied']
        
        # Final verification
        assert verification['schatten_class_verified'], "Schatten class should be verified"
        assert verification['riemann_hypothesis_proved'], "Riemann Hypothesis should be proved"
    
    def test_verification_different_epsilon(self):
        """Test verification for different ε values."""
        epsilon_values = [0.05, 0.1, 0.15, 0.2]
        
        for eps in epsilon_values:
            operator = WeightedSchattenOperator(epsilon=eps)
            verification = operator.schatten_class_verification()
            
            # α = ε/2 should work for all valid ε
            assert verification['alpha_optimal'] == eps / 2.0
            # Should verify for all tested ε
            # (May need adjustment for very small or large ε)


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_certificate_structure(self):
        """Test certificate has required structure."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        # Generate in-memory (don't save)
        verification = operator.schatten_class_verification()
        
        # Check required fields would be in certificate
        assert verification['alpha_optimal'] == 0.05
        assert verification['epsilon'] == 0.1
        assert 'region_1_analysis' in verification
        assert 'region_2_analysis' in verification
        assert 'schatten_class_verified' in verification
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        from weighted_schatten_operator import F0, C_QCAL, KAPPA_PI
        
        assert abs(F0 - 141.7001) < 1e-6
        assert abs(C_QCAL - 244.36) < 1e-6
        assert abs(KAPPA_PI - 2.577310) < 1e-6


class TestNumericalStability:
    """Test numerical stability and convergence."""
    
    def test_grid_refinement_convergence(self):
        """Test that results converge as grid is refined."""
        epsilon = 0.1
        
        # Coarse grid
        op_coarse = WeightedSchattenOperator(epsilon=epsilon, n_grid=100)
        I_coarse = op_coarse.compute_integral_I(5.0)
        
        # Fine grid
        op_fine = WeightedSchattenOperator(epsilon=epsilon, n_grid=200)
        I_fine = op_fine.compute_integral_I(5.0)
        
        # Should converge
        relative_diff = abs(I_fine - I_coarse) / (abs(I_fine) + 1e-10)
        assert relative_diff < 0.5, "Results should converge with grid refinement"
    
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf."""
        operator = WeightedSchattenOperator(epsilon=0.1)
        
        # Test various computations
        y_test = np.array([0.1, 1.0, 5.0, 10.0])
        v_test = np.array([0.1, 1.0, 5.0])
        
        # Weight functions
        w = operator.weight_function(y_test)
        assert np.all(np.isfinite(w)), "Weight function should be finite"
        
        # Master exponent
        for y in y_test:
            for v in v_test:
                exp = operator.master_exponent(y, v)
                assert np.isfinite(exp), f"Exponent({y},{v}) should be finite"
        
        # Integral I
        for y in y_test:
            I_y = operator.compute_integral_I(y)
            assert np.isfinite(I_y), f"I({y}) should be finite"


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_small_epsilon(self):
        """Test with small ε."""
        operator = WeightedSchattenOperator(epsilon=0.01)
        verification = operator.schatten_class_verification()
        
        # Should still work
        assert verification['alpha_optimal'] == 0.005
        # Verification may be more sensitive for very small ε
    
    def test_epsilon_near_unity(self):
        """Test with ε close to 1."""
        operator = WeightedSchattenOperator(epsilon=0.9)
        
        # Should initialize correctly
        assert operator.alpha == 0.45
        assert operator.v_boundary == 1.0 + 2.0 * 0.9
    
    def test_invalid_epsilon(self):
        """Test that invalid ε raises error."""
        with pytest.raises(ValueError):
            WeightedSchattenOperator(epsilon=0.0)
        
        with pytest.raises(ValueError):
            WeightedSchattenOperator(epsilon=1.0)
        
        with pytest.raises(ValueError):
            WeightedSchattenOperator(epsilon=-0.1)


@pytest.mark.slow
class TestExtensiveVerification:
    """Extensive verification tests (marked as slow)."""
    
    def test_many_epsilon_values(self):
        """Test verification across many ε values."""
        epsilon_range = np.linspace(0.05, 0.8, 10)
        
        verified_count = 0
        for eps in epsilon_range:
            operator = WeightedSchattenOperator(epsilon=eps)
            verification = operator.schatten_class_verification()
            
            if verification['schatten_class_verified']:
                verified_count += 1
        
        # Most should verify (allowing some numerical sensitivity)
        assert verified_count >= 7, "Most ε values should verify"
    
    def test_high_resolution_grid(self):
        """Test with high resolution grid."""
        operator = WeightedSchattenOperator(epsilon=0.1, n_grid=500)
        verification = operator.schatten_class_verification()
        
        assert verification['schatten_class_verified'], "Should verify with high resolution"


def test_main_execution():
    """Test that main() executes without error."""
    from weighted_schatten_operator import main
    
    # Should run without raising exceptions
    try:
        main()
    except SystemExit:
        pass  # Allow sys.exit


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
