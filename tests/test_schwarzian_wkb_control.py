#!/usr/bin/env python3
"""
Tests for Schwarzian WKB Control Module

This module tests the complete 6-step derivation of the Schwarzian derivative
control for WKB approximations near turning points.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.schwarzian_wkb_control import (
    SchwarziannWKBController,
    SchwarziannWKBResult,
    run_validation_suite,
    PI, PI2, PI4
)


class TestPotentialQ:
    """Test suite for potential Q(y) = (π⁴/16) · y² / [log(1+y)]²."""
    
    def test_potential_positive_y(self):
        """Test Q(y) for positive y."""
        controller = SchwarziannWKBController()
        
        y_values = np.array([0.1, 1.0, 10.0, 100.0])
        Q_values = controller.Q(y_values)
        
        # Q should be positive
        assert np.all(Q_values > 0), "Q should be positive for y > 0"
        
        # Q should be increasing
        assert np.all(np.diff(Q_values) > 0), "Q should be increasing"
    
    def test_potential_asymptotic_behavior(self):
        """Test Q(y) ∼ (π⁴/16) · y² / (log y)² for large y."""
        controller = SchwarziannWKBController()
        
        y = 1000.0
        Q_y = controller.Q(y)
        
        # Theoretical asymptotic
        log_y = np.log(y)
        Q_asymptotic = (PI4 / 16) * y**2 / log_y**2
        
        # Should agree to within a few percent
        relative_error = abs(Q_y - Q_asymptotic) / Q_asymptotic
        assert relative_error < 0.05, f"Q asymptotic error {relative_error:.2e} too large"
    
    def test_potential_smoothing(self):
        """Test Q(y) smoothing for y < 0."""
        controller = SchwarziannWKBController()
        
        y_values = np.array([-2.0, -1.0, -0.5])
        Q_values = controller.Q(y_values)
        
        # Should be positive and decreasing (exponential decay)
        assert np.all(Q_values > 0), "Smoothed Q should be positive"
        assert np.all(np.diff(Q_values) > 0), "Smoothed Q should increase toward y=0"
    
    def test_potential_derivatives(self):
        """Test Q'(y), Q''(y), Q'''(y)."""
        controller = SchwarziannWKBController()
        
        y = 10.0
        Q_prime = controller.Q_derivative(y, order=1)
        Q_double_prime = controller.Q_derivative(y, order=2)
        Q_triple_prime = controller.Q_derivative(y, order=3)
        
        # All should be finite
        assert np.isfinite(Q_prime), "Q' should be finite"
        assert np.isfinite(Q_double_prime), "Q'' should be finite"
        assert np.isfinite(Q_triple_prime), "Q''' should be finite"
        
        # Q' should be positive (Q is increasing)
        assert Q_prime > 0, "Q' should be positive for y > 0"


class TestTurningPoint:
    """Test suite for turning point computation."""
    
    @pytest.mark.parametrize("lambda_", [10.0, 50.0, 100.0, 500.0, 1000.0])
    def test_turning_point_existence(self, lambda_):
        """Test that turning point exists and satisfies Q(y+) = λ."""
        controller = SchwarziannWKBController()
        
        y_plus = controller.compute_turning_point(lambda_)
        
        # y+ should be positive
        assert y_plus > 0, "Turning point should be positive"
        
        # Q(y+) should equal λ
        Q_yplus = controller.Q(y_plus)
        relative_error = abs(Q_yplus - lambda_) / lambda_
        assert relative_error < 1e-6, f"Q(y+) - λ error: {relative_error:.2e}"
    
    def test_turning_point_scaling(self):
        """Test y+ ∼ √λ · L scaling."""
        controller = SchwarziannWKBController()
        
        lambda_values = [100.0, 500.0, 1000.0]
        
        for lambda_ in lambda_values:
            y_plus = controller.compute_turning_point(lambda_)
            L = controller.compute_L(lambda_)
            
            # Theoretical scaling
            y_plus_theory = np.sqrt(lambda_) * L
            
            # Should agree within 20% for large λ
            relative_error = abs(y_plus - y_plus_theory) / y_plus_theory
            assert relative_error < 0.2, f"y+ scaling error {relative_error:.2e} at λ={lambda_}"


class TestCharacteristicScale:
    """Test suite for characteristic scale L computation."""
    
    def test_L_small_lambda(self):
        """Test L for small λ."""
        controller = SchwarziannWKBController()
        
        lambda_ = 0.5
        L = controller.compute_L(lambda_)
        
        # Should return default value for λ ≤ 1
        assert L == 1.0, "L should be 1.0 for λ ≤ 1"
    
    @pytest.mark.parametrize("lambda_", [10.0, 100.0, 1000.0])
    def test_L_asymptotic(self, lambda_):
        """Test L ≈ (2/π²) log λ for large λ."""
        controller = SchwarziannWKBController()
        
        L = controller.compute_L(lambda_)
        L_theory = (2 / PI2) * np.log(lambda_)
        
        # Should be close to theoretical value
        assert abs(L - L_theory) / L_theory < 0.3, f"L error at λ={lambda_}"


class TestLangerVariable:
    """Test suite for Langer variable ζ and its derivatives."""
    
    def test_zeta_prime_scaling(self):
        """Test ζ' ≈ 2^{1/3} λ^{1/6} / L^{2/3}."""
        controller = SchwarziannWKBController()
        
        lambda_ = 100.0
        L = controller.compute_L(lambda_)
        zeta_prime = controller.compute_zeta_prime(lambda_, L)
        
        # Theoretical value
        zeta_prime_theory = 2**(1/3) * lambda_**(1/6) / L**(2/3)
        
        # Should match exactly (it's the definition)
        assert abs(zeta_prime - zeta_prime_theory) < 1e-10, "ζ' definition mismatch"
    
    def test_zeta_prime_positive(self):
        """Test that ζ' > 0."""
        controller = SchwarziannWKBController()
        
        for lambda_ in [10.0, 100.0, 1000.0]:
            L = controller.compute_L(lambda_)
            zeta_prime = controller.compute_zeta_prime(lambda_, L)
            assert zeta_prime > 0, f"ζ' should be positive, got {zeta_prime}"


class TestSchwarziannDerivative:
    """Test suite for Schwarzian derivative {ζ, y}."""
    
    def test_schwarzian_finiteness(self):
        """Test that Schwarzian is finite away from singular points."""
        controller = SchwarziannWKBController()
        
        lambda_ = 100.0
        y_plus = controller.compute_turning_point(lambda_)
        L = controller.compute_L(lambda_)
        
        # Sample points around turning point
        y_samples = np.linspace(y_plus - L, y_plus + L, 50)
        y_samples = y_samples[y_samples > 0.01]  # Avoid y=0
        
        for y in y_samples:
            schwarzian = controller.compute_schwarzian(y, lambda_, y_plus, L)
            assert np.isfinite(schwarzian), f"Schwarzian not finite at y={y}"
    
    @pytest.mark.parametrize("lambda_", [50.0, 100.0, 500.0])
    def test_schwarzian_bound(self, lambda_):
        """Test |{ζ, y}| ≤ C / (1 + |ζ|³) bound."""
        controller = SchwarziannWKBController()
        
        y_plus = controller.compute_turning_point(lambda_)
        L = controller.compute_L(lambda_)
        
        C_bound, y_samples, schwarzian_values = controller.verify_schwarzian_bound(
            lambda_, y_plus, L
        )
        
        # C should be finite and positive
        assert np.isfinite(C_bound), "Schwarzian bound C should be finite"
        assert C_bound > 0, "Schwarzian bound C should be positive"
        
        # Verify bound holds at all sample points
        Q_prime_yplus = controller.Q_derivative(y_plus, 1)
        u_values = y_plus - y_samples
        zeta_values = -(Q_prime_yplus)**(1/3) * u_values
        
        bound_check = np.abs(schwarzian_values) * (1 + np.abs(zeta_values)**3)
        max_violation = np.max(bound_check) - C_bound
        
        # Allow small numerical error
        assert max_violation < 1e-6, f"Schwarzian bound violated by {max_violation}"


class TestWKBIntegral:
    """Test suite for WKB integral I(λ)."""
    
    @pytest.mark.parametrize("lambda_", [10.0, 50.0, 100.0])
    def test_wkb_integral_convergence(self, lambda_):
        """Test that WKB integral converges."""
        controller = SchwarziannWKBController()
        
        integral, error = controller.compute_wkb_integral(lambda_)
        
        # Should be finite
        assert np.isfinite(integral), "WKB integral should be finite"
        assert integral > 0, "WKB integral should be positive"
        
        # Error should be small
        assert error < 0.1 * abs(integral), "Integration error too large"
    
    @pytest.mark.parametrize("lambda_", [100.0, 500.0, 1000.0])
    def test_wkb_asymptotic_agreement(self, lambda_):
        """Test I(λ) ≈ (1/2) λ log λ - (1/2) λ + O(1)."""
        controller = SchwarziannWKBController()
        
        integral, _ = controller.compute_wkb_integral(lambda_)
        theoretical = controller.theoretical_wkb_asymptotic(lambda_)
        
        # Relative error should decrease as λ increases
        relative_error = abs(integral - theoretical) / abs(theoretical)
        
        # For large λ, should be within 10%
        assert relative_error < 0.1, f"WKB asymptotic error {relative_error:.2e} at λ={lambda_}"


class TestCompleteAnalysis:
    """Test suite for complete 6-step analysis."""
    
    def test_complete_analysis_runs(self):
        """Test that complete analysis runs without errors."""
        controller = SchwarziannWKBController()
        
        result = controller.run_complete_analysis(100.0, verbose=False)
        
        # Check result type
        assert isinstance(result, SchwarziannWKBResult), "Should return SchwarziannWKBResult"
        
        # Check all fields are finite
        assert np.isfinite(result.y_plus), "y+ should be finite"
        assert np.isfinite(result.L_value), "L should be finite"
        assert np.isfinite(result.zeta_prime), "ζ' should be finite"
        assert np.isfinite(result.schwarzian_max), "Schwarzian max should be finite"
        assert np.isfinite(result.error_bound), "Error bound should be finite"
        assert np.isfinite(result.integral_error), "Integral error should be finite"
        assert np.isfinite(result.wkb_integral), "WKB integral should be finite"
        assert np.isfinite(result.relative_error), "Relative error should be finite"
    
    @pytest.mark.parametrize("lambda_", [50.0, 100.0, 500.0])
    def test_error_bounds_reasonable(self, lambda_):
        """Test that error bounds are reasonable."""
        controller = SchwarziannWKBController()
        
        result = controller.run_complete_analysis(lambda_, verbose=False)
        
        # Error bound should be small
        assert result.error_bound < 10.0, f"Error bound {result.error_bound} too large"
        
        # Integral error should be bounded
        assert result.integral_error < 100.0, f"Integral error {result.integral_error} too large"
        
        # Relative error should be reasonable
        assert result.relative_error < 0.2, f"Relative error {result.relative_error} too large"


class TestValidationSuite:
    """Test suite for complete validation."""
    
    def test_validation_suite_runs(self):
        """Test that validation suite runs successfully."""
        lambda_values = [10.0, 50.0, 100.0]
        
        results = run_validation_suite(lambda_values, verbose=False)
        
        # Check structure
        assert 'results' in results
        assert 'max_relative_error' in results
        assert 'mean_relative_error' in results
        assert 'max_integral_error' in results
        assert 'all_tests_passed' in results
        
        # Check counts
        assert len(results['results']) == len(lambda_values)
    
    @pytest.mark.slow
    def test_validation_suite_accuracy(self):
        """Test validation suite achieves good accuracy."""
        lambda_values = [50.0, 100.0, 200.0, 500.0]
        
        results = run_validation_suite(lambda_values, verbose=False)
        
        # Should pass all tests
        assert results['all_tests_passed'], "Not all validation tests passed"
        
        # Max error should be small
        assert results['max_relative_error'] < 0.1, \
            f"Max relative error {results['max_relative_error']} too large"


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_lambda(self):
        """Test behavior for small λ."""
        controller = SchwarziannWKBController()
        
        lambda_ = 1.0
        result = controller.run_complete_analysis(lambda_, verbose=False)
        
        # Should complete without errors
        assert np.isfinite(result.y_plus)
        assert np.isfinite(result.wkb_integral)
    
    def test_large_lambda(self):
        """Test behavior for large λ."""
        controller = SchwarziannWKBController()
        
        lambda_ = 5000.0
        result = controller.run_complete_analysis(lambda_, verbose=False)
        
        # Should complete without errors
        assert np.isfinite(result.y_plus)
        assert np.isfinite(result.wkb_integral)
        
        # Asymptotic formula should be very accurate
        assert result.relative_error < 0.05, \
            f"Large λ should have small error, got {result.relative_error}"
    
    def test_smoothing_parameter(self):
        """Test different smoothing parameters."""
        for smoothing_scale in [0.5, 1.0, 2.0]:
            controller = SchwarziannWKBController(smoothing_scale=smoothing_scale)
            
            lambda_ = 100.0
            result = controller.run_complete_analysis(lambda_, verbose=False)
            
            # Should be stable
            assert np.isfinite(result.y_plus)
            assert result.relative_error < 0.15


class TestTheoreticalConsistency:
    """Test theoretical consistency checks."""
    
    def test_theorem_statement_verified(self):
        """Verify the main theorem statement."""
        controller = SchwarziannWKBController()
        
        lambda_ = 200.0
        result = controller.run_complete_analysis(lambda_, verbose=False)
        
        # 1. ζ' should be of order λ^{1/6} / L^{2/3}
        expected_zeta_prime = 2**(1/3) * lambda_**(1/6) / result.L_value**(2/3)
        assert abs(result.zeta_prime - expected_zeta_prime) < 1e-10
        
        # 2. Schwarzian should be bounded
        assert result.schwarzian_max < 100.0  # Reasonable bound
        
        # 3. Error integral should be finite
        assert result.integral_error < 100.0
        
        # 4. WKB should match asymptotic
        assert result.relative_error < 0.1
    
    def test_independence_of_lambda(self):
        """Test that Schwarzian bound constant is independent of λ."""
        controller = SchwarziannWKBController()
        
        lambda_values = [100.0, 500.0, 1000.0]
        C_bounds = []
        
        for lambda_ in lambda_values:
            y_plus = controller.compute_turning_point(lambda_)
            L = controller.compute_L(lambda_)
            C_bound, _, _ = controller.verify_schwarzian_bound(lambda_, y_plus, L)
            C_bounds.append(C_bound)
        
        # C should not vary wildly with λ
        C_mean = np.mean(C_bounds)
        C_std = np.std(C_bounds)
        
        # Standard deviation should be small relative to mean
        assert C_std / C_mean < 0.5, \
            f"Schwarzian bound C varies too much: {C_bounds}"


@pytest.mark.slow
class TestVisualization:
    """Test visualization functions."""
    
    def test_plot_creation(self, tmp_path):
        """Test that plots can be created."""
        controller = SchwarziannWKBController()
        
        lambda_values = [10.0, 50.0, 100.0]
        save_path = tmp_path / "test_schwarzian_plot.png"
        
        fig = controller.plot_schwarzian_analysis(lambda_values, save_path=str(save_path))
        
        # Check file was created
        assert save_path.exists(), "Plot file not created"
        
        # Check figure has correct structure
        assert len(fig.axes) == 4, "Should have 4 subplots"


# Integration test
@pytest.mark.slow
def test_full_integration():
    """Full integration test of the entire module."""
    print("\n" + "="*70)
    print("FULL INTEGRATION TEST")
    print("="*70)
    
    # Run validation suite
    lambda_values = [10.0, 50.0, 100.0, 200.0, 500.0]
    results = run_validation_suite(lambda_values, verbose=True)
    
    # Should pass
    assert results['all_tests_passed'], "Integration test failed"
    
    # Check all results
    for i, result in enumerate(results['results']):
        lambda_ = result.lambda_
        print(f"\nλ = {lambda_}:")
        print(f"  y+ = {result.y_plus:.6f}")
        print(f"  L = {result.L_value:.6f}")
        print(f"  ζ' = {result.zeta_prime:.6f}")
        print(f"  max |{{ζ, y}}| = {result.schwarzian_max:.6e}")
        print(f"  Relative error = {result.relative_error:.2e}")
    
    print("\n" + "="*70)
    print("✓ FULL INTEGRATION TEST PASSED")
    print("="*70)


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
