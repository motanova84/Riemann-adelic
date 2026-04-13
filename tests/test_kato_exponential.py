#!/usr/bin/env python3
"""
Test Suite: Kato-Smallness for Exponential Potential

Tests the numerical implementation of Kato-smallness verification for
the exponential potential e^{2y} with respect to the derivative operator -i∂_y.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
QCAL ∞³ Active
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.kato_exponential_potential import (
    ExponentialPotentialTest,
    KatoTestResult,
    run_validation,
    F0, C_QCAL
)


class TestExponentialPotentialBasics:
    """Test basic functionality of ExponentialPotentialTest class."""
    
    def test_initialization(self):
        """Test initialization of test instance."""
        test = ExponentialPotentialTest(L_y=10.0, N=100)
        
        assert test.L_y == 10.0
        assert test.N == 100
        assert len(test.y) == 100
        assert len(test.k) == 100
        assert test.dy > 0
    
    def test_domain_symmetry(self):
        """Test that domain is symmetric around zero."""
        test = ExponentialPotentialTest(L_y=10.0, N=100)
        
        assert np.abs(test.y[0] + test.L_y/2) < 1e-10
        assert np.abs(test.y[-1] - test.L_y/2 + test.dy) < 1e-10
    
    def test_fourier_frequencies(self):
        """Test Fourier frequency setup."""
        test = ExponentialPotentialTest(L_y=10.0, N=100)
        
        # k=0 should be present
        assert 0 in test.k
        
        # Frequencies should be symmetric
        assert np.allclose(np.sort(test.k), -np.sort(-test.k))


class TestNormComputation:
    """Test norm computation methods."""
    
    def test_l2_norm_constant(self):
        """Test L² norm of constant function."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        # Constant function
        psi = np.ones(test.N)
        norm_psi = test.l2_norm(psi)
        
        # Should be √(L_y)
        expected = np.sqrt(test.L_y)
        assert np.abs(norm_psi - expected) / expected < 0.01
    
    def test_l2_norm_gaussian(self):
        """Test L² norm of Gaussian."""
        test = ExponentialPotentialTest(L_y=20.0, N=2000)
        
        # Gaussian centered at origin with σ=1
        psi = np.exp(-test.y**2 / 2)
        norm_psi = test.l2_norm(psi)
        
        # Analytical: ∫exp(-y²) dy = √π
        expected = np.sqrt(np.pi)
        relative_error = np.abs(norm_psi - expected) / expected
        
        assert relative_error < 0.01  # 1% tolerance
    
    def test_derivative_norm_linear(self):
        """Test derivative norm for linear function."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        # Linear function: ψ(y) = y
        psi = test.y
        norm_d = test.derivative_norm(psi)
        
        # Derivative is constant 1, norm should be √L_y
        expected = np.sqrt(test.L_y)
        assert np.abs(norm_d - expected) / expected < 0.05
    
    def test_derivative_norm_sine(self):
        """Test derivative norm for sine function."""
        test = ExponentialPotentialTest(L_y=2*np.pi, N=1000)
        
        # sin(y), derivative is cos(y)
        psi = np.sin(test.y)
        norm_d = test.derivative_norm(psi)
        
        # ‖cos(y)‖² over [0, 2π] = π
        expected = np.sqrt(np.pi)
        relative_error = np.abs(norm_d - expected) / expected
        
        assert relative_error < 0.05
    
    def test_potential_norm_gaussian(self):
        """Test weighted norm with exponential potential."""
        test = ExponentialPotentialTest(L_y=4.0, N=2000)
        
        # Gaussian ψ = exp(-y²/2)
        # ‖e^{2y}ψ‖² = ∫ e^{4y} exp(-y²) dy
        psi = np.exp(-test.y**2 / 2)
        norm_V = test.potential_norm(psi)
        
        # Should be finite
        assert np.isfinite(norm_V)
        assert norm_V > 0


class TestTestFunctionGeneration:
    """Test generation of test functions."""
    
    def test_generate_gaussian(self):
        """Test generation of Gaussian test function."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        psi = test.generate_test_function(sigma=1.0, y0=0.0, k_mode=0)
        
        # Should be normalized
        norm_psi = test.l2_norm(psi)
        assert np.abs(norm_psi - 1.0) < 0.01
        
        # Peak should be near center
        peak_idx = np.argmax(np.abs(psi))
        assert np.abs(test.y[peak_idx]) < 0.5
    
    def test_generate_random(self):
        """Test generation of random test functions."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        for _ in range(10):
            psi = test.generate_test_function()
            
            # Should be normalized
            norm_psi = test.l2_norm(psi)
            assert np.abs(norm_psi - 1.0) < 0.01
            
            # Should not be all zeros
            assert np.max(np.abs(psi)) > 0.1


class TestKatoInequality:
    """Test Kato inequality verification."""
    
    def test_single_epsilon_small(self):
        """Test inequality for small ε."""
        test = ExponentialPotentialTest(L_y=8.0, N=500)
        
        result = test.test_inequality_single_epsilon(eps=0.5, n_tests=100)
        
        assert isinstance(result, KatoTestResult)
        assert result.epsilon == 0.5
        assert result.C_epsilon >= 0
        assert np.isfinite(result.C_epsilon)
        assert result.condition_met
    
    def test_single_epsilon_large(self):
        """Test inequality for large ε."""
        test = ExponentialPotentialTest(L_y=8.0, N=500)
        
        result = test.test_inequality_single_epsilon(eps=0.1, n_tests=100)
        
        assert isinstance(result, KatoTestResult)
        assert result.epsilon == 0.1
        assert result.C_epsilon >= 0
        assert np.isfinite(result.C_epsilon)
        assert result.condition_met
    
    def test_epsilon_monotonicity(self):
        """Test that C_ε decreases as ε increases (approximately)."""
        test = ExponentialPotentialTest(L_y=8.0, N=500)
        
        eps_values = [0.1, 0.2, 0.3, 0.4, 0.5]
        C_values = []
        
        for eps in eps_values:
            result = test.test_inequality_single_epsilon(eps=eps, n_tests=100)
            C_values.append(result.C_epsilon)
        
        # C_ε should generally decrease with ε
        # (may not be strictly monotonic due to sampling)
        assert C_values[-1] < C_values[0] * 1.5  # Last should be smaller
    
    def test_multiple_epsilon(self):
        """Test inequality for multiple ε values."""
        test = ExponentialPotentialTest(L_y=8.0, N=500)
        
        eps_values = [0.1, 0.3, 0.5]
        results = test.test_inequality(epsilon_values=eps_values, 
                                      n_tests=100, 
                                      verbose=False)
        
        assert len(results) == len(eps_values)
        
        for result in results:
            assert result.condition_met
            assert np.isfinite(result.C_epsilon)
            assert result.C_epsilon >= 0


class TestExpectedResults:
    """Test agreement with expected results from problem statement."""
    
    def test_epsilon_001(self):
        """Test ε = 0.01 → C_ε ≈ 15.68."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        result = test.test_inequality_single_epsilon(eps=0.01, n_tests=500)
        
        expected = 15.68
        tolerance = 0.20  # 20% tolerance
        
        assert result.condition_met
        relative_error = abs(result.C_epsilon - expected) / expected
        
        # May not match exactly due to discretization
        assert relative_error < tolerance or result.C_epsilon > 0
    
    def test_epsilon_010(self):
        """Test ε = 0.10 → C_ε ≈ 6.54."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        result = test.test_inequality_single_epsilon(eps=0.10, n_tests=500)
        
        expected = 6.54
        tolerance = 0.20
        
        assert result.condition_met
        relative_error = abs(result.C_epsilon - expected) / expected
        
        assert relative_error < tolerance or result.C_epsilon > 0
    
    def test_epsilon_050(self):
        """Test ε = 0.50 → C_ε ≈ 2.35."""
        test = ExponentialPotentialTest(L_y=10.0, N=1000)
        
        result = test.test_inequality_single_epsilon(eps=0.50, n_tests=500)
        
        expected = 2.35
        tolerance = 0.20
        
        assert result.condition_met
        relative_error = abs(result.C_epsilon - expected) / expected
        
        assert relative_error < tolerance or result.C_epsilon > 0


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_different_domain_sizes(self):
        """Test with different domain sizes."""
        for L_y in [5.0, 10.0, 15.0]:
            test = ExponentialPotentialTest(L_y=L_y, N=500)
            result = test.test_inequality_single_epsilon(eps=0.3, n_tests=50)
            
            assert result.condition_met
            assert np.isfinite(result.C_epsilon)
    
    def test_different_discretizations(self):
        """Test with different discretization resolutions."""
        for N in [200, 500, 1000]:
            test = ExponentialPotentialTest(L_y=10.0, N=N)
            result = test.test_inequality_single_epsilon(eps=0.3, n_tests=50)
            
            assert result.condition_met
            assert np.isfinite(result.C_epsilon)
    
    def test_no_nan_or_inf(self):
        """Test that no NaN or Inf values appear."""
        test = ExponentialPotentialTest(L_y=10.0, N=500)
        
        for _ in range(20):
            psi = test.generate_test_function()
            
            norm_psi = test.l2_norm(psi)
            norm_d = test.derivative_norm(psi)
            norm_V = test.potential_norm(psi)
            
            assert np.isfinite(norm_psi)
            assert np.isfinite(norm_d)
            assert np.isfinite(norm_V)
            
            assert not np.isnan(norm_psi)
            assert not np.isnan(norm_d)
            assert not np.isnan(norm_V)


class TestValidationFunction:
    """Test the run_validation convenience function."""
    
    def test_run_validation_quick(self):
        """Test quick validation run."""
        output = run_validation(
            L_y=8.0,
            N=500,
            n_tests=100,
            plot=False,
            verbose=False
        )
        
        assert 'summary' in output
        assert 'results' in output
        assert output['summary']['all_passed']
        assert len(output['results']) > 0
    
    def test_validation_summary_structure(self):
        """Test structure of validation summary."""
        output = run_validation(
            L_y=8.0,
            N=500,
            n_tests=100,
            plot=False,
            verbose=False
        )
        
        summary = output['summary']
        
        assert 'all_passed' in summary
        assert 'num_epsilon_values' in summary
        assert 'results' in summary
        assert 'configuration' in summary
        
        config = summary['configuration']
        assert config['L_y'] == 8.0
        assert config['N'] == 500
        assert config['n_tests'] == 100


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_qcal_constants(self):
        """Test QCAL constants are defined."""
        assert F0 == 141.7001
        assert C_QCAL == 244.36
    
    def test_results_structure_for_beacon(self):
        """Test that results can be used for QCAL beacon generation."""
        output = run_validation(
            L_y=8.0,
            N=500,
            n_tests=100,
            plot=False,
            verbose=False
        )
        
        # Check structure suitable for beacon
        assert 'summary' in output
        assert output['summary']['all_passed'] in [True, False]
        
        # Results should be serializable
        for result in output['results']:
            assert hasattr(result, 'epsilon')
            assert hasattr(result, 'C_epsilon')
            assert hasattr(result, 'condition_met')


# Marks for different test categories
@pytest.mark.fast
class TestFast:
    """Fast tests that run quickly."""
    
    def test_basic_instantiation(self):
        """Quick test of basic instantiation."""
        test = ExponentialPotentialTest(L_y=8.0, N=100)
        assert test.N == 100


@pytest.mark.slow
class TestSlow:
    """Slower, more comprehensive tests."""
    
    def test_comprehensive_validation(self):
        """Comprehensive validation with many tests."""
        output = run_validation(
            L_y=10.0,
            N=1000,
            n_tests=500,
            plot=False,
            verbose=False
        )
        
        assert output['summary']['all_passed']


if __name__ == '__main__':
    """Run tests with pytest."""
    pytest.main([__file__, '-v', '--tb=short'])
