#!/usr/bin/env python3
"""
Unit Tests for Spectral Counting Operator
=========================================

Comprehensive test suite for spectral counting theorem validation.

Tests:
1. Potential Q(y) and derivative
2. Turning point computation
3. WKB integral I(λ)
4. Asymptotic decomposition
5. Spectral counting N(λ)
6. Error bounds O(log λ)
7. Edge cases and numerical stability

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SPECTRAL-COUNTING-TESTS v1.0
Date: February 16, 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from core.spectral_counting_operator import (
    SpectralCountingOperator,
    SpectralCountingResult,
    compute_spectral_count
)


class TestPotential:
    """Tests for potential Q(y) and its derivative."""
    
    def test_potential_at_zero(self):
        """Test Q(0) = 0."""
        operator = SpectralCountingOperator()
        assert operator.Q(0.0) == 0.0
    
    def test_potential_positive(self):
        """Test Q(y) > 0 for y > 0."""
        operator = SpectralCountingOperator()
        y_values = [0.1, 1.0, 10.0, 100.0]
        for y in y_values:
            Q_val = operator.Q(y)
            assert Q_val > 0, f"Q({y}) should be positive, got {Q_val}"
    
    def test_potential_grows_with_y(self):
        """Test Q(y) is increasing for large y."""
        operator = SpectralCountingOperator()
        y_values = [10.0, 20.0, 50.0, 100.0]
        Q_values = [operator.Q(y) for y in y_values]
        
        for i in range(len(Q_values) - 1):
            assert Q_values[i+1] > Q_values[i], \
                f"Q should be increasing: Q({y_values[i]}) = {Q_values[i]}, " \
                f"Q({y_values[i+1]}) = {Q_values[i+1]}"
    
    def test_derivative_exists(self):
        """Test that Q'(y) can be computed."""
        operator = SpectralCountingOperator()
        y_values = [1.0, 10.0, 100.0]
        for y in y_values:
            Q_prime = operator.Q_derivative(y)
            assert np.isfinite(Q_prime), f"Q'({y}) should be finite"


class TestTurningPoint:
    """Tests for turning point computation."""
    
    def test_turning_point_exists(self):
        """Test that turning point can be found."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 100.0, 1000.0]
        for lambda_val in lambda_values:
            y_plus = operator.find_turning_point(lambda_val)
            assert y_plus > 0, f"y₊({lambda_val}) should be positive"
            assert np.isfinite(y_plus), f"y₊({lambda_val}) should be finite"
    
    def test_turning_point_satisfies_equation(self):
        """Test Q(y₊) = λ."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 100.0, 1000.0]
        for lambda_val in lambda_values:
            y_plus = operator.find_turning_point(lambda_val)
            Q_at_y_plus = operator.Q(y_plus)
            relative_error = abs(Q_at_y_plus - lambda_val) / lambda_val
            assert relative_error < 1e-6, \
                f"Q(y₊) should equal λ: Q({y_plus}) = {Q_at_y_plus}, λ = {lambda_val}"
    
    def test_turning_point_asymptotics(self):
        """Test y₊ ~ √λ log λ for large λ."""
        operator = SpectralCountingOperator()
        lambda_val = 10000.0
        y_plus = operator.find_turning_point(lambda_val)
        
        # Asymptotic estimate
        log_lambda = np.log(lambda_val)
        y_plus_asymptotic = np.sqrt(lambda_val) * log_lambda
        
        relative_error = abs(y_plus - y_plus_asymptotic) / y_plus_asymptotic
        assert relative_error < 0.2, \
            f"y₊ should approach √λ log λ: y₊ = {y_plus}, " \
            f"asymptotic = {y_plus_asymptotic}, error = {relative_error:.3%}"
    
    def test_invalid_lambda_raises_error(self):
        """Test that invalid λ values raise errors."""
        operator = SpectralCountingOperator()
        with pytest.raises(ValueError):
            operator.find_turning_point(0.0)
        with pytest.raises(ValueError):
            operator.find_turning_point(-10.0)


class TestWKBIntegral:
    """Tests for WKB integral I(λ)."""
    
    def test_integral_positive(self):
        """Test I(λ) > 0."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 100.0, 1000.0]
        for lambda_val in lambda_values:
            I_lambda = operator.compute_I_lambda(lambda_val)
            assert I_lambda > 0, f"I({lambda_val}) should be positive, got {I_lambda}"
    
    def test_integral_grows_with_lambda(self):
        """Test I(λ) is increasing."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 50.0, 100.0, 500.0]
        I_values = [operator.compute_I_lambda(lam) for lam in lambda_values]
        
        for i in range(len(I_values) - 1):
            assert I_values[i+1] > I_values[i], \
                f"I(λ) should be increasing: I({lambda_values[i]}) = {I_values[i]}, " \
                f"I({lambda_values[i+1]}) = {I_values[i+1]}"
    
    def test_integral_with_provided_turning_point(self):
        """Test that providing y₊ gives same result."""
        operator = SpectralCountingOperator()
        lambda_val = 1000.0
        
        # Compute without providing y₊
        I_auto = operator.compute_I_lambda(lambda_val)
        
        # Compute with provided y₊
        y_plus = operator.find_turning_point(lambda_val)
        I_manual = operator.compute_I_lambda(lambda_val, y_plus=y_plus)
        
        assert abs(I_auto - I_manual) < 1e-6, \
            f"Results should match: I_auto = {I_auto}, I_manual = {I_manual}"


class TestAsymptoticDecomposition:
    """Tests for asymptotic decomposition I(λ) = I_asymptotic + J(λ)."""
    
    def test_asymptotic_decomposition(self):
        """Test I(λ) = I_asymptotic + J(λ)."""
        operator = SpectralCountingOperator()
        lambda_val = 1000.0
        
        I_full = operator.compute_I_lambda(lambda_val)
        I_asymptotic, J_lambda = operator.compute_I_asymptotic(lambda_val)
        
        I_reconstructed = I_asymptotic + J_lambda
        relative_error = abs(I_full - I_reconstructed) / I_full
        
        assert relative_error < 1e-6, \
            f"Decomposition should be exact: I_full = {I_full}, " \
            f"I_asymptotic + J = {I_reconstructed}"
    
    def test_asymptotic_formula(self):
        """Test I_asymptotic = (λ/2) log λ - (λ/2)."""
        operator = SpectralCountingOperator()
        lambda_val = 1000.0
        
        I_asymptotic, _ = operator.compute_I_asymptotic(lambda_val)
        expected = 0.5 * lambda_val * np.log(lambda_val) - 0.5 * lambda_val
        
        assert abs(I_asymptotic - expected) < 1e-10, \
            f"Asymptotic formula incorrect: got {I_asymptotic}, expected {expected}"


class TestSpectralCounting:
    """Tests for spectral counting N(λ)."""
    
    def test_count_positive(self):
        """Test N(λ) ≥ 0."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 100.0, 1000.0]
        for lambda_val in lambda_values:
            N_lambda = operator.count_eigenvalues(lambda_val)
            assert N_lambda >= 0, f"N({lambda_val}) should be non-negative, got {N_lambda}"
    
    def test_count_grows_with_lambda(self):
        """Test N(λ) is increasing."""
        operator = SpectralCountingOperator()
        lambda_values = [10.0, 50.0, 100.0, 500.0]
        N_values = [operator.count_eigenvalues(lam) for lam in lambda_values]
        
        for i in range(len(N_values) - 1):
            assert N_values[i+1] >= N_values[i], \
                f"N(λ) should be increasing: N({lambda_values[i]}) = {N_values[i]}, " \
                f"N({lambda_values[i+1]}) = {N_values[i+1]}"
    
    def test_theoretical_count_formula(self):
        """Test theoretical count (λ/2π) log λ - (λ/2π)."""
        operator = SpectralCountingOperator()
        lambda_val = 1000.0
        
        N_theoretical = operator.theoretical_count(lambda_val)
        expected = (lambda_val / (2.0 * np.pi)) * np.log(lambda_val) - (lambda_val / (2.0 * np.pi))
        
        assert abs(N_theoretical - expected) < 1e-10, \
            f"Theoretical count incorrect: got {N_theoretical}, expected {expected}"
    
    def test_count_matches_theoretical(self):
        """Test N(λ) ≈ N_theoretical for large λ."""
        operator = SpectralCountingOperator()
        lambda_val = 10000.0
        
        N_lambda = operator.count_eigenvalues(lambda_val)
        N_theoretical = operator.theoretical_count(lambda_val)
        
        relative_error = abs(N_lambda - N_theoretical) / N_theoretical
        assert relative_error < 0.01, \
            f"Counts should match: N = {N_lambda}, N_theoretical = {N_theoretical}, " \
            f"error = {relative_error:.3%}"


class TestErrorBounds:
    """Tests for error bounds and O(log λ) criterion."""
    
    def test_error_normalized_bounded(self):
        """Test error/log(λ) is bounded."""
        operator = SpectralCountingOperator()
        lambda_values = np.logspace(1, 4, 20)  # 10 to 10000
        
        for lambda_val in lambda_values:
            result = operator.compute(lambda_val)
            assert abs(result.error_normalized) < 1.0, \
                f"error/log(λ) should be O(1): got {result.error_normalized} at λ={lambda_val}"
    
    def test_asymptotic_behavior_validated(self):
        """Test complete asymptotic behavior validation."""
        operator = SpectralCountingOperator()
        lambda_values = np.logspace(1, 4, 30)
        
        validation = operator.validate_asymptotic_behavior(lambda_values)
        
        assert validation["status"] == "success", "Validation should succeed"
        assert validation["asymptotic_criterion_satisfied"], \
            "Asymptotic criterion should be satisfied"
        assert validation["error_normalized"]["bounded"], \
            "Error should be bounded"


class TestCompleteComputation:
    """Tests for complete computation with all diagnostics."""
    
    def test_compute_returns_result(self):
        """Test that compute returns valid result."""
        operator = SpectralCountingOperator()
        result = operator.compute(100.0)
        
        assert isinstance(result, SpectralCountingResult)
        assert result.converged
        assert result.lambda_val == 100.0
        assert result.y_plus > 0
        assert result.I_lambda > 0
        assert result.N_lambda >= 0
    
    def test_compute_caching(self):
        """Test that caching works correctly."""
        operator = SpectralCountingOperator()
        lambda_val = 100.0
        
        # First call
        result1 = operator.compute(lambda_val, use_cache=True)
        
        # Second call should use cache
        result2 = operator.compute(lambda_val, use_cache=True)
        
        # Results should be identical
        assert result1.I_lambda == result2.I_lambda
        assert result1.N_lambda == result2.N_lambda
    
    def test_compute_without_caching(self):
        """Test computation without caching."""
        operator = SpectralCountingOperator()
        lambda_val = 100.0
        
        result = operator.compute(lambda_val, use_cache=False)
        assert lambda_val not in operator._cache


class TestConvenienceFunction:
    """Tests for convenience function."""
    
    def test_convenience_function(self):
        """Test compute_spectral_count convenience function."""
        result = compute_spectral_count(1000.0)
        
        assert isinstance(result, SpectralCountingResult)
        assert result.converged
        assert result.lambda_val == 1000.0
        assert result.N_lambda > 0


class TestEdgeCases:
    """Tests for edge cases and numerical stability."""
    
    def test_small_lambda(self):
        """Test behavior for small λ."""
        operator = SpectralCountingOperator()
        result = operator.compute(1.0)
        
        assert result.converged
        assert result.N_lambda >= 0
    
    def test_large_lambda(self):
        """Test behavior for large λ."""
        operator = SpectralCountingOperator()
        result = operator.compute(50000.0)
        
        assert result.converged
        assert result.N_lambda > 0
        assert np.isfinite(result.N_lambda)
    
    def test_string_representation(self):
        """Test __repr__ method."""
        operator = SpectralCountingOperator()
        repr_str = repr(operator)
        
        assert "SpectralCountingOperator" in repr_str
        assert "precision" in repr_str


# Run tests if executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
