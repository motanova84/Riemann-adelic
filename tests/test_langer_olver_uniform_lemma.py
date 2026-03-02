#!/usr/bin/env python3
"""
Tests for Langer-Olver Uniform Lemma
=====================================

Tests the uniform lemma ζ↔y transformation and error bounds.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from operators.langer_olver_uniform_lemma import (
    LangerOlverUniformLemma,
    LangerOlverResult,
    ErrorCoefficients,
    F0_QCAL,
    C_COHERENCE
)


class TestPotentialFunction:
    """Test Q(y) potential function and its derivatives."""
    
    def test_Q_positive(self):
        """Test that Q(y) is positive for y > 0."""
        lemma = LangerOlverUniformLemma()
        
        y_values = np.linspace(0.1, 100, 50)
        for y in y_values:
            Q_val = lemma.Q(y)
            assert Q_val >= 0, f"Q({y}) = {Q_val} should be non-negative"
    
    def test_Q_grows_quadratically(self):
        """Test that Q(y) ~ y² for large y."""
        lemma = LangerOlverUniformLemma()
        
        # For large y: Q(y) ≈ α y² / (log y)²
        y = 1000.0
        Q_val = lemma.Q(y)
        expected = lemma.alpha * y**2 / (np.log(1 + y))**2
        
        assert abs(Q_val - expected) / expected < 1e-10
    
    def test_Q_derivative_continuity(self):
        """Test that Q'(y) is continuous."""
        lemma = LangerOlverUniformLemma()
        
        y = 10.0
        h = 1e-6
        
        # Numerical derivative
        Q_deriv_numerical = (lemma.Q(y + h) - lemma.Q(y - h)) / (2 * h)
        
        # Analytical derivative
        Q_deriv_analytical = lemma.Q_derivative(y, order=1)
        
        rel_error = abs(Q_deriv_numerical - Q_deriv_analytical) / abs(Q_deriv_analytical)
        assert rel_error < 1e-4, f"Q'({y}) mismatch: {rel_error}"
    
    def test_Q_second_derivative(self):
        """Test that Q''(y) is computed correctly."""
        lemma = LangerOlverUniformLemma()
        
        y = 10.0
        h = 1e-5
        
        # Numerical second derivative
        Q_second_numerical = (lemma.Q(y + h) - 2*lemma.Q(y) + lemma.Q(y - h)) / h**2
        
        # Computed second derivative
        Q_second_computed = lemma.Q_derivative(y, order=2)
        
        # Should be close (numerical differentiation is less accurate)
        rel_error = abs(Q_second_numerical - Q_second_computed) / abs(Q_second_computed)
        assert rel_error < 0.1, f"Q''({y}) relative error: {rel_error}"


class TestYPlusFinding:
    """Test finding y+ where Q(y+) = λ."""
    
    def test_find_y_plus_basic(self):
        """Test basic y+ finding."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        # Verify Q(y+) = λ
        Q_yplus = lemma.Q(y_plus)
        rel_error = abs(Q_yplus - lambda_val) / lambda_val
        
        assert rel_error < 1e-6, f"Q(y+) = {Q_yplus} vs λ = {lambda_val}"
    
    def test_find_y_plus_scaling(self):
        """Test that y+ scales approximately as √λ for large λ."""
        lemma = LangerOlverUniformLemma()
        
        lambda_values = np.array([100, 1000, 10000])
        y_plus_values = [lemma.find_y_plus(lam) for lam in lambda_values]
        
        # Check approximate scaling: y+ ~ √(λ / α) × log y
        for i in range(len(lambda_values) - 1):
            ratio_lambda = lambda_values[i+1] / lambda_values[i]
            ratio_y = y_plus_values[i+1] / y_plus_values[i]
            
            # Should be roughly √ratio_lambda (with log correction)
            expected_ratio = np.sqrt(ratio_lambda)
            
            # Allow factor of 2 deviation due to log terms
            assert 0.5 * expected_ratio < ratio_y < 2 * expected_ratio


class TestZetaTransformation:
    """Test ζ(y) coordinate transformation."""
    
    def test_zeta_at_y_plus(self):
        """Test that ζ(y+) = 0."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        zeta = lemma.compute_zeta_from_y(y_plus, lambda_val, y_plus)
        
        assert abs(zeta) < 1e-10, f"ζ(y+) = {zeta} should be 0"
    
    def test_zeta_negative(self):
        """Test that ζ(y) < 0 for y < y+."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        y_values = np.linspace(y_plus * 0.1, y_plus * 0.9, 10)
        
        for y in y_values:
            zeta = lemma.compute_zeta_from_y(y, lambda_val, y_plus)
            assert zeta < 0, f"ζ({y}) = {zeta} should be negative"
    
    def test_zeta_monotonic(self):
        """Test that ζ(y) is monotonically increasing in y."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        y_values = np.linspace(y_plus * 0.1, y_plus * 0.99, 20)
        zeta_values = [lemma.compute_zeta_from_y(y, lambda_val, y_plus) for y in y_values]
        
        # Check monotonicity
        for i in range(len(zeta_values) - 1):
            assert zeta_values[i+1] > zeta_values[i], "ζ should be monotonically increasing"


class TestInverseTransformation:
    """Test inverse transformation ζ → y."""
    
    def test_inverse_consistency(self):
        """Test round-trip consistency: y → ζ → y."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        # Test points
        y_original = y_plus * 0.5
        
        # Forward: y → ζ
        zeta = lemma.compute_zeta_from_y(y_original, lambda_val, y_plus)
        
        # Inverse: ζ → y
        y_reconstructed, _ = lemma.compute_y_from_zeta(zeta, lambda_val, y_plus)
        
        # Check consistency
        rel_error = abs(y_reconstructed - y_original) / y_original
        assert rel_error < 0.1, f"Round-trip error: {rel_error}"
    
    def test_leading_order_approximation(self):
        """Test leading order approximation u ≈ [Q'(y+)]^{-1/3} (-ζ)."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 1000.0
        y_plus = lemma.find_y_plus(lambda_val)
        Q_prime = lemma.Q_derivative(y_plus, 1)
        
        # Small ζ value
        zeta = -5.0
        
        # Leading order
        u_leading = Q_prime**(-1/3) * (-zeta)
        y_leading = y_plus - u_leading
        
        # With correction
        y_corrected, error_E = lemma.compute_y_from_zeta(zeta, lambda_val, y_plus)
        
        # Correction should be small for large λ
        u_corrected = y_plus - y_corrected
        correction = abs(u_corrected - u_leading) / u_leading
        
        assert correction < 0.5, f"Correction {correction} too large"


class TestErrorBounds:
    """Test error bounds |E(ζ, λ)| ≤ C|ζ|/√λ."""
    
    def test_error_coefficients(self):
        """Test computation of error coefficients A, B, α₁, α₂."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        coeffs = lemma.compute_error_coefficients(y_plus, lambda_val)
        
        # Check that coefficients are finite
        assert np.isfinite(coeffs.A)
        assert np.isfinite(coeffs.B)
        assert np.isfinite(coeffs.alpha1)
        assert np.isfinite(coeffs.alpha2)
        
        # Check scaling: A ~ 1/(√λ log λ)
        expected_A_scale = 1 / (np.sqrt(lambda_val) * np.log(lambda_val))
        assert abs(coeffs.A) < 10 * expected_A_scale
    
    def test_error_bound_scaling(self):
        """Test that |E(ζ, λ)| scales as O(|ζ|/√λ)."""
        lemma = LangerOlverUniformLemma()
        
        # Test for increasing λ
        lambda_values = np.array([100, 1000, 10000])
        zeta = -10.0  # Fixed ζ value
        
        errors = []
        for lambda_val in lambda_values:
            y_plus = lemma.find_y_plus(lambda_val)
            _, error_E = lemma.compute_y_from_zeta(zeta, lambda_val, y_plus)
            errors.append(abs(error_E))
        
        # Check that error decreases with λ
        for i in range(len(errors) - 1):
            assert errors[i+1] < errors[i], "Error should decrease with increasing λ"
        
        # Check scaling: error ~ 1/√λ
        sqrt_lambda_values = np.sqrt(lambda_values)
        scaled_errors = np.array(errors) * sqrt_lambda_values
        
        # Scaled errors should be roughly constant
        ratio = scaled_errors[-1] / scaled_errors[0]
        assert 0.5 < ratio < 2.0, f"Scaling ratio {ratio} deviates from expected"


class TestUniformLemma:
    """Test the full uniform lemma verification."""
    
    def test_intermediate_region(self):
        """Test that lemma holds in intermediate region 1 ≤ |ζ| ≤ λ^{1/3}."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 1000.0
        zeta_max = lambda_val**(1/3)  # ≈ 10
        
        # Sample in intermediate region
        zeta_values = -np.logspace(0, np.log10(zeta_max), 10)
        
        result = lemma.verify_uniform_lemma(lambda_val, zeta_values, verbose=False)
        
        # Check all points are in intermediate region
        assert all(result['in_intermediate_region'])
        
        # Check empirical C constant is reasonable
        assert result['C_constant'] < 100, f"C constant {result['C_constant']} too large"
    
    def test_multiple_lambda_values(self):
        """Test uniform lemma for multiple λ values."""
        lemma = LangerOlverUniformLemma()
        
        lambda_values = np.array([10, 100, 1000])
        
        C_constants = []
        for lambda_val in lambda_values:
            zeta_max = lambda_val**(1/3)
            zeta_values = -np.logspace(0, np.log10(zeta_max), 10)
            
            result = lemma.verify_uniform_lemma(lambda_val, zeta_values, verbose=False)
            C_constants.append(result['C_constant'])
        
        # C should be approximately independent of λ (uniform bound)
        max_C = max(C_constants)
        min_C = min(C_constants)
        
        # Allow factor of 10 variation
        assert max_C / min_C < 10, "C constant varies too much with λ"


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_certificate_structure(self):
        """Test that certificate has correct structure."""
        lemma = LangerOlverUniformLemma()
        
        lambda_values = np.array([10, 100, 1000])
        certificate = lemma.generate_certificate(lambda_values, num_zeta_samples=10)
        
        # Check required fields
        assert 'protocol' in certificate
        assert 'version' in certificate
        assert 'signature' in certificate
        assert 'qcal_constants' in certificate
        assert 'parameters' in certificate
        assert 'test_results' in certificate
        assert 'summary' in certificate
        assert 'coherence' in certificate
        
        # Check QCAL constants
        assert certificate['qcal_constants']['f0_hz'] == F0_QCAL
        assert certificate['qcal_constants']['C'] == C_COHERENCE
    
    def test_certificate_coherence(self):
        """Test coherence metric Ψ."""
        lemma = LangerOlverUniformLemma()
        
        lambda_values = np.array([100, 1000])
        certificate = lemma.generate_certificate(lambda_values, num_zeta_samples=10)
        
        # Check coherence
        psi = certificate['coherence']['Psi']
        assert 0 <= psi <= 1, f"Ψ = {psi} should be in [0, 1]"
        
        # If tests pass, Ψ should be high
        if certificate['summary']['all_tests_passed']:
            assert psi >= 0.888, "Ψ should exceed threshold for passing tests"


class TestMathematicalProperties:
    """Test mathematical properties of the uniform lemma."""
    
    def test_paso_1_definition(self):
        """Test PASO 1: Definition of ζ(y)."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 100.0
        y_plus = lemma.find_y_plus(lambda_val)
        y = y_plus * 0.8
        
        # Compute u = y+ - y
        u = y_plus - y
        
        # Compute I(u)
        I_u = lemma.compute_I_u(u, y_plus, lambda_val)
        
        # Compute ζ from definition: ζ = -[(3/2) I(u)]^{2/3}
        zeta_definition = -((3/2) * I_u)**(2/3)
        
        # Compute ζ from method
        zeta_method = lemma.compute_zeta_from_y(y, lambda_val, y_plus)
        
        # Should match
        rel_error = abs(zeta_definition - zeta_method) / abs(zeta_definition)
        assert rel_error < 1e-6, f"PASO 1 definition mismatch: {rel_error}"
    
    def test_paso_6_series_inversion(self):
        """Test PASO 6: Series inversion u = f(ζ)."""
        lemma = LangerOlverUniformLemma()
        
        lambda_val = 1000.0
        y_plus = lemma.find_y_plus(lambda_val)
        
        # Test for small ζ where series is valid
        zeta = -2.0
        
        # Compute y from ζ
        y, error_E = lemma.compute_y_from_zeta(zeta, lambda_val, y_plus)
        u = y_plus - y
        
        # Verify ζ from u
        zeta_check = lemma.compute_zeta_from_y(y, lambda_val, y_plus)
        
        rel_error = abs(zeta - zeta_check) / abs(zeta)
        assert rel_error < 0.1, f"Series inversion error: {rel_error}"


@pytest.mark.slow
class TestHighPrecisionVerification:
    """High-precision tests (marked as slow)."""
    
    def test_large_lambda_convergence(self):
        """Test convergence for very large λ."""
        lemma = LangerOlverUniformLemma()
        
        lambda_values = np.logspace(2, 5, 10)  # 100 to 100000
        
        C_constants = []
        for lambda_val in lambda_values:
            zeta_max = lambda_val**(1/3)
            zeta_values = -np.logspace(0, np.log10(zeta_max), 20)
            
            result = lemma.verify_uniform_lemma(lambda_val, zeta_values, verbose=False)
            C_constants.append(result['C_constant'])
        
        # For large λ, C should stabilize
        late_C = np.mean(C_constants[-3:])
        assert late_C < 50, f"C constant {late_C} should stabilize"


def test_demo_runs():
    """Test that demo runs without errors."""
    from operators.langer_olver_uniform_lemma import demo_uniform_lemma
    
    certificate = demo_uniform_lemma()
    
    # Verify certificate was generated
    assert certificate is not None
    assert 'summary' in certificate
    assert 'coherence' in certificate


if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, "-v", "-s"])
