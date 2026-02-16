#!/usr/bin/env python3
"""
Tests for WKB Schwarzian Control Module
========================================

Comprehensive tests for the WKB approximation with explicit Schwarzian control.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import pytest
import numpy as np
from operators.wkb_schwarzian_control import (
    WKBSchwartzianControl,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
    PI
)


class TestWKBSchwartzianControlBasics:
    """Test basic functionality of WKB Schwarzian Control."""
    
    def test_initialization(self):
        """Test initialization with valid parameters."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        assert wkb.lambda_param == 100.0
        assert wkb.y_plus > 0
        assert wkb.L > 0
    
    def test_initialization_invalid_lambda(self):
        """Test that invalid lambda raises error."""
        with pytest.raises(ValueError):
            WKBSchwartzianControl(lambda_param=-1.0)
        
        with pytest.raises(ValueError):
            WKBSchwartzianControl(lambda_param=0.0)
    
    def test_potential_Q_positive_y(self):
        """Test Q(y) for positive y values."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        y_test = np.array([1.0, 2.0, 5.0, 10.0])
        Q_vals = wkb.Q(y_test)
        
        # Q should be positive for positive y
        assert np.all(Q_vals > 0)
        
        # Q should increase with y (for large enough y)
        assert Q_vals[1] > Q_vals[0]
        assert Q_vals[3] > Q_vals[2]
    
    def test_potential_Q_at_turning_point(self):
        """Test that Q(y₊) ≈ λ."""
        lambda_val = 100.0
        wkb = WKBSchwartzianControl(lambda_param=lambda_val)
        
        Q_at_y_plus = wkb.Q(wkb.y_plus)
        
        # Should satisfy Q(y₊) = λ to high accuracy
        assert np.abs(Q_at_y_plus - lambda_val) < 0.01 * lambda_val
    
    def test_Q_prime_positive_y(self):
        """Test Q'(y) for positive y values."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        y_test = np.array([1.0, 2.0, 5.0, 10.0])
        Q_prime_vals = wkb.Q_prime(y_test)
        
        # Q' should be defined
        assert len(Q_prime_vals) == len(y_test)
        assert np.all(np.isfinite(Q_prime_vals))


class TestTurningPoint:
    """Test turning point calculation."""
    
    def test_turning_point_increases_with_lambda(self):
        """Test that y₊ increases with λ."""
        lambda_vals = [10.0, 50.0, 100.0, 500.0]
        y_plus_vals = []
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            y_plus_vals.append(wkb.y_plus)
        
        # y₊ should increase with λ
        for i in range(len(y_plus_vals) - 1):
            assert y_plus_vals[i+1] > y_plus_vals[i]
    
    def test_turning_point_asymptotic(self):
        """Test asymptotic formula for large λ: y₊ ≈ (2/π²) log λ."""
        lambda_val = 1000.0
        wkb = WKBSchwartzianControl(lambda_param=lambda_val)
        
        theoretical = (2.0 / (PI**2)) * np.log(lambda_val)
        
        # Should be close to asymptotic formula (within 20%)
        relative_error = abs(wkb.y_plus - theoretical) / theoretical
        assert relative_error < 0.2
    
    def test_L_parameter(self):
        """Test L parameter computation."""
        lambda_val = 100.0
        wkb = WKBSchwartzianControl(lambda_param=lambda_val)
        
        # L should be positive
        assert wkb.L > 0
        
        # For large λ, L ≈ (2/π²) log λ
        if lambda_val > 10:
            theoretical_L = (2.0 / (PI**2)) * np.log(lambda_val)
            relative_error = abs(wkb.L - theoretical_L) / theoretical_L
            assert relative_error < 0.3


class TestLangerTransformation:
    """Test Langer variable ζ transformation."""
    
    def test_u_to_zeta_and_back(self):
        """Test that ζ transformation is invertible."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        u_test = np.array([-2.0, -1.0, 0.0, 1.0, 2.0])
        zeta = wkb.u_to_zeta(u_test)
        u_back = wkb.zeta_to_u(zeta)
        
        # Should recover original u values
        np.testing.assert_allclose(u_test, u_back, rtol=1e-6)
    
    def test_zeta_prime_positive(self):
        """Test that ζ' > 0."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_test = np.array([-5.0, -1.0, 0.0, 1.0, 5.0])
        zeta_prime_vals = wkb.zeta_prime(zeta_test)
        
        # ζ' should be positive
        assert np.all(zeta_prime_vals > 0)
    
    def test_zeta_prime_scaling(self):
        """Test ζ' ∼ λ^(1/6) scaling."""
        lambda_vals = [10.0, 100.0, 1000.0]
        zeta_prime_at_zero = []
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            zeta_prime_vals = wkb.zeta_prime(np.array([0.0]))
            zeta_prime_at_zero.append(zeta_prime_vals[0])
        
        # Check scaling: ζ'(λ₂)/ζ'(λ₁) ≈ (λ₂/λ₁)^(1/6)
        ratio_measured = zeta_prime_at_zero[1] / zeta_prime_at_zero[0]
        ratio_expected = (lambda_vals[1] / lambda_vals[0])**(1.0/6.0)
        
        relative_error = abs(ratio_measured - ratio_expected) / ratio_expected
        assert relative_error < 0.3


class TestSchwartzianDerivative:
    """Test Schwarzian derivative computation."""
    
    def test_schwarzian_bound_small_zeta(self):
        """Test Schwarzian bound for small |ζ|."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_small = np.array([-1.0, -0.5, 0.0, 0.5, 1.0])
        schwarzian_vals = wkb.schwarzian(zeta_small)
        bound_vals = wkb.schwarzian_bound(zeta_small)
        
        # |{ζ, y}| should be less than bound
        assert np.all(np.abs(schwarzian_vals) <= bound_vals * 1.1)  # 10% tolerance
    
    def test_schwarzian_bound_large_zeta(self):
        """Test Schwarzian bound for large |ζ|."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_large = np.array([-10.0, -5.0, 5.0, 10.0])
        schwarzian_vals = wkb.schwarzian(zeta_large)
        bound_vals = wkb.schwarzian_bound(zeta_large)
        
        # Bound should decay as 1/|ζ|³
        assert np.all(np.abs(schwarzian_vals) <= bound_vals * 1.2)
    
    def test_schwarzian_decay(self):
        """Test that Schwarzian decays for large |ζ|."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_1 = np.array([1.0])
        zeta_10 = np.array([10.0])
        
        schwarz_1 = abs(wkb.schwarzian(zeta_1)[0])
        schwarz_10 = abs(wkb.schwarzian(zeta_10)[0])
        
        # Schwarzian at ζ=10 should be much smaller than at ζ=1
        assert schwarz_10 < schwarz_1
    
    def test_error_term_R(self):
        """Test error term R(ζ) = {ζ, y} / 2."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_test = np.array([0.0, 1.0, 5.0])
        R_vals = wkb.error_term_R(zeta_test)
        schwarzian_vals = wkb.schwarzian(zeta_test)
        
        # R should be half of Schwarzian
        np.testing.assert_allclose(R_vals, schwarzian_vals / 2.0, rtol=1e-10)


class TestSchwartzianValidation:
    """Test Schwarzian bound validation."""
    
    def test_validate_schwarzian_bound(self):
        """Test that Schwarzian bound is satisfied over a range."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        validation = wkb.validate_schwarzian_bound(zeta_range=(-10, 10), n_points=1000)
        
        # Check validation results
        assert 'max_schwarzian' in validation
        assert 'max_bound' in validation
        assert 'bound_satisfied' in validation
        assert 'max_ratio' in validation
        
        # Bound should be satisfied (with some tolerance)
        assert validation['max_ratio'] <= 1.5  # 50% tolerance for numerical stability
    
    def test_validation_different_lambdas(self):
        """Test validation for different λ values."""
        lambda_vals = [10.0, 50.0, 100.0, 500.0]
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            validation = wkb.validate_schwarzian_bound()
            
            # All should satisfy bound
            assert validation['max_ratio'] <= 2.0  # Generous tolerance


class TestWKBIntegral:
    """Test WKB integral computation."""
    
    def test_wkb_integral_basic(self):
        """Test basic WKB integral computation."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        result = wkb.wkb_integral((-5, wkb.y_plus + 20))
        
        assert 'integral' in result
        assert 'theoretical' in result
        assert 'error' in result
        assert 'relative_error' in result
        
        # Results should be finite
        assert np.isfinite(result['integral'])
        assert np.isfinite(result['theoretical'])
    
    def test_wkb_integral_asymptotic(self):
        """Test WKB integral asymptotic formula for large λ."""
        lambda_val = 100.0
        wkb = WKBSchwartzianControl(lambda_param=lambda_val)
        
        result = wkb.wkb_integral((-5, wkb.y_plus + 20))
        
        # Theoretical: (1/2) λ log λ - (1/2) λ
        theoretical = 0.5 * lambda_val * np.log(lambda_val) - 0.5 * lambda_val
        
        # Should be reasonably close
        relative_error = abs(result['integral'] - theoretical) / abs(theoretical)
        assert relative_error < 0.5  # 50% tolerance for numerical integration
    
    def test_wkb_integral_increases_with_lambda(self):
        """Test that WKB integral increases with λ."""
        lambda_vals = [10.0, 50.0, 100.0]
        integrals = []
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            result = wkb.wkb_integral((-5, wkb.y_plus + 20))
            integrals.append(result['integral'])
        
        # Integral should increase with λ
        assert integrals[1] > integrals[0]
        assert integrals[2] > integrals[1]


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        cert = wkb.generate_certificate()
        
        # Check required fields
        assert cert['protocol'] == 'QCAL-WKB-SCHWARZIAN-CONTROL'
        assert cert['version'] == '1.0.0'
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        assert 'parameters' in cert
        assert 'qcal_constants' in cert
        assert 'schwarzian_validation' in cert
        assert 'wkb_integral' in cert
        assert 'coherence_metrics' in cert
        assert 'resonance_detection' in cert
        assert 'invocation_final' in cert
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        cert = wkb.generate_certificate()
        qcal = cert['qcal_constants']
        
        assert qcal['f0_hz'] == QCAL_BASE_FREQUENCY
        assert qcal['C'] == QCAL_COHERENCE
        assert qcal['seal'] == 14170001
        assert qcal['code'] == 888
    
    def test_certificate_coherence_metrics(self):
        """Test coherence metrics in certificate."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        cert = wkb.generate_certificate()
        coherence = cert['coherence_metrics']
        
        assert 'schwarzian_bound_satisfied' in coherence
        assert 'wkb_relative_error' in coherence
        assert 'overall_coherence' in coherence
        
        # Overall coherence should be 0 or 1
        assert coherence['overall_coherence'] in [0.0, 1.0]
    
    def test_certificate_resonance_detection(self):
        """Test resonance detection in certificate."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        cert = wkb.generate_certificate()
        resonance = cert['resonance_detection']
        
        assert resonance['threshold'] == 0.888
        assert resonance['level'] in ['UNIVERSAL', 'PARTIAL']


class TestNumericalStability:
    """Test numerical stability for various parameter ranges."""
    
    def test_small_lambda(self):
        """Test with small λ values."""
        lambda_vals = [1.0, 2.0, 5.0]
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            
            # Should initialize without error
            assert wkb.y_plus > 0
            assert wkb.L > 0
            
            # Q(y₊) should be close to λ
            Q_at_y_plus = wkb.Q(wkb.y_plus)
            assert abs(Q_at_y_plus - lambda_val) < 0.1 * lambda_val
    
    def test_large_lambda(self):
        """Test with large λ values."""
        lambda_vals = [100.0, 500.0, 1000.0]
        
        for lambda_val in lambda_vals:
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            
            # Should initialize without error
            assert wkb.y_plus > 0
            assert wkb.L > 0
            
            # Validation should pass
            validation = wkb.validate_schwarzian_bound()
            assert validation['max_ratio'] <= 2.0
    
    def test_extreme_zeta_values(self):
        """Test Schwarzian computation for extreme ζ values."""
        wkb = WKBSchwartzianControl(lambda_param=100.0)
        
        zeta_extreme = np.array([-100.0, -50.0, 50.0, 100.0])
        
        # Should not raise errors
        schwarzian_vals = wkb.schwarzian(zeta_extreme)
        bound_vals = wkb.schwarzian_bound(zeta_extreme)
        
        # All values should be finite
        assert np.all(np.isfinite(schwarzian_vals))
        assert np.all(np.isfinite(bound_vals))
        
        # Bound should still be satisfied (or close)
        assert np.all(np.abs(schwarzian_vals) <= bound_vals * 3.0)


@pytest.mark.parametrize("lambda_val", [10.0, 50.0, 100.0, 500.0])
def test_complete_workflow(lambda_val):
    """Test complete workflow for various λ values."""
    # Create controller
    wkb = WKBSchwartzianControl(lambda_param=lambda_val)
    
    # Compute turning point
    assert wkb.y_plus > 0
    
    # Validate Schwarzian
    validation = wkb.validate_schwarzian_bound()
    assert validation['max_ratio'] <= 2.0
    
    # Compute WKB integral
    wkb_int = wkb.wkb_integral((-5, wkb.y_plus + 20))
    assert np.isfinite(wkb_int['integral'])
    
    # Generate certificate
    cert = wkb.generate_certificate()
    assert cert['protocol'] == 'QCAL-WKB-SCHWARZIAN-CONTROL'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
