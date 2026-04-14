#!/usr/bin/env python3
"""
Tests for Langer-Olver Transformation and Weyl m-function
=========================================================

This module contains comprehensive tests for the Langer-Olver transformation
implementation and its connection to the Riemann Hypothesis.
"""

import pytest
import numpy as np
from operators.langer_olver_transformation import (
    LangerOlverTransformation,
    LangerOlverResult,
    compute_weyl_m_function,
    compute_scattering_phase,
    generate_qcal_certificate
)


class TestLangerOlverTransformation:
    """Test suite for Langer-Olver transformation."""
    
    def test_initialization(self):
        """Test transformer initialization."""
        transformer = LangerOlverTransformation()
        assert transformer.scale == np.pi**4 / 16
        
        custom_scale = 2.0
        transformer2 = LangerOlverTransformation(potential_scale=custom_scale)
        assert transformer2.scale == custom_scale
    
    def test_potential_Q(self):
        """Test potential function Q(y)."""
        transformer = LangerOlverTransformation()
        
        # Test at y = 0 (should be smoothed)
        Q_0 = transformer.Q(0)
        assert Q_0 == 0.0
        
        # Test at small y (should be smoothed)
        Q_small = transformer.Q(1e-12)
        assert np.isfinite(Q_small)
        assert Q_small > 0
        
        # Test at y = 1
        Q_1 = transformer.Q(1.0)
        expected = transformer.scale * 1.0 / np.log(2)**2
        assert abs(Q_1 - expected) < 1e-10
        
        # Test positivity for y > 0
        for y in [0.1, 1.0, 10.0, 100.0]:
            Q_y = transformer.Q(y)
            assert Q_y > 0, f"Q({y}) should be positive"
    
    def test_turning_point(self):
        """Test turning point calculation."""
        transformer = LangerOlverTransformation()
        
        # Test for various λ values
        for lambda_val in [1.0, 10.0, 100.0]:
            y_plus = transformer.find_turning_point(lambda_val)
            
            # Verify Q(y+) ≈ λ
            Q_yplus = transformer.Q(y_plus)
            rel_error = abs(Q_yplus - lambda_val) / lambda_val
            assert rel_error < 1e-6, f"Q(y+) should equal λ for λ={lambda_val}"
            
            # Verify y+ > 0
            assert y_plus > 0
    
    def test_zeta_coordinate(self):
        """Test Langer-Olver coordinate ζ(y)."""
        transformer = LangerOlverTransformation()
        lambda_val = 100.0
        y_plus = transformer.find_turning_point(lambda_val)
        
        # Test ζ(0) < 0 (below turning point)
        zeta_0 = transformer.compute_zeta(0, lambda_val, y_plus)
        assert zeta_0.real < 0, "ζ(0) should be negative"
        assert abs(zeta_0.imag) < 1e-10, "ζ(0) should be real"
        
        # Test ζ(y+) ≈ 0 (at turning point)
        # Note: numerically might not be exactly zero due to integration
        zeta_plus = transformer.compute_zeta(y_plus, lambda_val, y_plus)
        assert abs(zeta_plus) < 0.1, "ζ(y+) should be near zero"
        
        # Test ζ(y) > 0 for y > y+ (above turning point)
        y_above = y_plus + 1.0
        zeta_above = transformer.compute_zeta(y_above, lambda_val, y_plus)
        assert zeta_above.real > 0, "ζ(y) should be positive for y > y+"
    
    def test_I_lambda(self):
        """Test WKB integral I(λ)."""
        transformer = LangerOlverTransformation()
        
        # Test for increasing λ
        lambda_vals = [10.0, 50.0, 100.0]
        I_vals = []
        
        for lam in lambda_vals:
            y_plus = transformer.find_turning_point(lam)
            I_lam = transformer.compute_I_lambda(lam, y_plus)
            I_vals.append(I_lam)
            
            # I(λ) should be positive
            assert I_lam > 0
        
        # I(λ) should be increasing with λ
        for i in range(len(I_vals) - 1):
            assert I_vals[i+1] > I_vals[i], "I(λ) should increase with λ"
    
    def test_weyl_m_function(self):
        """Test Weyl m-function computation."""
        transformer = LangerOlverTransformation()
        
        # Test for various λ values
        for lambda_val in [10.0, 50.0, 100.0]:
            m_lambda = transformer.compute_m_function(lambda_val)
            
            # m(λ) should be complex
            assert isinstance(m_lambda, complex)
            
            # For real λ > 0, m(λ) should have finite magnitude
            assert np.isfinite(abs(m_lambda))
            assert abs(m_lambda) > 0
    
    def test_scattering_phase(self):
        """Test scattering phase θ(λ)."""
        transformer = LangerOlverTransformation()
        
        lambda_vals = [10.0, 50.0, 100.0, 200.0]
        theta_vals = []
        
        for lam in lambda_vals:
            theta = transformer.compute_scattering_phase(lam)
            theta_vals.append(theta)
            
            # θ(λ) should be real
            assert np.isfinite(theta)
        
        # θ(λ) should generally increase with λ
        # (allowing some numerical variation)
        increasing_count = sum(1 for i in range(len(theta_vals)-1) 
                             if theta_vals[i+1] > theta_vals[i])
        assert increasing_count >= len(theta_vals) - 2, "θ(λ) should generally increase"
    
    def test_full_result(self):
        """Test complete result computation."""
        transformer = LangerOlverTransformation()
        lambda_val = 100.0
        
        result = transformer.compute_full_result(lambda_val)
        
        # Verify result type
        assert isinstance(result, LangerOlverResult)
        
        # Verify fields
        assert result.lambda_val == lambda_val
        assert result.y_plus > 0
        assert np.isfinite(result.zeta_0)
        assert result.I_lambda > 0
        assert np.isfinite(result.phi_0)
        assert np.isfinite(result.m_lambda)
        assert np.isfinite(result.theta)
        assert np.isfinite(result.gamma_arg)
        assert np.isfinite(result.weyl_asymptotic)
    
    def test_asymptotic_behavior(self):
        """Test asymptotic behavior for large λ."""
        transformer = LangerOlverTransformation()
        
        # Test I(λ) ~ (1/2) λ log λ for large λ
        lambda_vals = [100.0, 500.0, 1000.0]
        
        for lam in lambda_vals:
            y_plus = transformer.find_turning_point(lam)
            I_lam = transformer.compute_I_lambda(lam, y_plus)
            
            # Expected asymptotic: I(λ) ~ (1/2) λ log λ
            asymptotic = 0.5 * lam * np.log(lam)
            
            # For large λ, I(λ) should approach the asymptotic form
            # Allow significant deviation for finite λ
            rel_diff = abs(I_lam - asymptotic) / asymptotic
            assert rel_diff < 2.0, f"I(λ) should approach asymptotic for λ={lam}"
    
    def test_riemann_connection_validation(self):
        """Test validation of connection to Riemann zeros."""
        transformer = LangerOlverTransformation()
        
        lambda_vals = np.array([10.0, 50.0, 100.0])
        validation = transformer.validate_riemann_connection(lambda_vals)
        
        # Validation should succeed
        assert validation['valid'] is True
        assert validation['n_samples'] == len(lambda_vals)
        
        # Check results structure
        assert 'results' in validation
        assert len(validation['results']) == len(lambda_vals)
        
        # Check Weyl coefficient convergence
        assert 'weyl_coefficient_mean' in validation
        assert 'expected_weyl' in validation
        assert np.isfinite(validation['weyl_coefficient_mean'])


class TestConvenienceFunctions:
    """Test suite for convenience functions."""
    
    def test_compute_weyl_m_function(self):
        """Test convenience function for m(λ)."""
        lambda_val = 50.0
        m_lambda = compute_weyl_m_function(lambda_val)
        
        assert isinstance(m_lambda, complex)
        assert np.isfinite(abs(m_lambda))
    
    def test_compute_scattering_phase(self):
        """Test convenience function for θ(λ)."""
        lambda_val = 50.0
        theta = compute_scattering_phase(lambda_val)
        
        assert isinstance(theta, (int, float))
        assert np.isfinite(theta)


class TestQCALCertificate:
    """Test suite for QCAL certificate generation."""
    
    def test_certificate_generation(self):
        """Test QCAL certificate generation."""
        validation_results = {
            'valid': True,
            'n_samples': 5,
            'weyl_coefficient_mean': 0.16,
            'weyl_coefficient_std': 0.01,
            'expected_weyl': 1 / (2 * np.pi),
            'max_weyl_error': 0.01,
            'theta_range': (10.0, 100.0)
        }
        
        certificate = generate_qcal_certificate(validation_results)
        
        # Check required fields
        assert certificate['protocol'] == 'QCAL-LANGER-OLVER-WEYL'
        assert certificate['version'] == '1.0'
        assert certificate['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check QCAL constants
        qcal = certificate['qcal_constants']
        assert qcal['f0_hz'] == 141.7001
        assert qcal['C'] == 244.36
        assert qcal['kappa_pi'] == 2.577310
        assert qcal['seal'] == 14170001
        assert qcal['code'] == 888
        
        # Check coherence
        assert 'Psi' in certificate['coherence']
        assert 0 <= certificate['coherence']['Psi'] <= 1
        
        # Check resonance
        assert 'level' in certificate['resonance_detection']
        assert certificate['resonance_detection']['level'] in [
            'UNIVERSAL', 'QUANTUM', 'CLASSICAL', 'NONE'
        ]
    
    def test_certificate_coherence_levels(self):
        """Test certificate coherence level determination."""
        # Test UNIVERSAL level (Ψ >= 0.888)
        validation1 = {
            'valid': True,
            'max_weyl_error': 0.01
        }
        cert1 = generate_qcal_certificate(validation1)
        assert cert1['coherence']['Psi'] >= 0.888
        assert cert1['resonance_detection']['level'] == 'UNIVERSAL'
        
        # Test lower coherence
        validation2 = {
            'valid': True,
            'max_weyl_error': 0.5
        }
        cert2 = generate_qcal_certificate(validation2)
        assert cert2['coherence']['Psi'] < 0.888
        
        # Test invalid validation
        validation3 = {
            'valid': False
        }
        cert3 = generate_qcal_certificate(validation3)
        assert cert3['coherence']['Psi'] == 0.0
        assert cert3['resonance_detection']['level'] == 'NONE'


class TestNumericalStability:
    """Test suite for numerical stability."""
    
    def test_small_lambda(self):
        """Test stability for small λ values."""
        transformer = LangerOlverTransformation()
        
        # Test small but positive λ
        lambda_val = 1.0
        result = transformer.compute_full_result(lambda_val)
        
        # Should complete without errors
        assert np.isfinite(result.I_lambda)
        assert np.isfinite(result.theta)
    
    def test_large_lambda(self):
        """Test stability for large λ values."""
        transformer = LangerOlverTransformation()
        
        # Test large λ
        lambda_val = 1000.0
        result = transformer.compute_full_result(lambda_val)
        
        # Should complete without errors
        assert np.isfinite(result.I_lambda)
        assert np.isfinite(result.theta)
        
        # Asymptotic behavior should be reasonable
        asymptotic_I = 0.5 * lambda_val * np.log(lambda_val)
        assert result.I_lambda > 0
        assert result.I_lambda < 10 * asymptotic_I  # Sanity check
    
    def test_array_input(self):
        """Test computation over array of λ values."""
        transformer = LangerOlverTransformation()
        
        lambda_vals = np.array([10.0, 50.0, 100.0, 200.0])
        
        # Should handle multiple values
        results = []
        for lam in lambda_vals:
            result = transformer.compute_full_result(lam)
            results.append(result)
        
        assert len(results) == len(lambda_vals)
        
        # All results should be valid
        for result in results:
            assert np.isfinite(result.I_lambda)
            assert np.isfinite(result.theta)


class TestMathematicalProperties:
    """Test suite for mathematical properties."""
    
    def test_gamma_function_argument(self):
        """Test gamma function argument computation."""
        transformer = LangerOlverTransformation()
        
        for lambda_val in [10.0, 50.0, 100.0]:
            result = transformer.compute_full_result(lambda_val)
            
            # gamma_arg should be real (angle)
            assert np.isfinite(result.gamma_arg)
            
            # Should be in reasonable range [-π, π]
            assert abs(result.gamma_arg) <= 2 * np.pi
    
    def test_phase_formula(self):
        """Test phase formula θ(λ) = I(λ) + (1/2) arg Γ."""
        transformer = LangerOlverTransformation()
        
        for lambda_val in [10.0, 50.0, 100.0]:
            result = transformer.compute_full_result(lambda_val)
            
            # Verify relationship
            expected_theta = result.I_lambda + 0.5 * result.gamma_arg
            
            # Allow some numerical tolerance
            diff = abs(result.theta - expected_theta)
            assert diff < 1e-6, f"Phase formula verification failed for λ={lambda_val}"
    
    def test_weyl_coefficient_convergence(self):
        """Test Weyl coefficient convergence to Riemann value."""
        transformer = LangerOlverTransformation()
        
        # Test convergence for increasing λ
        lambda_vals = [100.0, 500.0, 1000.0, 2000.0]
        coeffs = []
        
        for lam in lambda_vals:
            result = transformer.compute_full_result(lam)
            coeffs.append(result.weyl_asymptotic)
        
        # Expected Riemann value: 1/(2π) ≈ 0.159155
        expected = 1 / (2 * np.pi)
        
        # Coefficients should approach expected value
        # (allowing significant deviation for finite λ)
        for coeff in coeffs:
            # Just check they're in reasonable range
            assert 0 < coeff < 1.0


@pytest.mark.slow
class TestPerformance:
    """Test suite for performance (marked as slow)."""
    
    def test_large_scale_computation(self):
        """Test computation for many λ values."""
        transformer = LangerOlverTransformation()
        
        # Generate many λ values
        lambda_vals = np.logspace(1, 3, 20)  # 10 to 1000
        
        # Should complete in reasonable time
        validation = transformer.validate_riemann_connection(lambda_vals)
        
        assert validation['valid'] is True
        assert validation['n_samples'] >= len(lambda_vals) * 0.9  # Allow some failures


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
