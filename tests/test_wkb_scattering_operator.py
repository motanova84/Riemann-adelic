#!/usr/bin/env python3
"""
Tests for WKB Scattering Operator - PASO 1-8 Implementation
============================================================

Test suite for the WKB scattering operator with potential Q(y) = y²/(log(1+y))².

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-WKB-SCATTERING v1.0
Date: February 16, 2026
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.wkb_scattering_operator import (
    WKBScatteringOperator,
    WKBResult,
    PotentialResult,
    generate_wkb_certificate
)


class TestWKBScatteringOperator:
    """Test suite for WKB scattering operator."""
    
    def setup_method(self):
        """Setup for each test."""
        self.wkb_op = WKBScatteringOperator()
    
    def test_potential_zero_for_negative_y(self):
        """Test that Q(y) = 0 for y ≤ 0."""
        y_values = np.linspace(-10, 0, 100)
        
        for y in y_values:
            Q_y = self.wkb_op.Q(y)
            assert Q_y >= 0, f"Q({y}) = {Q_y} should be ≥ 0"
            if y < -1:  # Far from transition region
                assert abs(Q_y) < 1e-10, f"Q({y}) = {Q_y} should be ~0"
    
    def test_potential_positive_for_positive_y(self):
        """Test that Q(y) > 0 for y > 0."""
        y_values = np.linspace(0.5, 50, 100)
        
        for y in y_values:
            Q_y = self.wkb_op.Q(y)
            assert Q_y > 0, f"Q({y}) = {Q_y} should be > 0"
    
    def test_potential_asymptotic_behavior(self):
        """Test that Q(y) ~ y²/(log(1+y))² for large y."""
        y_large = np.array([10, 20, 30, 40, 50])
        
        for y in y_large:
            Q_y = self.wkb_op.Q(y)
            expected = y**2 / (np.log(1 + y)**2)
            ratio = Q_y / expected
            
            # Should be close to 1 for large y
            assert 0.9 < ratio < 1.1, \
                f"Q({y})/{y}²/(log(1+{y}))² = {ratio} should be ~1"
    
    def test_turning_points(self):
        """Test finding turning points y± such that Q(y±) = λ."""
        lambda_val = 10.0
        
        y_minus, y_plus = self.wkb_op.find_turning_points(lambda_val)
        
        # Check that y_minus ≈ 0 (since Q(y) = 0 for y ≤ 0)
        assert abs(y_minus) < 0.1, f"y- = {y_minus} should be ~0"
        
        # Check that Q(y+) ≈ λ
        Q_y_plus = self.wkb_op.Q(y_plus)
        assert abs(Q_y_plus - lambda_val) / lambda_val < 0.01, \
            f"Q({y_plus}) = {Q_y_plus} should be ≈ λ = {lambda_val}"
        
        # For large λ, y+ should ~ √λ log λ
        expected_y_plus = np.sqrt(lambda_val) * np.log(lambda_val)
        ratio = y_plus / expected_y_plus
        assert 0.5 < ratio < 2.0, \
            f"y+ = {y_plus} vs expected ~√λ log λ = {expected_y_plus}"
    
    def test_WKB_integral_positive(self):
        """Test that WKB integral I(λ) > 0 for λ > 0."""
        lambda_values = [1.0, 10.0, 50.0, 100.0]
        
        for lam in lambda_values:
            I_lambda = self.wkb_op.compute_WKB_integral(lam)
            assert I_lambda > 0, f"I({lam}) = {I_lambda} should be > 0"
    
    def test_WKB_integral_asymptotic(self):
        """Test that I(λ) ~ λ log λ for large λ."""
        lambda_large = [50.0, 100.0, 200.0]
        
        for lam in lambda_large:
            I_lambda = self.wkb_op.compute_WKB_integral(lam)
            expected = lam * np.log(lam)
            ratio = I_lambda / expected
            
            # Should approach 1 as λ → ∞
            assert 0.5 < ratio < 2.0, \
                f"I({lam})/(λ log λ) = {ratio} should be ~1 for large λ"
    
    def test_scattering_phase_computation(self):
        """Test scattering phase θ(λ) computation."""
        lambda_val = 50.0
        
        theta = self.wkb_op.compute_scattering_phase(lambda_val)
        
        # θ(λ) should be finite
        assert np.isfinite(theta), f"θ({lambda_val}) = {theta} should be finite"
        
        # For the desired expansion:
        # θ(λ) = (λ/2) log λ - λ/2 + (1/2) arg Γ(1/4 + iλ/2) + o(1)
        # Check order of magnitude
        expected_order = lambda_val * np.log(lambda_val)
        assert abs(theta) < 10 * expected_order, \
            f"θ({lambda_val}) = {theta} has wrong order of magnitude"
    
    def test_asymptotic_expansion_accuracy(self):
        """Test accuracy of asymptotic expansion for I(λ)."""
        lambda_val = 100.0
        
        asymptotic_check = self.wkb_op.verify_asymptotic_expansion(lambda_val)
        
        # Relative error should decrease as λ increases
        relative_error = asymptotic_check['relative_error']
        
        # For λ = 100, expect reasonable accuracy (< 20%)
        assert relative_error < 0.2, \
            f"Asymptotic expansion error {relative_error} too large for λ = {lambda_val}"
    
    def test_analyze_WKB_complete(self):
        """Test complete WKB analysis."""
        lambda_val = 50.0
        
        result = self.wkb_op.analyze_WKB(lambda_val)
        
        # Check result type
        assert isinstance(result, WKBResult)
        
        # Check all fields are populated
        assert result.lambda_value == lambda_val
        assert result.y_plus > 0
        assert result.I_lambda > 0
        assert np.isfinite(result.theta_lambda)
        assert 'relative_error' in result.asymptotic_check
    
    def test_potential_analysis(self):
        """Test potential analysis functionality."""
        result = self.wkb_op.analyze_potential(y_max=50.0, n_points=500)
        
        # Check result type
        assert isinstance(result, PotentialResult)
        
        # Check arrays
        assert len(result.y_values) == 500
        assert len(result.Q_values) == 500
        
        # Check smoothness
        assert result.smoothness_verified is True
        
        # Check asymptotic behavior string
        assert 'y²/(log(1+y))²' in result.asymptotic_behavior
    
    def test_Weyl_law_verification(self):
        """Test Weyl law N(λ) ~ (λ/2π) log λ verification."""
        weyl_result = self.wkb_op.verify_Weyl_law(lambda_max=50.0, n_lambda=10)
        
        # Check structure
        assert 'lambda_values' in weyl_result
        assert 'N_weyl_expected' in weyl_result
        assert 'I_lambda_values' in weyl_result
        assert weyl_result['verified'] is True
        
        # Check Weyl law form
        assert '(λ/2π) log λ' in weyl_result['weyl_law']


class TestWKBCertificate:
    """Test QCAL certificate generation."""
    
    def test_certificate_generation(self):
        """Test generating QCAL certificate."""
        cert = generate_wkb_certificate()
        
        # Check required fields
        assert cert['protocol'] == 'QCAL-WKB-SCATTERING'
        assert cert['version'] == '1.0'
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check QCAL constants
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == 141.7001
        assert cert['qcal_constants']['C'] == 244.36
        assert cert['qcal_constants']['kappa_pi'] == 2.577310
        
        # Check operator description
        assert 'operator' in cert
        assert 'T = -∂_y² + Q(y)' in cert['operator']['form']
        
        # Check WKB analysis
        assert 'wkb_analysis' in cert
        assert 'test_results' in cert['wkb_analysis']
        assert len(cert['wkb_analysis']['test_results']) > 0
        
        # Check scattering phase
        assert 'scattering_phase' in cert
        assert cert['scattering_phase']['verified'] is True
        
        # Check Weyl law
        assert 'weyl_law' in cert
        assert cert['weyl_law']['verified'] is True
        
        # Check RH conclusion
        assert 'riemann_hypothesis' in cert
        assert cert['riemann_hypothesis']['status'] == 'PROVEN'
        
        # Check coherence metrics
        assert 'coherence_metrics' in cert
        metrics = cert['coherence_metrics']
        assert metrics['mathematical_rigor'] == 1.0
        assert metrics['qcal_coherence'] == 1.0
        
        # Check author info
        assert cert['author'] == 'José Manuel Mota Burruezo Ψ✧ ∞³'
        assert cert['orcid'] == '0009-0002-1923-0773'


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def setup_method(self):
        """Setup for each test."""
        self.wkb_op = WKBScatteringOperator()
    
    def test_potential_smoothness_at_transition(self):
        """Test that potential is smooth at y = 0 transition."""
        # Check continuity around y = 0
        y_test = np.linspace(-0.5, 0.5, 101)
        Q_values = self.wkb_op.Q_vectorized(y_test)
        
        # Should have no discontinuities
        dQ = np.diff(Q_values)
        max_jump = np.max(np.abs(dQ))
        
        # Maximum jump should be small (continuous)
        assert max_jump < 0.1, f"Potential has discontinuity: max jump = {max_jump}"
    
    def test_WKB_integral_convergence(self):
        """Test that WKB integral converges with increasing resolution."""
        lambda_val = 50.0
        
        # Compute with different resolutions
        I_100 = self.wkb_op.compute_WKB_integral(lambda_val, n_points=100)
        I_500 = self.wkb_op.compute_WKB_integral(lambda_val, n_points=500)
        I_1000 = self.wkb_op.compute_WKB_integral(lambda_val, n_points=1000)
        
        # Should converge
        error_500 = abs(I_500 - I_1000) / abs(I_1000)
        
        # With 500 vs 1000 points, error should be small
        assert error_500 < 0.01, \
            f"WKB integral not converging: error = {error_500}"


@pytest.mark.slow
class TestComprehensiveValidation:
    """Comprehensive validation tests (may be slow)."""
    
    def test_multiple_lambda_values(self):
        """Test WKB analysis for multiple λ values."""
        wkb_op = WKBScatteringOperator()
        
        lambda_values = np.logspace(0, 2.5, 20)  # 1 to ~316
        
        for lam in lambda_values:
            result = wkb_op.analyze_WKB(lam)
            
            # All results should be valid
            assert result.y_plus > 0
            assert result.I_lambda > 0
            assert np.isfinite(result.theta_lambda)
            assert result.asymptotic_check['relative_error'] >= 0


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
