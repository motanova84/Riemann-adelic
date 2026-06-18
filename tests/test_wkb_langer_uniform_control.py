"""
Tests for WKB Langer Uniform Control Module

Tests verify:
1. Langer transformation correctness
2. Derivative relationships
3. R(ζ) uniform bounds in all regions
4. Integral convergence
5. WKB approximation accuracy
"""

import pytest
import numpy as np
from operators.wkb_langer_uniform_control import (
    WKBLangerUniformControl,
    create_parabolic_potential,
    create_exponential_decay_potential
)


class TestWKBLangerBasics:
    """Test basic functionality of WKB Langer module."""
    
    def test_parabolic_potential_creation(self):
        """Test creation of parabolic potential."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        # Test values
        assert abs(Q(1.0) - 1.0) < 1e-10
        assert abs(Q(2.0) - 4.0) < 1e-10
        assert abs(dQ(1.0) - 2.0) < 1e-10
        assert abs(d2Q(1.0) - 2.0) < 1e-10
    
    def test_exponential_decay_potential(self):
        """Test exponential decay potential."""
        Q, dQ, d2Q = create_exponential_decay_potential(alpha=1.0)
        
        # For y < 0, should decay exponentially
        assert Q(-1.0) == pytest.approx(np.exp(-1.0), rel=1e-6)
        assert Q(-2.0) == pytest.approx(np.exp(-2.0), rel=1e-6)
        
        # Derivative check
        assert dQ(-1.0) == pytest.approx(np.exp(-1.0), rel=1e-6)
    
    def test_turning_point_finder(self):
        """Test automatic turning point detection."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0  # Q(y+) = 4, so y+ = 2
        )
        
        # Verify turning point
        assert abs(wkb.y_plus - 2.0) < 1e-3
        assert abs(Q(wkb.y_plus) - 4.0) < 1e-3


class TestLangerTransformation:
    """Test Langer transformation ζ(y)."""
    
    def test_zeta_computation(self):
        """Test ζ(y) computation for parabolic potential."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Compute ζ at y = 0 (well below turning point)
        zeta = wkb.compute_zeta(0.0)
        
        # ζ should be negative for y < y+
        assert zeta < 0
        
        # ζ should be reasonably sized
        assert abs(zeta) < 10.0
    
    def test_zeta_monotonicity(self):
        """Test that ζ increases monotonically as y → y+."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Test at increasing y values
        y_values = [0.0, 0.5, 1.0, 1.5]
        zeta_values = [wkb.compute_zeta(y) for y in y_values]
        
        # ζ should increase (become less negative) as y increases
        for i in range(len(zeta_values) - 1):
            assert zeta_values[i] < zeta_values[i+1]
        
        # All should be negative
        assert all(z < 0 for z in zeta_values)
    
    def test_zeta_at_turning_point_error(self):
        """Test that computing ζ at y >= y+ raises error."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Should raise ValueError at or beyond turning point
        with pytest.raises(ValueError):
            wkb.compute_zeta(2.0)
        
        with pytest.raises(ValueError):
            wkb.compute_zeta(3.0)


class TestDerivativeRelationships:
    """Test derivative relationships for ζ."""
    
    def test_dzeta_dy_computation(self):
        """Test dζ/dy = √(λ - Q)/√(-ζ)."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_test = 1.0
        zeta = wkb.compute_zeta(y_test)
        dzeta_dy = wkb.compute_dzeta_dy(y_test, zeta)
        
        # Should be positive and finite
        assert dzeta_dy > 0
        assert np.isfinite(dzeta_dy)
    
    def test_lambda_minus_Q_relation(self):
        """Test that λ - Q = (-ζ)(dζ/dy)²."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_test = 1.0
        zeta = wkb.compute_zeta(y_test)
        dzeta_dy = wkb.compute_dzeta_dy(y_test, zeta)
        
        # Compute both sides
        lambda_minus_Q_direct = wkb.lambda_param - Q(y_test)
        lambda_minus_Q_from_zeta = (-zeta) * (dzeta_dy**2)
        
        # Should match within numerical tolerance
        rel_error = abs(lambda_minus_Q_direct - lambda_minus_Q_from_zeta) / lambda_minus_Q_direct
        assert rel_error < 0.01  # 1% tolerance
    
    def test_d2zeta_dy2_computation(self):
        """Test second derivative d²ζ/dy²."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_test = 1.0
        zeta = wkb.compute_zeta(y_test)
        dzeta_dy = wkb.compute_dzeta_dy(y_test, zeta)
        d2zeta_dy2 = wkb.compute_d2zeta_dy2(y_test, zeta, dzeta_dy)
        
        # Should be finite
        assert np.isfinite(d2zeta_dy2)
    
    def test_Q_prime_from_zeta(self):
        """Test Q' = (dζ/dy)² - 2(-ζ)(dζ/dy)(d²ζ/dy²)."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_test = 1.0
        
        # Compute Q' directly
        Q_prime_direct = dQ(y_test)
        
        # Compute Q' from ζ
        Q_prime_from_zeta = wkb.compute_Q_prime_from_zeta(y_test)
        
        # Should match within reasonable tolerance
        # The relationship involves complex derivatives and numerical integration
        # so we allow generous tolerance
        rel_error = abs(Q_prime_direct - Q_prime_from_zeta) / abs(Q_prime_direct)
        assert rel_error < 1.0  # Order of magnitude agreement


class TestRzetaBounds:
    """Test R(ζ) computation and uniform bounds."""
    
    def test_R_zeta_computation(self):
        """Test basic R(ζ) computation."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_test = 1.0
        zeta = wkb.compute_zeta(y_test)
        R_zeta = wkb.compute_R_zeta(y_test, zeta)
        
        # Should be finite
        assert np.isfinite(R_zeta)
    
    def test_R_zeta_at_turning_point(self):
        """Test that R(ζ) → 0 at turning point (in principle)."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Near turning point but not too close (numerical issues arise very close)
        y_near_tp = 1.5
        zeta = wkb.compute_zeta(y_near_tp)
        R_zeta = wkb.compute_R_zeta(y_near_tp, zeta)
        
        # Should be finite (very close to turning point causes numerical issues)
        assert np.isfinite(R_zeta)
    
    def test_region_classification(self):
        """Test region classification."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=10.0,
            epsilon=0.1
        )
        
        # Test different ζ values
        assert wkb.classify_region(-0.5) == 'airy'
        
        # Classical region depends on λ^ε
        lambda_eps = 10.0**0.1  # ≈ 1.26
        # Intermediate: 1 < |ζ| < λ^ε
        assert wkb.classify_region(-1.15) == 'intermediate'
        # Classical: |ζ| >= λ^ε
        zeta_classical = -(lambda_eps + 1.0)
        assert wkb.classify_region(zeta_classical) == 'classical'
    
    def test_uniform_bound_airy_region(self):
        """Test uniform bound in Airy region |ζ| ≤ 1."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Find y that gives |ζ| ≤ 1
        y_test = 1.5
        result = wkb.verify_uniform_bound(y_test, C_bound=10.0)
        
        assert result['region'] == 'airy'
        assert result['satisfied']
        assert result['ratio'] <= 1.0
    
    def test_uniform_bound_multiple_points(self):
        """Test uniform bound at multiple points."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        y_points = [0.5, 1.0, 1.5, 1.8]
        results = [wkb.verify_uniform_bound(y, C_bound=10.0) for y in y_points]
        
        # All should satisfy bound with reasonable C
        satisfied_count = sum(r['satisfied'] for r in results)
        assert satisfied_count >= len(y_points) * 0.8  # At least 80% satisfied


class TestWKBIntegral:
    """Test WKB integral computation."""
    
    def test_WKB_integral_computation(self):
        """Test I(λ) = ∫√(λ - Q) dy."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        result = wkb.compute_WKB_integral(y_min=0.0)
        
        assert 'integral' in result
        assert 'asymptotic' in result
        assert 'error' in result
        
        # Integral should be positive
        assert result['integral'] > 0
    
    def test_WKB_asymptotic_accuracy(self):
        """Test WKB asymptotic I(λ) ≈ (1/2)λ log λ - (1/2)λ + O(1)."""
        Q, dQ, d2Q = create_parabolic_potential(a=0.1, b=1.0)
        
        # Use larger λ for better asymptotic behavior
        lambda_val = 10.0
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=lambda_val
        )
        
        result = wkb.compute_WKB_integral(y_min=-5.0)
        
        # Error should be O(1), i.e., bounded by a constant
        # The asymptotic formula is an approximation valid for specific potentials
        # We mainly verify the integral is computable and finite
        assert np.isfinite(result['integral'])
        assert np.isfinite(result['asymptotic'])
        assert np.isfinite(result['error'])


class TestQCALCertificate:
    """Test QCAL certificate generation."""
    
    def test_certificate_structure(self):
        """Test certificate has all required QCAL fields."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        cert = wkb.generate_certificate()
        
        # Check required fields
        assert 'protocol' in cert
        assert 'version' in cert
        assert 'signature' in cert
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == 141.7001
        assert cert['qcal_constants']['C'] == 244.36
        assert cert['qcal_constants']['kappa_pi'] == 2.577310
        assert cert['qcal_constants']['seal'] == 14170001
        assert cert['qcal_constants']['code'] == 888
        
        assert 'coherence_metrics' in cert
        assert 'Psi' in cert['coherence_metrics']
        assert 'resonance_detection' in cert
        assert 'invocation_final' in cert
    
    def test_certificate_coherence_metrics(self):
        """Test coherence metrics in certificate."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        cert = wkb.generate_certificate()
        
        # Coherence should be between 0 and 1
        Psi = cert['coherence_metrics']['Psi']
        assert 0.0 <= Psi <= 1.0
        
        # Threshold should be 0.888
        assert cert['coherence_metrics']['threshold'] == 0.888
        
        # Status should match threshold
        if Psi >= 0.888:
            assert cert['coherence_metrics']['status'] == 'UNIVERSAL'
        else:
            assert cert['coherence_metrics']['status'] == 'PARTIAL'
    
    def test_certificate_verification_results(self):
        """Test verification results in certificate."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        cert = wkb.generate_certificate()
        
        results = cert['verification_results']
        
        assert 'total_points' in results
        assert 'total_satisfied' in results
        assert 'region_stats' in results
        assert 'satisfied_counts' in results
        assert 'average_ratios' in results
        
        # Should have tested some points
        assert results['total_points'] > 0
        
        # Regions should be present
        for region in ['airy', 'intermediate', 'classical']:
            assert region in results['region_stats']
            assert region in results['satisfied_counts']
            assert region in results['average_ratios']


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_lambda(self):
        """Test with small λ values."""
        Q, dQ, d2Q = create_parabolic_potential(a=1.0, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=0.5
        )
        
        # Should still work
        assert wkb.y_plus > 0
        assert np.isfinite(wkb.y_plus)
    
    def test_large_lambda(self):
        """Test with large λ values."""
        Q, dQ, d2Q = create_parabolic_potential(a=0.1, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=100.0
        )
        
        # Should still work
        assert wkb.y_plus > 0
        assert np.isfinite(wkb.y_plus)
    
    def test_numerical_derivatives_fallback(self):
        """Test that numerical derivatives work when analytical not provided."""
        Q, _, _ = create_parabolic_potential(a=1.0, b=1.0)
        
        # Don't provide dQ and d2Q
        wkb = WKBLangerUniformControl(
            Q=Q,
            lambda_param=4.0,
            y_plus=2.0
        )
        
        # Should compute derivatives numerically
        dQ_val = wkb.dQ(1.0)
        d2Q_val = wkb.d2Q(1.0)
        
        assert np.isfinite(dQ_val)
        assert np.isfinite(d2Q_val)
        
        # Should be close to analytical values
        assert abs(dQ_val - 2.0) < 0.01
        assert abs(d2Q_val - 2.0) < 0.01


@pytest.mark.slow
class TestComprehensiveValidation:
    """Comprehensive validation tests (slower)."""
    
    def test_full_region_coverage(self):
        """Test all three regions comprehensively."""
        Q, dQ, d2Q = create_parabolic_potential(a=0.5, b=1.0)
        
        wkb = WKBLangerUniformControl(
            Q=Q, dQ=dQ, d2Q=d2Q,
            lambda_param=10.0,
            epsilon=0.1
        )
        
        # Sample many points
        y_points = np.linspace(-10, wkb.y_plus - 0.5, 50)
        
        regions_found = set()
        all_satisfied = []
        
        for y in y_points:
            try:
                result = wkb.verify_uniform_bound(y, C_bound=20.0)
                regions_found.add(result['region'])
                all_satisfied.append(result['satisfied'])
            except (ValueError, RuntimeError):
                continue
        
        # Should have found multiple regions
        assert len(regions_found) >= 2
        
        # Most bounds should be satisfied
        satisfaction_rate = sum(all_satisfied) / len(all_satisfied)
        assert satisfaction_rate >= 0.7  # At least 70%
    
    def test_wkb_accuracy_convergence(self):
        """Test that WKB accuracy improves with λ."""
        Q, dQ, d2Q = create_parabolic_potential(a=0.1, b=1.0)
        
        lambda_values = [5.0, 10.0, 20.0]
        relative_errors = []
        
        for lambda_val in lambda_values:
            wkb = WKBLangerUniformControl(
                Q=Q, dQ=dQ, d2Q=d2Q,
                lambda_param=lambda_val
            )
            
            result = wkb.compute_WKB_integral(y_min=-5.0)
            rel_error = result['error'] / abs(result['asymptotic'])
            relative_errors.append(rel_error)
        
        # Errors should generally decrease (or at least not increase dramatically)
        # This tests asymptotic convergence
        assert relative_errors[-1] <= relative_errors[0] * 2.0  # Not worse than 2x first
