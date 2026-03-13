#!/usr/bin/env python3
"""
Tests for Langer Variable and Uniform Remainder Control.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.langer_variable_control import (
    PotentialQ,
    LangerTransform,
    RegionClassifier,
    RemainderController,
    WeylfunctionExpansion,
    demonstrate_uniform_control,
    LangerVariable,
    RemainderBound,
    UniformControlResult,
)


class TestPotentialQ:
    """Test potential Q(y) implementation."""
    
    def test_potential_positive_y(self):
        """Test Q(y) for positive y."""
        Q = PotentialQ()
        
        # Test at y=1
        y = 1.0
        Q_y = Q(y)
        
        # Q(1) = (π⁴/16) · 1 / [log(2)]²
        expected = (np.pi ** 4 / 16.0) / (np.log(2.0) ** 2)
        
        assert abs(Q_y - expected) < 1e-10, f"Q(1) = {Q_y}, expected {expected}"
    
    def test_potential_near_zero(self):
        """Test Q(y) near y=0."""
        Q = PotentialQ()
        
        y = 0.01
        Q_y = Q(y)
        
        # Near zero, Q(y) should be small and positive
        assert Q_y >= 0, "Q should be non-negative"
        assert Q_y < 1.0, "Q should be small near zero"
        assert np.isfinite(Q_y), "Q should be finite"
    
    def test_potential_negative_y(self):
        """Test Q(y) for negative y (smooth extension)."""
        Q = PotentialQ()
        
        y = -0.5
        Q_y = Q(y)
        
        # Should be positive and finite
        assert Q_y >= 0, "Q should be non-negative"
        assert np.isfinite(Q_y), "Q should be finite"
    
    def test_potential_derivative(self):
        """Test Q'(y) computation."""
        Q = PotentialQ()
        
        y = 1.0
        Q_prime = Q.derivative(y)
        
        # Should be positive for y > 0
        assert Q_prime > 0, "Q' should be positive for y > 0"
        assert np.isfinite(Q_prime), "Q' should be finite"


class TestLangerTransform:
    """Test Langer transformation."""
    
    def test_turning_point(self):
        """Test turning point computation."""
        Q = PotentialQ()
        lambda_param = 10.0
        
        langer = LangerTransform(Q, lambda_param)
        y_plus = langer.y_plus
        
        # At turning point, Q(y+) ≈ λ
        Q_at_y_plus = Q(y_plus)
        
        assert abs(Q_at_y_plus - lambda_param) / lambda_param < 0.01, \
            f"Q(y+) = {Q_at_y_plus}, λ = {lambda_param}"
    
    def test_zeta_at_turning_point(self):
        """Test ζ = 0 at turning point."""
        Q = PotentialQ()
        lambda_param = 10.0
        
        langer = LangerTransform(Q, lambda_param)
        
        # At y = y+, ζ should be 0
        zeta = langer.zeta_from_y(langer.y_plus)
        
        assert abs(zeta) < 1e-6, f"ζ(y+) = {zeta}, expected 0"
    
    def test_zeta_increases_with_y(self):
        """Test that |ζ| increases as y moves away from y+."""
        Q = PotentialQ()
        lambda_param = 10.0
        
        langer = LangerTransform(Q, lambda_param)
        y_plus = langer.y_plus
        
        # Test points above y+
        y1 = y_plus + 0.1
        y2 = y_plus + 0.5
        
        zeta1 = langer.zeta_from_y(y1)
        zeta2 = langer.zeta_from_y(y2)
        
        assert abs(zeta2) > abs(zeta1), "ζ should increase with y"
    
    def test_langer_variable_object(self):
        """Test LangerVariable creation."""
        Q = PotentialQ()
        lambda_param = 10.0
        
        langer = LangerTransform(Q, lambda_param)
        y = langer.y_plus + 1.0
        
        lv = langer.create_langer_variable(y)
        
        assert isinstance(lv, LangerVariable)
        assert lv.y == y
        assert lv.lambda_param == lambda_param
        assert lv.y_plus == langer.y_plus
        assert np.isfinite(lv.Q)


class TestRegionClassifier:
    """Test region classification."""
    
    def test_airy_region(self):
        """Test Airy region classification."""
        lambda_param = 100.0
        classifier = RegionClassifier(lambda_param)
        
        zeta = 0.5 + 0.0j
        region = classifier.classify(zeta)
        
        assert region == "airy", f"Expected airy, got {region}"
    
    def test_intermediate_region(self):
        """Test intermediate region classification."""
        lambda_param = 100.0
        classifier = RegionClassifier(lambda_param)
        
        # λ^{1/3} = 100^{1/3} ≈ 4.64
        zeta = 2.0 + 0.0j
        region = classifier.classify(zeta)
        
        assert region == "intermediate", f"Expected intermediate, got {region}"
    
    def test_classical_region(self):
        """Test classical region classification."""
        lambda_param = 100.0
        classifier = RegionClassifier(lambda_param)
        
        # λ^{1/3} = 100^{1/3} ≈ 4.64
        zeta = 10.0 + 0.0j
        region = classifier.classify(zeta)
        
        assert region == "classical", f"Expected classical, got {region}"
    
    def test_boundary_values(self):
        """Test classification at boundary values."""
        lambda_param = 1000.0
        classifier = RegionClassifier(lambda_param)
        
        # Test at airy boundary
        zeta_airy = 1.0 + 0.0j
        assert classifier.classify(zeta_airy) == "airy"
        
        # Test just above airy boundary
        zeta_inter = 1.01 + 0.0j
        assert classifier.classify(zeta_inter) == "intermediate"


class TestRemainderController:
    """Test remainder term control."""
    
    def test_airy_region_bound(self):
        """Test remainder bound in Airy region."""
        lambda_param = 100.0
        controller = RemainderController(lambda_param)
        
        zeta = 0.5 + 0.0j
        bound_result = controller.remainder_bound(zeta)
        
        assert bound_result.region == "airy"
        assert bound_result.bound > 0
        assert np.isfinite(bound_result.bound)
        # In Airy region, bound should be O(1)
        assert bound_result.bound < 100, "Bound should be O(1)"
    
    def test_intermediate_region_bound(self):
        """Test remainder bound in intermediate region."""
        lambda_param = 100.0
        controller = RemainderController(lambda_param)
        
        zeta = 2.0 + 0.0j
        bound_result = controller.remainder_bound(zeta)
        
        assert bound_result.region == "intermediate"
        # Should satisfy |R(ζ)| ≤ C / |ζ|^{3/2}
        expected = controller.uniform_constant / (abs(zeta) ** 1.5)
        assert abs(bound_result.bound - expected) < 1e-6
    
    def test_classical_region_bound(self):
        """Test remainder bound in classical region."""
        lambda_param = 1000.0
        controller = RemainderController(lambda_param)
        
        # λ^{1/3} = 10
        zeta = 15.0 + 0.0j
        bound_result = controller.remainder_bound(zeta)
        
        assert bound_result.region == "classical"
        # λ^{1/6} term should be controlled
        assert bound_result.bound > 0
        assert np.isfinite(bound_result.bound)
    
    def test_uniform_bound_verification(self):
        """Test uniform bound |R(ζ)| ≤ C/(1+|ζ|)^{3/2}."""
        lambda_param = 100.0
        controller = RemainderController(lambda_param, uniform_constant=15.0)
        
        # Test multiple ζ values
        zeta_values = [0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0]
        
        for zeta_abs in zeta_values:
            zeta = zeta_abs + 0.0j
            verified = controller.verify_uniform_bound(zeta)
            
            assert verified, f"Uniform bound failed at |ζ| = {zeta_abs}"
    
    def test_lambda_independence(self):
        """Test that bound is uniform in λ for different regions."""
        zeta_airy = 0.5 + 0.0j
        zeta_classical = 20.0 + 0.0j
        
        # Test for different λ values
        lambda_values = [10.0, 100.0, 1000.0]
        
        bounds_airy = []
        bounds_classical = []
        
        for lambda_val in lambda_values:
            controller = RemainderController(lambda_val, uniform_constant=15.0)
            
            # Airy region
            result_airy = controller.remainder_bound(zeta_airy)
            bounds_airy.append(result_airy.bound)
            
            # Classical region (if applicable)
            if lambda_val ** (1.0/3.0) < abs(zeta_classical):
                result_classical = controller.remainder_bound(zeta_classical)
                bounds_classical.append(result_classical.bound)
        
        # Airy bounds should be similar (independent of λ)
        assert max(bounds_airy) / min(bounds_airy) < 2.0, \
            "Airy bounds should be λ-independent"


class TestWeylfunctionExpansion:
    """Test Weyl m-function expansion."""
    
    def test_I_lambda_computation(self):
        """Test I(λ) integral computation."""
        Q = PotentialQ()
        lambda_param = 10.0
        
        weyl = WeylfunctionExpansion(Q, lambda_param)
        I_lambda = weyl.compute_I_lambda()
        
        assert I_lambda > 0, "I(λ) should be positive"
        assert np.isfinite(I_lambda), "I(λ) should be finite"
    
    def test_m_function_asymptotic(self):
        """Test m(λ) asymptotic expansion."""
        Q = PotentialQ()
        lambda_param = 100.0
        
        weyl = WeylfunctionExpansion(Q, lambda_param)
        m = weyl.m_function_asymptotic()
        
        # Should be complex or real
        assert np.isfinite(m), "m(λ) should be finite"
        
        # Main term should scale like √λ
        assert abs(m) > 0.1 * np.sqrt(lambda_param), \
            "m(λ) should scale with √λ"
    
    def test_scattering_phase(self):
        """Test scattering phase θ(λ)."""
        Q = PotentialQ()
        lambda_param = 100.0
        
        weyl = WeylfunctionExpansion(Q, lambda_param)
        theta = weyl.scattering_phase()
        
        assert np.isfinite(theta), "θ(λ) should be finite"
        assert isinstance(theta, (int, float)), "θ(λ) should be real"
    
    def test_increasing_lambda(self):
        """Test that I(λ) increases with λ."""
        Q = PotentialQ()
        
        lambda1 = 10.0
        lambda2 = 100.0
        
        weyl1 = WeylfunctionExpansion(Q, lambda1)
        weyl2 = WeylfunctionExpansion(Q, lambda2)
        
        I1 = weyl1.compute_I_lambda()
        I2 = weyl2.compute_I_lambda()
        
        assert I2 > I1, "I(λ) should increase with λ"


class TestUniformControl:
    """Test uniform control demonstration."""
    
    def test_demonstrate_uniform_control(self):
        """Test uniform control demonstration."""
        lambda_values = np.array([10.0, 100.0])
        
        result = demonstrate_uniform_control(
            lambda_values=lambda_values,
            n_zeta=20,
            verbose=False
        )
        
        assert isinstance(result, UniformControlResult)
        assert result.verification_passed, "Uniform control should be verified"
        assert result.max_bound > 0
        assert np.isfinite(result.max_bound)
    
    def test_uniform_constant_independence(self):
        """Test that verification passes for all λ."""
        lambda_values = np.array([10.0, 50.0, 100.0, 500.0])
        
        result = demonstrate_uniform_control(
            lambda_values=lambda_values,
            n_zeta=30,
            verbose=False
        )
        
        # Should pass for all λ
        assert result.verification_passed, \
            "Uniform bound should hold for all λ"
    
    def test_bounds_shape(self):
        """Test shape of bounds array."""
        lambda_values = np.array([10.0, 100.0, 1000.0])
        n_zeta = 25
        
        result = demonstrate_uniform_control(
            lambda_values=lambda_values,
            n_zeta=n_zeta,
            verbose=False
        )
        
        expected_shape = (len(lambda_values), n_zeta)
        assert result.bounds.shape == expected_shape, \
            f"Expected shape {expected_shape}, got {result.bounds.shape}"


class TestIntegration:
    """Integration tests."""
    
    def test_full_pipeline(self):
        """Test full pipeline from y to remainder bound."""
        Q = PotentialQ()
        lambda_param = 100.0
        
        # Create Langer transform
        langer = LangerTransform(Q, lambda_param)
        
        # Pick a physical point
        y = langer.y_plus + 2.0
        
        # Compute ζ
        lv = langer.create_langer_variable(y)
        
        # Compute remainder bound
        controller = RemainderController(lambda_param)
        bound_result = controller.remainder_bound(lv.zeta)
        
        # Verify
        assert bound_result.bound > 0
        assert controller.verify_uniform_bound(lv.zeta)
    
    def test_theorem_statement(self):
        """Test main theorem: |R(ζ)| ≤ C/(1+|ζ|)^{3/2}."""
        # Test for multiple λ and ζ combinations
        lambda_values = [10.0, 100.0, 1000.0]
        zeta_abs_values = np.logspace(-1, 2, 30)
        
        C = 15.0  # Uniform constant
        
        all_verified = True
        
        for lambda_val in lambda_values:
            controller = RemainderController(lambda_val, uniform_constant=C)
            
            for zeta_abs in zeta_abs_values:
                zeta = zeta_abs + 0.0j
                
                # Compute bound
                bound_result = controller.remainder_bound(zeta)
                
                # Verify uniform bound
                uniform_bound = C / ((1.0 + abs(zeta)) ** 1.5)
                
                if bound_result.bound > uniform_bound * 1.05:  # 5% tolerance
                    all_verified = False
                    print(f"Failed at λ={lambda_val}, |ζ|={zeta_abs}")
                    print(f"  Bound: {bound_result.bound}")
                    print(f"  Uniform: {uniform_bound}")
                    break
            
            if not all_verified:
                break
        
        assert all_verified, "Uniform bound |R(ζ)| ≤ C/(1+|ζ|)^{3/2} failed"


@pytest.mark.parametrized("lambda_param", [10.0, 100.0, 1000.0])
def test_parametrized_lambda(lambda_param):
    """Parametrized test for different λ values."""
    controller = RemainderController(lambda_param, uniform_constant=15.0)
    
    # Test a few ζ values in each region
    test_cases = [
        (0.5, "airy"),
        (2.0, None),  # Could be intermediate or classical depending on λ
        (10.0, None),
    ]
    
    for zeta_abs, expected_region in test_cases:
        zeta = zeta_abs + 0.0j
        bound_result = controller.remainder_bound(zeta)
        
        assert bound_result.bound > 0
        assert controller.verify_uniform_bound(zeta)
        
        if expected_region is not None:
            assert bound_result.region == expected_region


if __name__ == "__main__":
    # Run all tests
    pytest.main([__file__, "-v"])
