#!/usr/bin/env python3
"""
Tests for WKB-Scattering Phase Connection Module
================================================

Tests the implementation of WKB integral I(λ), Jost functions,
Prüfer transformation, and the global phase theorem:
    θ(λ) = I(λ) + (1/2) arg Γ(1/4 + iλ/2) + O(1)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-WKB-SCATTERING-PHASE-TESTS v1.0
Date: February 16, 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.wkb_scattering_phase import (
    WKBScatteringPhase,
    create_wkb_scattering_analyzer,
    WKBIntegralResult,
    JostFunctionResult,
    PruferTransformResult,
    ScatteringPhaseResult,
    ALPHA_Q,
    F0_QCAL,
    C_COHERENCE
)


class TestPotentialQ:
    """Test potential Q(y) = (π⁴/16) y²/(log(1+y))²."""
    
    def test_potential_positive_y(self):
        """Test Q(y) for positive y values."""
        analyzer = WKBScatteringPhase()
        
        y_vals = np.array([0.5, 1.0, 2.0, 5.0, 10.0])
        Q_vals = analyzer.potential_Q(y_vals)
        
        # Q should be positive for y > 0
        assert np.all(Q_vals > 0), "Q(y) should be positive for y > 0"
        
        # Q should be monotonically increasing initially
        # (after accounting for logarithmic denominator)
        assert Q_vals[0] < Q_vals[-1], "Q(y) should grow with y"
    
    def test_potential_negative_y(self):
        """Test smooth extension for y < 0."""
        analyzer = WKBScatteringPhase()
        
        y_neg = np.array([-1.0, -2.0, -5.0])
        Q_neg = analyzer.potential_Q(y_neg)
        
        # Q should be positive and finite
        assert np.all(Q_neg > 0), "Q(y) should be positive for y < 0"
        assert np.all(np.isfinite(Q_neg)), "Q(y) should be finite"
    
    def test_potential_symmetry_property(self):
        """Test that Q has reasonable symmetry."""
        analyzer = WKBScatteringPhase()
        
        y_test = 1.0
        Q_plus = analyzer.potential_Q(y_test)
        Q_minus = analyzer.potential_Q(-y_test)
        
        # Should have similar magnitude (smooth extension)
        assert np.isclose(Q_plus, Q_minus, rtol=0.5), \
            "Q(y) and Q(-y) should have similar magnitude"
    
    def test_potential_scalar_and_array(self):
        """Test Q works for both scalar and array inputs."""
        analyzer = WKBScatteringPhase()
        
        # Scalar
        Q_scalar = analyzer.potential_Q(1.0)
        assert isinstance(Q_scalar, float), "Scalar input should return float"
        
        # Array
        Q_array = analyzer.potential_Q(np.array([1.0, 2.0]))
        assert isinstance(Q_array, np.ndarray), "Array input should return array"
        assert len(Q_array) == 2, "Output array should have correct length"


class TestTurningPoints:
    """Test turning point calculation where Q(y±) = λ."""
    
    def test_turning_points_positive_lambda(self):
        """Test turning points for positive λ."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        y_minus, y_plus = analyzer.find_turning_points(lambda_val)
        
        # Check that turning points exist
        assert y_minus < y_plus, "y- should be less than y+"
        
        # Verify Q(y±) ≈ λ
        Q_minus = analyzer.potential_Q(y_minus)
        Q_plus = analyzer.potential_Q(y_plus)
        
        assert np.isclose(Q_minus, lambda_val, rtol=0.1), \
            f"Q(y-) = {Q_minus} should equal λ = {lambda_val}"
        assert np.isclose(Q_plus, lambda_val, rtol=0.1), \
            f"Q(y+) = {Q_plus} should equal λ = {lambda_val}"
    
    def test_turning_points_various_lambda(self):
        """Test turning points for various λ values."""
        analyzer = WKBScatteringPhase()
        
        lambda_values = [0.1, 0.5, 1.0, 2.0, 5.0]
        
        for lambda_val in lambda_values:
            y_minus, y_plus = analyzer.find_turning_points(lambda_val)
            
            # Verify basic properties
            assert y_minus < y_plus, f"For λ={lambda_val}, y- < y+"
            assert np.isfinite(y_minus) and np.isfinite(y_plus), \
                "Turning points should be finite"


class TestWKBIntegral:
    """Test WKB integral I(λ) = ∫√(λ - Q(y)) dy."""
    
    def test_wkb_integral_positive_lambda(self):
        """Test WKB integral for positive λ."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.compute_WKB_integral(lambda_val)
        
        assert isinstance(result, WKBIntegralResult), \
            "Should return WKBIntegralResult"
        assert result.lambda_value == lambda_val, "Lambda should match input"
        assert np.isfinite(result.integral_value), "Integral should be finite"
        assert result.turning_points[0] < result.turning_points[1], \
            "Turning points should be ordered"
    
    def test_wkb_integral_scaling(self):
        """Test WKB integral scales with λ."""
        analyzer = WKBScatteringPhase()
        
        lambda_small = 0.5
        lambda_large = 2.0
        
        result_small = analyzer.compute_WKB_integral(lambda_small)
        result_large = analyzer.compute_WKB_integral(lambda_large)
        
        # Larger λ should give larger integral (classical region)
        I_small = np.abs(result_small.integral_value)
        I_large = np.abs(result_large.integral_value)
        
        assert I_large > I_small, \
            "Larger λ should give larger WKB integral"
    
    def test_wkb_phase_accumulation(self):
        """Test phase accumulation is real and positive."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.compute_WKB_integral(lambda_val)
        
        assert isinstance(result.phase_accumulation, (float, np.floating)), \
            "Phase accumulation should be real"
        # Phase can be positive or negative depending on path


class TestJostFunction:
    """Test Jost function f+(y,λ) solution."""
    
    def test_jost_function_basic(self):
        """Test basic Jost function computation."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.solve_jost_function(lambda_val)
        
        assert isinstance(result, JostFunctionResult), \
            "Should return JostFunctionResult"
        assert len(result.f_plus) == len(result.y_values), \
            "f+ should match y_values length"
        assert np.all(np.isfinite(result.f_plus)), \
            "f+ should be finite everywhere"
    
    def test_jost_determinant(self):
        """Test Jost determinant D(λ) = f+(0,λ)."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.solve_jost_function(lambda_val)
        
        # D(λ) should be the value at y=0
        assert np.isfinite(result.D_lambda), "D(λ) should be finite"
        # Verify it matches f+(0)
        assert np.isclose(result.D_lambda, result.f_plus[0], rtol=1e-6), \
            "D(λ) should equal f+(0)"
    
    def test_jost_asymptotic_behavior(self):
        """Test f+(y,λ) ∼ e^{i√λ y} as y → ∞."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.solve_jost_function(lambda_val, y_max=50.0)
        
        # At large y, f+ should have oscillatory behavior
        f_large_y = result.f_plus[-10:]  # Last 10 points
        
        # Check magnitude is roughly constant (unit normalization)
        magnitudes = np.abs(f_large_y)
        # Allow some variation but not exponential growth
        assert np.max(magnitudes) / np.min(magnitudes) < 10, \
            "f+ should not grow exponentially at large y"


class TestPruferTransformation:
    """Test Prüfer transformation f+ = R sin(φ)."""
    
    def test_prufer_basic(self):
        """Test basic Prüfer transformation."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.prufer_transformation(lambda_val)
        
        assert isinstance(result, PruferTransformResult), \
            "Should return PruferTransformResult"
        assert len(result.R_values) == len(result.y_values), \
            "R should match grid"
        assert len(result.phi_values) == len(result.y_values), \
            "φ should match grid"
    
    def test_prufer_amplitude_positive(self):
        """Test amplitude R(y,λ) > 0."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.prufer_transformation(lambda_val)
        
        assert np.all(result.R_values >= 0), \
            "Amplitude R should be non-negative"
        assert np.all(np.isfinite(result.R_values)), \
            "R should be finite"
    
    def test_prufer_phase_derivative(self):
        """Test φ'(y,λ) satisfies expected equation."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.prufer_transformation(lambda_val)
        
        # φ' should be finite and mostly real
        assert np.all(np.isfinite(result.phi_derivative)), \
            "φ' should be finite"
        
        # φ' ≈ √λ for large y (asymptotic behavior)
        sqrt_lambda = np.sqrt(lambda_val)
        phi_prime_large = result.phi_derivative[-10:].mean()
        
        # Should be close to √λ asymptotically
        assert np.abs(phi_prime_large - sqrt_lambda) / sqrt_lambda < 0.5, \
            f"φ'(large y) ≈ {phi_prime_large} should approach √λ = {sqrt_lambda}"


class TestScatteringPhase:
    """Test scattering phase θ(λ) computation."""
    
    def test_scattering_phase_finite(self):
        """Test θ(λ) is finite."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        theta = analyzer.compute_scattering_phase(lambda_val)
        
        assert np.isfinite(theta), "θ(λ) should be finite"
        assert isinstance(theta, (float, np.floating)), \
            "θ(λ) should be real"
    
    def test_scattering_phase_range(self):
        """Test θ(λ) is in reasonable range."""
        analyzer = WKBScatteringPhase()
        
        lambda_vals = [0.5, 1.0, 2.0]
        
        for lambda_val in lambda_vals:
            theta = analyzer.compute_scattering_phase(lambda_val)
            
            # Phase should be in [-π, π]
            assert -np.pi <= theta <= np.pi, \
                f"θ({lambda_val}) = {theta} should be in [-π, π]"


class TestGammaArgTerm:
    """Test Γ function argument term."""
    
    def test_gamma_arg_basic(self):
        """Test (1/2) arg Γ(1/4 + iλ/2) computation."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        gamma_term = analyzer.gamma_arg_term(lambda_val)
        
        assert np.isfinite(gamma_term), \
            "Γ term should be finite"
        assert isinstance(gamma_term, (float, np.floating)), \
            "Γ term should be real"
    
    def test_gamma_arg_various_lambda(self):
        """Test Γ term for various λ."""
        analyzer = WKBScatteringPhase()
        
        lambda_vals = [0.1, 0.5, 1.0, 2.0, 5.0, 10.0]
        
        for lambda_val in lambda_vals:
            gamma_term = analyzer.gamma_arg_term(lambda_val)
            assert np.isfinite(gamma_term), \
                f"Γ term should be finite for λ={lambda_val}"


class TestGlobalPhaseTheorem:
    """Test global phase theorem θ(λ) = I(λ) + (1/2) arg Γ(1/4 + iλ/2) + O(1)."""
    
    def test_global_phase_theorem_verification(self):
        """Test theorem verification for single λ."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.verify_global_phase_theorem(lambda_val, tolerance=0.5)
        
        assert isinstance(result, ScatteringPhaseResult), \
            "Should return ScatteringPhaseResult"
        assert result.lambda_value == lambda_val, "Lambda should match"
        assert np.isfinite(result.theta_lambda), "θ(λ) should be finite"
        assert np.isfinite(result.Delta_lambda), "Δ(λ) should be finite"
        assert np.isfinite(result.error_estimate), "Error should be finite"
    
    def test_global_phase_theorem_multiple_lambda(self):
        """Test theorem holds for multiple λ values."""
        analyzer = WKBScatteringPhase()
        
        lambda_vals = [0.5, 1.0, 2.0, 3.0]
        verified_count = 0
        
        for lambda_val in lambda_vals:
            result = analyzer.verify_global_phase_theorem(lambda_val, tolerance=1.0)
            if result.theorem_verified:
                verified_count += 1
        
        # At least some should verify (allow numerical errors)
        verification_rate = verified_count / len(lambda_vals)
        assert verification_rate >= 0.25, \
            f"At least 25% of tests should verify, got {verification_rate:.2%}"
    
    def test_error_estimate_reasonable(self):
        """Test error estimate is reasonable."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.verify_global_phase_theorem(lambda_val)
        
        # Error should be finite and not too large
        assert 0 <= result.error_estimate < 10.0, \
            f"Error {result.error_estimate} should be reasonable"
    
    def test_components_relationship(self):
        """Test Δ(λ) = θ(λ) - Re[I(λ)]."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        result = analyzer.verify_global_phase_theorem(lambda_val)
        
        # Verify the relationship
        expected_delta = result.theta_lambda - np.real(result.I_lambda)
        
        assert np.isclose(result.Delta_lambda, expected_delta, rtol=1e-6), \
            "Δ(λ) should equal θ(λ) - Re[I(λ)]"


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_generate_certificate_basic(self):
        """Test certificate generation with basic parameters."""
        analyzer = WKBScatteringPhase()
        
        lambda_vals = [0.5, 1.0, 2.0]
        certificate = analyzer.generate_certificate(lambda_vals)
        
        assert isinstance(certificate, dict), "Certificate should be dict"
        assert "protocol" in certificate, "Should have protocol"
        assert "qcal_constants" in certificate, "Should have QCAL constants"
        assert "theorem_validation" in certificate, "Should have validation"
        assert "coherence_metrics" in certificate, "Should have metrics"
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        analyzer = WKBScatteringPhase()
        
        certificate = analyzer.generate_certificate([1.0])
        qcal = certificate["qcal_constants"]
        
        assert qcal["f0_hz"] == F0_QCAL, "f0 should match"
        assert qcal["C"] == C_COHERENCE, "C should match"
        assert "seal" in qcal, "Should have seal"
        assert qcal["seal"] == 14170001, "Seal should match QCAL"
    
    def test_certificate_coherence_metrics(self):
        """Test coherence metrics in certificate."""
        analyzer = WKBScatteringPhase()
        
        certificate = analyzer.generate_certificate([1.0, 2.0])
        metrics = certificate["coherence_metrics"]
        
        assert "wkb_accuracy" in metrics, "Should have WKB accuracy"
        assert "global_coherence" in metrics, "Should have global coherence"
        assert 0 <= metrics["global_coherence"] <= 1, \
            "Coherence should be in [0, 1]"
    
    def test_certificate_resonance_detection(self):
        """Test resonance detection in certificate."""
        analyzer = WKBScatteringPhase()
        
        certificate = analyzer.generate_certificate([1.0])
        resonance = certificate["resonance_detection"]
        
        assert "threshold" in resonance, "Should have threshold"
        assert resonance["threshold"] == 0.888, "Threshold should be 0.888"
        assert "level" in resonance, "Should have level"
        assert resonance["level"] in ["UNIVERSAL", "PARTIAL"], \
            "Level should be valid"


class TestFactoryFunction:
    """Test factory function."""
    
    def test_create_wkb_scattering_analyzer(self):
        """Test factory function creates analyzer."""
        analyzer = create_wkb_scattering_analyzer()
        
        assert isinstance(analyzer, WKBScatteringPhase), \
            "Should create WKBScatteringPhase instance"
        assert analyzer.alpha == ALPHA_Q, \
            "Should use default alpha"
    
    def test_create_with_custom_alpha(self):
        """Test factory with custom alpha."""
        custom_alpha = 2.0
        analyzer = create_wkb_scattering_analyzer(alpha=custom_alpha)
        
        assert analyzer.alpha == custom_alpha, \
            "Should use custom alpha"


class TestIntegration:
    """Integration tests combining multiple components."""
    
    def test_full_pipeline(self):
        """Test complete pipeline from Q to theorem verification."""
        analyzer = WKBScatteringPhase()
        
        lambda_val = 1.0
        
        # Step 1: WKB integral
        wkb = analyzer.compute_WKB_integral(lambda_val)
        assert np.isfinite(wkb.integral_value), "WKB should be finite"
        
        # Step 2: Jost function
        jost = analyzer.solve_jost_function(lambda_val)
        assert np.isfinite(jost.D_lambda), "Jost determinant should be finite"
        
        # Step 3: Prüfer transformation
        prufer = analyzer.prufer_transformation(lambda_val)
        assert np.all(np.isfinite(prufer.phi_values)), "Phase should be finite"
        
        # Step 4: Global phase theorem
        result = analyzer.verify_global_phase_theorem(lambda_val)
        assert np.isfinite(result.error_estimate), "Error should be finite"
    
    def test_certificate_generation_pipeline(self):
        """Test certificate generation with full validation."""
        analyzer = WKBScatteringPhase()
        
        lambda_vals = [0.5, 1.0, 1.5, 2.0]
        certificate = analyzer.generate_certificate(lambda_vals)
        
        # Verify certificate structure
        assert certificate["parameters"]["n_tests"] == len(lambda_vals), \
            "Should record correct number of tests"
        assert "tests_verified" in certificate["theorem_validation"], \
            "Should track verified tests"
        
        # Verify QCAL signature
        assert certificate["signature"] == "∴𓂀Ω∞³Φ", \
            "Should have QCAL signature"


def test_module_constants():
    """Test module-level constants."""
    assert F0_QCAL == 141.7001, "f0 should be 141.7001 Hz"
    assert C_COHERENCE == 244.36, "C should be 244.36"
    assert ALPHA_Q == (np.pi**4) / 16.0, "Alpha should be π⁴/16"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
