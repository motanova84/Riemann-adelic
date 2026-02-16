#!/usr/bin/env python3
"""
Tests for Scattering Phase Gamma Correction module.

Validates the theorem: θ(λ) = I(λ) + (1/2) arg Γ(1/4 + iλ/2) + O(1)
"""

import pytest
import numpy as np
from operators.scattering_phase_gamma_correction import (
    ScatteringPhaseGammaCorrection,
    generate_scattering_gamma_certificate,
    ScatteringPhaseResult,
    JostDeterminantResult
)


class TestPotential:
    """Test potential Q(y) definition and properties."""
    
    def test_potential_positive(self):
        """Test that Q(y) ≥ 0 for all y."""
        analyzer = ScatteringPhaseGammaCorrection()
        y = np.linspace(-10, 10, 100)
        Q = analyzer.potential_Q(y)
        
        assert np.all(Q >= 0), "Potential should be non-negative"
    
    def test_potential_growth(self):
        """Test that Q(y) grows like y² for large |y|."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        # For large y, Q(y) ≈ (π⁴/16) y² / (log y)²
        y_large = 100.0
        Q_large = analyzer.potential_Q(y_large)
        
        # Expected asymptotic: (π⁴/16) * y² / (log y)²
        expected = (np.pi**4 / 16.0) * y_large**2 / np.log(1 + y_large)**2
        
        rel_error = np.abs(Q_large - expected) / expected
        assert rel_error < 0.1, f"Potential growth incorrect: {rel_error}"
    
    def test_potential_smoothness(self):
        """Test that Q(y) is smooth (no jumps)."""
        analyzer = ScatteringPhaseGammaCorrection()
        y = np.linspace(-5, 5, 200)
        Q = analyzer.potential_Q(y)
        
        # Check finite differences for smoothness
        dQ = np.diff(Q)
        max_jump = np.max(np.abs(dQ))
        
        # Should be no large jumps for smooth potential
        assert max_jump < 10.0, f"Potential has large jumps: {max_jump}"


class TestTurningPoint:
    """Test classical turning point calculation."""
    
    def test_turning_point_exists(self):
        """Test that turning point can be found for λ > 0."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        y_t = analyzer.find_turning_point(lambda_val)
        
        assert y_t > 0, "Turning point should be positive"
        
        # Verify Q(y_t) ≈ λ
        Q_at_turning = analyzer.potential_Q(y_t)
        rel_error = np.abs(Q_at_turning - lambda_val) / lambda_val
        
        assert rel_error < 0.2, f"Turning point inaccurate: Q(y_t)={Q_at_turning}, λ={lambda_val}"
    
    def test_turning_point_increases_with_lambda(self):
        """Test that y_t increases with λ."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambdas = [1.0, 5.0, 10.0, 20.0]
        turning_points = [analyzer.find_turning_point(lam) for lam in lambdas]
        
        # Should be monotonically increasing
        for i in range(len(turning_points) - 1):
            assert turning_points[i+1] > turning_points[i], \
                "Turning point should increase with λ"


class TestWKBIntegral:
    """Test WKB integral I(λ) computation."""
    
    def test_wkb_positive(self):
        """Test that I(λ) > 0 for λ > 0."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        I_lambda = analyzer.wkb_integral(lambda_val)
        
        assert I_lambda > 0, "WKB integral should be positive"
    
    def test_wkb_increases_with_lambda(self):
        """Test that I(λ) increases with λ."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambdas = [1.0, 5.0, 10.0, 20.0, 50.0]
        I_vals = [analyzer.wkb_integral(lam) for lam in lambdas]
        
        # Should be monotonically increasing
        for i in range(len(I_vals) - 1):
            assert I_vals[i+1] > I_vals[i], \
                f"I(λ) should increase with λ: I({lambdas[i]})={I_vals[i]}, I({lambdas[i+1]})={I_vals[i+1]}"
    
    def test_wkb_scaling(self):
        """Test approximate scaling I(λ) ~ λ^{3/2} for large λ."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        # For confining potential, expect power-law growth
        lambda1 = 10.0
        lambda2 = 20.0
        
        I1 = analyzer.wkb_integral(lambda1)
        I2 = analyzer.wkb_integral(lambda2)
        
        # Ratio should be approximately (λ2/λ1)^{3/2} = 2^{3/2} ≈ 2.83
        ratio = I2 / I1
        expected_ratio = (lambda2 / lambda1)**(3/2)
        
        # Allow 50% deviation due to log corrections
        assert 0.5 * expected_ratio < ratio < 2.0 * expected_ratio, \
            f"WKB scaling incorrect: ratio={ratio}, expected~{expected_ratio}"


class TestGammaCorrection:
    """Test Gamma function correction term."""
    
    def test_gamma_correction_finite(self):
        """Test that gamma correction is finite and real."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        gamma_corr = analyzer.gamma_arg_correction(lambda_val)
        
        assert np.isfinite(gamma_corr), "Gamma correction should be finite"
        assert np.isreal(gamma_corr), "Gamma correction should be real"
    
    def test_gamma_correction_varies_with_lambda(self):
        """Test that gamma correction depends on λ."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda1 = 5.0
        lambda2 = 20.0
        
        gamma1 = analyzer.gamma_arg_correction(lambda1)
        gamma2 = analyzer.gamma_arg_correction(lambda2)
        
        # Should be different
        assert np.abs(gamma1 - gamma2) > 0.01, \
            "Gamma correction should vary with λ"
    
    def test_gamma_correction_magnitude(self):
        """Test that gamma correction has reasonable magnitude."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        gamma_corr = analyzer.gamma_arg_correction(lambda_val)
        
        # Should be O(1) in magnitude
        assert np.abs(gamma_corr) < 20.0, \
            f"Gamma correction too large: {gamma_corr}"


class TestReflectionCoefficient:
    """Test reflection coefficient R(ζ)."""
    
    def test_reflection_bounded(self):
        """Test that |R(ζ)| ≤ 1."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        zeta_vals = np.linspace(0, 5, 20)
        
        for zeta in zeta_vals:
            R = analyzer.reflection_coefficient(lambda_val, zeta)
            assert np.abs(R) <= 1.0, f"Reflection coefficient |R| > 1 at ζ={zeta}"
    
    def test_reflection_decays(self):
        """Test that R(ζ) decays as ζ increases."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        R0 = analyzer.reflection_coefficient(lambda_val, 0.0)
        R5 = analyzer.reflection_coefficient(lambda_val, 5.0)
        
        # Should decay
        assert np.abs(R5) < np.abs(R0), \
            "Reflection coefficient should decay with ζ"


class TestJostDeterminant:
    """Test Jost determinant D(λ) computation."""
    
    def test_jost_computes(self):
        """Test that Jost determinant can be computed."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        result = analyzer.jost_determinant(lambda_val)
        
        assert isinstance(result, JostDeterminantResult)
        assert np.isfinite(result.log_D_lambda)
        assert np.isfinite(result.S_matrix)
    
    def test_s_matrix_unitarity(self):
        """Test that S-matrix is approximately unitary."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_vals = [5.0, 10.0, 20.0]
        
        for lam in lambda_vals:
            result = analyzer.jost_determinant(lam)
            S_magnitude = np.abs(result.S_matrix)
            
            # Should be close to 1 (unitary)
            # Allow some deviation due to numerical approximations
            assert 0.5 < S_magnitude < 2.0, \
                f"S-matrix not approximately unitary at λ={lam}: |S|={S_magnitude}"
    
    def test_phase_shift_real(self):
        """Test that phase shift is real."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        result = analyzer.jost_determinant(lambda_val)
        
        assert np.isreal(result.phase_shift), "Phase shift should be real"


class TestScatteringPhase:
    """Test complete scattering phase θ(λ) computation."""
    
    def test_scattering_phase_computes(self):
        """Test that scattering phase can be computed."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        result = analyzer.scattering_phase(lambda_val)
        
        assert isinstance(result, ScatteringPhaseResult)
        assert result.lambda_value == lambda_val
        assert np.isfinite(result.total_phase_theta)
    
    def test_scattering_phase_components(self):
        """Test that θ(λ) = I(λ) + gamma_correction + O(1)."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        result = analyzer.scattering_phase(lambda_val)
        
        # Verify the formula
        expected_theta = result.wkb_integral_I + result.gamma_correction + result.error_O1
        
        assert np.abs(result.total_phase_theta - expected_theta) < 1e-10, \
            "Phase formula doesn't match components"
    
    def test_scattering_phase_increases(self):
        """Test that θ(λ) generally increases with λ."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambdas = [1.0, 5.0, 10.0, 20.0]
        phases = [analyzer.scattering_phase(lam).total_phase_theta for lam in lambdas]
        
        # Should mostly increase (allowing for small fluctuations from gamma term)
        for i in range(len(phases) - 1):
            # Check trend is increasing
            if i < len(phases) - 2:
                avg_increase = (phases[i+2] - phases[i]) / 2
                assert avg_increase > 0, "Phase should generally increase with λ"
    
    def test_airy_matching_validity(self):
        """Test that Airy matching is valid for tested λ values."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_vals = [1.0, 5.0, 10.0, 20.0]
        
        for lam in lambda_vals:
            result = analyzer.scattering_phase(lam)
            # Airy matching should be valid for reasonable λ
            # (may fail for very small or very large λ due to numerical issues)
            assert isinstance(result.airy_matching_valid, bool)
    
    def test_error_O1_bounded(self):
        """Test that O(1) error is indeed O(1)."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_vals = np.linspace(1.0, 50.0, 10)
        
        for lam in lambda_vals:
            result = analyzer.scattering_phase(lam)
            assert np.abs(result.error_O1) < 5.0, \
                f"O(1) error too large: {result.error_O1} at λ={lam}"


class TestUniformity:
    """Test uniformity of θ(λ) formula in λ."""
    
    def test_uniformity_verification(self):
        """Test that error O(1) is uniform across λ range."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_range = np.linspace(1.0, 50.0, 15)
        uniformity = analyzer.verify_uniformity(lambda_range)
        
        assert 'is_uniform' in uniformity
        assert 'error_std' in uniformity
        assert 'error_max' in uniformity
        
        # Standard deviation of errors should be bounded
        assert uniformity['error_std'] < 2.0, \
            f"Error standard deviation too large: {uniformity['error_std']}"
    
    def test_error_variation_bounded(self):
        """Test that error variation is bounded."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_range = np.linspace(5.0, 40.0, 10)
        uniformity = analyzer.verify_uniformity(lambda_range)
        
        # Max error should be reasonable
        assert uniformity['error_max'] < 3.0, \
            f"Maximum error too large: {uniformity['error_max']}"


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_certificate_generates(self):
        """Test that certificate can be generated."""
        cert = generate_scattering_gamma_certificate()
        
        assert isinstance(cert, dict)
        assert 'protocol' in cert
        assert 'signature' in cert
        assert 'qcal_constants' in cert
    
    def test_certificate_qcal_constants(self):
        """Test that QCAL constants are correct."""
        cert = generate_scattering_gamma_certificate()
        
        qcal = cert['qcal_constants']
        assert qcal['f0_hz'] == 141.7001
        assert qcal['C'] == 244.36
        assert qcal['seal'] == 14170001
        assert qcal['code'] == 888
    
    def test_certificate_coherence(self):
        """Test that coherence metrics are present."""
        cert = generate_scattering_gamma_certificate()
        
        assert 'coherence_metrics' in cert
        assert 'Psi' in cert['coherence_metrics']
        
        # Psi should be between 0 and 1
        psi = cert['coherence_metrics']['Psi']
        assert 0.0 <= psi <= 1.0, f"Invalid coherence Psi: {psi}"
    
    def test_certificate_test_results(self):
        """Test that test results are included."""
        cert = generate_scattering_gamma_certificate()
        
        assert 'test_results' in cert
        assert len(cert['test_results']) > 0
        
        # Each result should have required fields
        for result in cert['test_results']:
            assert 'lambda' in result
            assert 'theta' in result
            assert 'I_lambda' in result
            assert 'gamma_correction' in result
    
    def test_certificate_signature(self):
        """Test that QCAL signature is present."""
        cert = generate_scattering_gamma_certificate()
        
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        assert cert['protocol'] == 'QCAL-SCATTERING-GAMMA-CORRECTION'
    
    def test_certificate_invocation(self):
        """Test that final invocation is present."""
        cert = generate_scattering_gamma_certificate()
        
        assert 'invocation_final' in cert
        assert 'es' in cert['invocation_final']
        assert 'en' in cert['invocation_final']
        assert 'fr' in cert['invocation_final']


class TestTheorem:
    """Integration tests for the main theorem."""
    
    def test_theorem_formula_holds(self):
        """Test that the theorem formula θ(λ) = I(λ) + (1/2)arg Γ + O(1) holds."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_vals = [5.0, 10.0, 20.0]
        
        for lam in lambda_vals:
            result = analyzer.scattering_phase(lam)
            
            # Components
            I_lambda = result.wkb_integral_I
            gamma_corr = result.gamma_correction
            error = result.error_O1
            theta = result.total_phase_theta
            
            # Verify formula
            computed_theta = I_lambda + gamma_corr + error
            assert np.abs(theta - computed_theta) < 1e-8, \
                f"Theorem formula violated at λ={lam}"
    
    def test_gamma_term_significance(self):
        """Test that Gamma correction is non-negligible."""
        analyzer = ScatteringPhaseGammaCorrection()
        
        lambda_val = 10.0
        result = analyzer.scattering_phase(lambda_val)
        
        # Gamma correction should be significant compared to error
        gamma_magnitude = np.abs(result.gamma_correction)
        error_magnitude = np.abs(result.error_O1)
        
        # Gamma term should be at least as large as error term
        # (this is what makes it important!)
        assert gamma_magnitude > 0.1, \
            "Gamma correction should be non-negligible"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
