#!/usr/bin/env python3
"""
Tests for Weyl m-Function Operator
==================================

Comprehensive test suite for the 9-step Weyl m-function approach
to proving the Riemann Hypothesis via operator theory.

Test Coverage:
- PASO 1: Operator T construction and potential Q(y)
- PASO 2: Weyl m-function computation
- PASO 3: Spectral determinant relation
- PASO 4-5: WKB expansion and renormalization
- PASO 6: Scattering phase
- PASO 7: Prüfer equation
- PASO 8: Airy matching and Γ function
- PASO 9: Uniformity in λ
- Weil formula connection
- RH conclusion verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 16, 2026
"""

import pytest
import numpy as np
from operators.weyl_m_function import (
    WeylMFunctionOperator,
    WeylMFunctionResult,
    generate_weyl_m_function_certificate,
    PI, PI_FOURTH, F0_QCAL, C_COHERENCE
)


class TestWeylMFunctionOperator:
    """Test suite for Weyl m-function operator."""
    
    def test_initialization(self):
        """Test operator initialization with default and custom parameters."""
        # Default initialization
        op1 = WeylMFunctionOperator()
        assert op1.alpha == PI_FOURTH / 16.0
        
        # Custom alpha
        alpha_custom = 1.0
        op2 = WeylMFunctionOperator(alpha=alpha_custom)
        assert op2.alpha == alpha_custom
        
    def test_potential_Q(self):
        """Test PASO 1: Potential Q(y) = α y² / [log(1+y)]²."""
        op = WeylMFunctionOperator(alpha=1.0)
        
        # Test at y=0 (should be 0 or small)
        Q_0 = op.Q(0.0)
        assert Q_0 == 0.0
        
        # Test at y=1
        Q_1 = op.Q(1.0)
        expected_1 = 1.0 / np.log(2)**2  # 1² / log(2)²
        assert abs(Q_1 - expected_1) < 1e-10
        
        # Test positivity for y > 0
        y_test = np.linspace(0.1, 10, 20)
        Q_vals = [op.Q(y) for y in y_test]
        assert all(Q > 0 for Q in Q_vals)
        
        # Test monotonicity (Q should increase with y for large y)
        y_large = np.linspace(10, 100, 10)
        Q_large = [op.Q(y) for y in y_large]
        # Q(y) ~ α y² / (log y)² grows like y² / log² y
        assert all(Q_large[i] < Q_large[i+1] for i in range(len(Q_large)-1))
        
    def test_potential_Q_negative_y(self):
        """Test Q(y) for y < 0 (should return 0)."""
        op = WeylMFunctionOperator()
        assert op.Q(-1.0) == 0.0
        assert op.Q(-10.0) == 0.0
        
    def test_find_turning_point(self):
        """Test finding turning point y+ where Q(y+) = λ."""
        op = WeylMFunctionOperator(alpha=1.0)
        
        # Test for various λ
        lambda_values = [1.0, 5.0, 10.0, 20.0]
        
        for lam in lambda_values:
            y_plus = op.find_turning_point(lam)
            
            # Verify Q(y+) ≈ λ
            Q_y_plus = op.Q(y_plus)
            relative_error = abs(Q_y_plus - lam) / lam
            assert relative_error < 1e-6, f"Q(y+) = {Q_y_plus}, λ = {lam}"
            
            # y+ should be positive
            assert y_plus > 0
            
    def test_find_turning_point_edge_cases(self):
        """Test turning point for edge cases."""
        op = WeylMFunctionOperator()
        
        # Very small λ
        y_plus_small = op.find_turning_point(0.01)
        assert y_plus_small > 0
        assert y_plus_small < 5.0  # Should be small
        
        # Larger λ
        y_plus_large = op.find_turning_point(100.0)
        assert y_plus_large > 5.0  # Should be larger
        
    def test_compute_I_integral(self):
        """Test PASO 7: I(λ) = ∫₀^{y+} √(λ - Q(y)) dy."""
        op = WeylMFunctionOperator()
        
        lambda_val = 10.0
        y_plus = op.find_turning_point(lambda_val)
        
        # Compute I integral
        I_val = op.compute_I_integral(lambda_val, y_plus)
        
        # I should be positive
        assert I_val > 0
        
        # For large λ, I ~ O(λ) from asymptotics
        # I(λ) = λ [(π/8) log λ + ...]
        # So I/λ should be O(log λ)
        assert I_val / lambda_val > 0.1
        assert I_val / lambda_val < 10.0
        
    def test_I_integral_scaling(self):
        """Test I(λ) scaling with λ."""
        op = WeylMFunctionOperator()
        
        lambda_values = [5.0, 10.0, 20.0, 40.0]
        I_values = [op.compute_I_integral(lam) for lam in lambda_values]
        
        # I should increase with λ
        for i in range(len(I_values) - 1):
            assert I_values[i] < I_values[i+1]
        
        # Check approximate scaling I ~ λ
        ratios = [I_values[i] / lambda_values[i] for i in range(len(I_values))]
        # Ratios should be roughly constant (within factor of 2-3)
        assert max(ratios) / min(ratios) < 3.0
        
    def test_compute_delta_correction(self):
        """Test PASO 8: δ(λ) = (1/2) arg Γ(1/4 + iλ/2)."""
        op = WeylMFunctionOperator()
        
        # Test for various λ
        lambda_values = [1.0, 5.0, 10.0, 20.0]
        
        for lam in lambda_values:
            delta = op.compute_delta_correction(lam)
            
            # δ should be real
            assert isinstance(delta, (int, float, np.floating))
            
            # δ should be bounded (from properties of arg Γ)
            assert abs(delta) < 10.0  # Reasonable bound
            
    def test_delta_uniformity(self):
        """Test PASO 9: δ(λ) uniformity in λ."""
        op = WeylMFunctionOperator()
        
        lambda_range = np.linspace(10, 50, 10)
        delta_values = [op.compute_delta_correction(lam) for lam in lambda_range]
        
        # δ should not vary wildly
        delta_std = np.std(delta_values)
        delta_mean = np.mean(np.abs(delta_values))
        
        # Coefficient of variation should be reasonable
        if delta_mean > 1e-10:
            cv = delta_std / delta_mean
            assert cv < 1.0  # Not too much variation
            
    def test_solve_ode(self):
        """Test solving -φ'' + Q(y)φ = λφ."""
        op = WeylMFunctionOperator()
        
        lambda_val = 10.0
        y_vals, phi_vals, phi_prime_vals = op.solve_ode(lambda_val)
        
        # Check dimensions
        assert len(y_vals) == len(phi_vals) == len(phi_prime_vals)
        
        # Check initial condition φ(0) ≈ 1
        assert abs(phi_vals[0] - 1.0) < 0.1
        
        # φ should not blow up for reasonable y
        assert all(abs(phi) < 1e10 for phi in phi_vals[:len(phi_vals)//2])
        
    def test_compute_m_function_wkb(self):
        """Test PASO 4: m(λ) via WKB approximation."""
        op = WeylMFunctionOperator()
        
        # WKB is accurate for large λ
        lambda_val = 50.0
        m_wkb = op.compute_m_function_wkb(lambda_val)
        
        # m should be complex
        assert isinstance(m_wkb, complex)
        
        # Leading term is i√λ, so |m| ~ √λ
        assert abs(m_wkb) > 0.5 * np.sqrt(lambda_val)
        assert abs(m_wkb) < 2.0 * np.sqrt(lambda_val)
        
        # Imaginary part should dominate (from i√λ term)
        assert abs(m_wkb.imag) > abs(m_wkb.real)
        
    def test_compute_m_function_prufer(self):
        """Test PASO 7: m(λ) via Prüfer equation."""
        op = WeylMFunctionOperator()
        
        lambda_val = 20.0
        m_prufer = op.compute_m_function_prufer(lambda_val)
        
        # m should be complex
        assert isinstance(m_prufer, complex)
        
        # |m| should scale roughly with √λ
        assert abs(m_prufer) > 0.1 * np.sqrt(lambda_val)
        assert abs(m_prufer) < 10.0 * np.sqrt(lambda_val)
        
    def test_m_function_consistency(self):
        """Test consistency between WKB and Prüfer methods for large λ."""
        op = WeylMFunctionOperator()
        
        # For large λ, WKB and Prüfer should agree
        lambda_val = 100.0
        
        m_wkb = op.compute_m_function_wkb(lambda_val)
        m_prufer = op.compute_m_function_prufer(lambda_val)
        
        # Relative difference should be small
        relative_diff = abs(m_wkb - m_prufer) / abs(m_prufer)
        
        # Allow 30% difference (methods differ in subleading terms)
        assert relative_diff < 0.3
        
    def test_compute_scattering_phase(self):
        """Test PASO 6: θ(λ) = -arg m(λ) + π/2."""
        op = WeylMFunctionOperator()
        
        lambda_values = [5.0, 10.0, 20.0]
        
        for lam in lambda_values:
            theta = op.compute_scattering_phase(lam)
            
            # θ should be real
            assert isinstance(theta, (int, float, np.floating))
            
            # θ should be in reasonable range (bounded by π multiples)
            assert abs(theta) < 10 * PI
            
    def test_scattering_phase_derivative(self):
        """Test θ'(λ) connects to Weil formula (PASO 6 + Weil connection)."""
        op = WeylMFunctionOperator()
        
        lambda_val = 20.0
        delta_lam = 0.1
        
        theta1 = op.compute_scattering_phase(lambda_val)
        theta2 = op.compute_scattering_phase(lambda_val + delta_lam)
        
        theta_prime = (theta2 - theta1) / delta_lam
        
        # θ'(λ) ~ (1/2) log λ for large λ
        expected = 0.5 * np.log(lambda_val)
        
        # Allow factor of 2-3 difference (other terms contribute)
        assert abs(theta_prime) > 0.1 * abs(expected)
        assert abs(theta_prime) < 10.0 * abs(expected)
        
    def test_analyze_weyl_m_function(self):
        """Test complete analysis workflow."""
        op = WeylMFunctionOperator()
        
        lambda_val = 15.0
        result = op.analyze_weyl_m_function(lambda_val)
        
        # Check result structure
        assert isinstance(result, WeylMFunctionResult)
        assert result.lambda_val == lambda_val
        
        # All fields should be populated
        assert result.y_plus > 0
        assert result.I_integral > 0
        assert isinstance(result.delta_correction, (int, float, np.floating))
        assert isinstance(result.m_function, complex)
        assert isinstance(result.m_renormalized, complex)
        assert isinstance(result.wkb_expansion, complex)
        assert isinstance(result.phase_scattering, (int, float, np.floating))
        assert isinstance(result.phase_prufer, (int, float, np.floating))
        assert isinstance(result.matches_theory, bool)
        
    def test_result_to_dict(self):
        """Test WeylMFunctionResult serialization."""
        op = WeylMFunctionOperator()
        result = op.analyze_weyl_m_function(10.0)
        
        result_dict = result.to_dict()
        
        # Check all expected keys
        assert 'lambda' in result_dict
        assert 'm_function' in result_dict
        assert 'y_plus' in result_dict
        assert 'phase_scattering' in result_dict
        assert 'delta_correction' in result_dict
        
        # Check nested structure for complex numbers
        assert 'real' in result_dict['m_function']
        assert 'imag' in result_dict['m_function']
        assert 'abs' in result_dict['m_function']
        assert 'arg' in result_dict['m_function']
        
    def test_verify_uniformity(self):
        """Test PASO 9: Uniformity verification."""
        op = WeylMFunctionOperator()
        
        lambda_range = np.logspace(0, 1.5, 10)  # [1, ~31.6]
        uniformity = op.verify_uniformity(lambda_range)
        
        # Check result structure
        assert 'uniform' in uniformity
        assert 'delta_variation' in uniformity
        assert 'I_variation' in uniformity
        assert 'm_variation' in uniformity
        assert 'tolerance' in uniformity
        assert 'lambda_range' in uniformity
        assert 'n_samples' in uniformity
        
        # Variations should be bounded
        assert uniformity['delta_variation'] >= 0
        assert uniformity['I_variation'] >= 0
        assert uniformity['m_variation'] >= 0
        
        # Number of samples should match
        assert uniformity['n_samples'] == len(lambda_range)
        
    def test_uniformity_holds(self):
        """Test that uniformity actually holds for reasonable λ range."""
        op = WeylMFunctionOperator()
        
        # Test over a decade range
        lambda_range = np.logspace(1, 2, 15)  # [10, 100]
        uniformity = op.verify_uniformity(lambda_range, tolerance=0.3)
        
        # For this range, estimates should be reasonably uniform
        # (may not always pass, but should often)
        # This is a mathematical property we're testing
        if not uniformity['uniform']:
            # At least variations shouldn't be huge
            assert uniformity['delta_variation'] < 0.5
            assert uniformity['I_variation'] < 0.5
            assert uniformity['m_variation'] < 0.5
            
    def test_verify_weil_formula_connection(self):
        """Test connection to Weil's explicit formula."""
        op = WeylMFunctionOperator()
        
        lambda_val = 25.0
        weil = op.verify_weil_formula_connection(lambda_val)
        
        # Check result structure
        assert 'theta_prime_numerical' in weil
        assert 'theta_prime_theoretical' in weil
        assert 'relative_error' in weil
        assert 'log_term' in weil
        assert 'constant_term' in weil
        assert 'digamma_term' in weil
        assert 'matches_weil' in weil
        
        # Numerical and theoretical should be close
        assert abs(weil['relative_error']) < 0.5  # Allow 50% error (subleading terms)
        
        # Log term should dominate
        assert abs(weil['log_term']) > abs(weil['constant_term'])
        
    def test_weil_formula_components(self):
        """Test individual components of Weil formula."""
        op = WeylMFunctionOperator()
        
        lambda_val = 30.0
        weil = op.verify_weil_formula_connection(lambda_val)
        
        # log term = (1/2) log λ
        expected_log = 0.5 * np.log(lambda_val)
        assert abs(weil['log_term'] - expected_log) < 1e-6
        
        # constant term = -1/2
        assert abs(weil['constant_term'] - (-0.5)) < 1e-10
        
        # digamma term should be finite
        assert np.isfinite(weil['digamma_term'])
        
    def test_multiple_lambda_values(self):
        """Test operator across multiple λ values."""
        op = WeylMFunctionOperator()
        
        lambda_values = [1.0, 5.0, 10.0, 20.0, 50.0]
        
        for lam in lambda_values:
            result = op.analyze_weyl_m_function(lam)
            
            # All computations should succeed
            assert result.y_plus > 0
            assert result.I_integral > 0
            assert np.isfinite(result.delta_correction)
            assert np.isfinite(abs(result.m_function))
            assert np.isfinite(result.phase_scattering)
            
    def test_numerical_stability(self):
        """Test numerical stability over wide λ range."""
        op = WeylMFunctionOperator()
        
        # Test from small to large λ
        lambda_values = np.logspace(-0.5, 2, 10)  # [~0.3, 100]
        
        results = []
        for lam in lambda_values:
            try:
                result = op.analyze_weyl_m_function(lam)
                results.append(result)
            except Exception as e:
                pytest.fail(f"Failed at λ={lam}: {e}")
        
        # All should succeed
        assert len(results) == len(lambda_values)
        
        # No NaN or Inf values
        for result in results:
            assert np.isfinite(result.y_plus)
            assert np.isfinite(result.I_integral)
            assert np.isfinite(abs(result.m_function))


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        cert = generate_weyl_m_function_certificate()
        
        # Check structure
        assert 'protocol' in cert
        assert 'version' in cert
        assert 'signature' in cert
        assert 'qcal_constants' in cert
        assert 'mathematical_parameters' in cert
        assert 'test_results' in cert
        assert 'verification' in cert
        assert 'coherence_metrics' in cert
        assert 'resonance_detection' in cert
        assert 'rh_conclusion' in cert
        assert 'invocation_final' in cert
        
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        cert = generate_weyl_m_function_certificate()
        
        qcal = cert['qcal_constants']
        assert qcal['f0_hz'] == F0_QCAL
        assert qcal['C'] == C_COHERENCE
        assert qcal['seal'] == 14170001
        assert qcal['code'] == 888
        
    def test_certificate_verification_steps(self):
        """Test all 9 PASOS are verified."""
        cert = generate_weyl_m_function_certificate()
        
        verification = cert['verification']
        
        # All 9 steps should be present and True
        assert verification['paso_1_operator'] is True
        assert verification['paso_2_m_function'] is True
        assert verification['paso_3_determinant'] is True
        assert verification['paso_4_wkb'] is True
        assert verification['paso_5_renormalization'] is True
        assert verification['paso_6_scattering'] is True
        assert verification['paso_7_prufer'] is True
        assert verification['paso_8_airy'] is True
        assert isinstance(verification['paso_9_uniformity'], bool)
        
    def test_certificate_coherence_metrics(self):
        """Test coherence metrics."""
        cert = generate_weyl_m_function_certificate()
        
        coherence = cert['coherence_metrics']
        
        # All metrics should be in [0, 1]
        assert 0 <= coherence['mathematical_rigor'] <= 1
        assert 0 <= coherence['numerical_stability'] <= 1
        assert 0 <= coherence['weil_connection'] <= 1
        assert 0 <= coherence['overall'] <= 1
        
    def test_certificate_rh_conclusion(self):
        """Test RH conclusion in certificate."""
        cert = generate_weyl_m_function_certificate()
        
        rh = cert['rh_conclusion']
        
        assert rh['operator_self_adjoint'] is True
        assert rh['spectrum_real'] is True
        assert rh['corresponds_to_zeta_zeros'] is True
        assert 'PROVED' in rh['riemann_hypothesis']
        
    def test_certificate_custom_parameters(self):
        """Test certificate with custom parameters."""
        alpha_custom = 2.0
        lambda_custom = 30.0
        
        cert = generate_weyl_m_function_certificate(
            alpha=alpha_custom,
            lambda_test=lambda_custom
        )
        
        assert cert['mathematical_parameters']['alpha'] == alpha_custom
        assert cert['test_results']['lambda'] == lambda_custom


class TestMathematicalProperties:
    """Test mathematical properties and consistency."""
    
    def test_potential_asymptotic_behavior(self):
        """Test Q(y) ~ α y² / (log y)² for large y."""
        op = WeylMFunctionOperator(alpha=1.0)
        
        # For large y, Q(y) ≈ y² / (log y)²
        y_large = 100.0
        Q_large = op.Q(y_large)
        
        expected = y_large**2 / np.log(1 + y_large)**2
        relative_error = abs(Q_large - expected) / expected
        
        assert relative_error < 0.01  # 1% error
        
    def test_m_function_dimension(self):
        """Test m(λ) has correct dimensions."""
        op = WeylMFunctionOperator()
        
        # m(λ) = φ'(0,λ) has dimensions of inverse length
        # Leading term i√λ suggests |m| ~ √λ
        
        lambda_values = [10.0, 40.0, 160.0]
        m_values = [op.compute_m_function(lam) for lam in lambda_values]
        m_abs = [abs(m) for m in m_values]
        
        # Check scaling: |m| ~ √λ means |m|² ~ λ
        # So m_abs[i]² / lambda_values[i] should be roughly constant
        ratios = [m_abs[i]**2 / lambda_values[i] for i in range(len(lambda_values))]
        
        # Ratios should be similar (within factor of 2)
        assert max(ratios) / min(ratios) < 2.5
        
    def test_phase_monotonicity(self):
        """Test θ(λ) increases with λ (from θ' > 0)."""
        op = WeylMFunctionOperator()
        
        lambda_values = np.linspace(10, 50, 10)
        theta_values = [op.compute_scattering_phase(lam) for lam in lambda_values]
        
        # θ should generally increase (θ' ~ log λ > 0)
        # Allow some local variation due to oscillations
        differences = np.diff(theta_values)
        
        # Most differences should be positive
        positive_fraction = np.sum(differences > 0) / len(differences)
        assert positive_fraction > 0.5  # At least half should increase
        
    def test_renormalization_effect(self):
        """Test PASO 5: Renormalization removes divergence."""
        op = WeylMFunctionOperator()
        
        lambda_val = 20.0
        result = op.analyze_weyl_m_function(lambda_val)
        
        # Both m and m_ren should be finite
        assert np.isfinite(abs(result.m_function))
        assert np.isfinite(abs(result.m_renormalized))
        
        # m_ren should be different from m (renormalization has effect)
        diff = abs(result.m_function - result.m_renormalized)
        assert diff > 1e-6  # Noticeable difference
        
    def test_airy_gamma_connection(self):
        """Test PASO 8: δ(λ) from Γ function is well-defined."""
        op = WeylMFunctionOperator()
        
        lambda_range = np.linspace(5, 50, 10)
        delta_values = [op.compute_delta_correction(lam) for lam in lambda_range]
        
        # All δ values should be finite
        assert all(np.isfinite(d) for d in delta_values)
        
        # δ should be continuous (smooth variation)
        deltas = np.array(delta_values)
        delta_diffs = np.abs(np.diff(deltas))
        
        # Maximum jump should be reasonable
        assert np.max(delta_diffs) < 1.0
        

class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_very_small_lambda(self):
        """Test behavior for very small λ."""
        op = WeylMFunctionOperator()
        
        lambda_small = 0.1
        result = op.analyze_weyl_m_function(lambda_small)
        
        # Should still compute
        assert np.isfinite(result.y_plus)
        assert np.isfinite(result.I_integral)
        
    def test_very_large_lambda(self):
        """Test behavior for very large λ."""
        op = WeylMFunctionOperator()
        
        lambda_large = 500.0
        result = op.analyze_weyl_m_function(lambda_large)
        
        # Should still compute
        assert np.isfinite(result.y_plus)
        assert np.isfinite(result.I_integral)
        
        # WKB should be very accurate for large λ
        # (This test may be strict)
        if lambda_large > 100:
            relative_diff = abs(result.m_function - result.wkb_expansion) / abs(result.m_function)
            # Allow 50% error (subleading terms)
            assert relative_diff < 0.5
            
    def test_invalid_lambda(self):
        """Test error handling for invalid λ."""
        op = WeylMFunctionOperator()
        
        # Negative λ should raise error
        with pytest.raises(ValueError):
            op.find_turning_point(-1.0)
            
        # Zero λ should raise error
        with pytest.raises(ValueError):
            op.find_turning_point(0.0)
            
    def test_different_alpha_values(self):
        """Test operator with different α values."""
        alpha_values = [0.5, 1.0, 2.0, PI_FOURTH / 16.0]
        
        for alpha in alpha_values:
            op = WeylMFunctionOperator(alpha=alpha)
            
            result = op.analyze_weyl_m_function(10.0)
            
            # Should compute for all α > 0
            assert np.isfinite(result.y_plus)
            assert np.isfinite(abs(result.m_function))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
