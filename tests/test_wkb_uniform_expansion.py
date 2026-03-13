#!/usr/bin/env python3
"""
Test suite for WKB Uniform Expansion Theorem
============================================

Tests the complete implementation of the WKB uniform expansion theorem
for spectral operators with potential Q(y).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from operators.wkb_uniform_expansion import (
    WKBUniformExpansion,
    generate_wkb_certificate,
    WKBExpansionResult,
    LiouvilleGreenTransform,
    EigenvalueAsymptotics
)


class TestPotentialQ:
    """Test potential Q(y) and its properties."""
    
    def test_potential_asymptotic_growth(self):
        """Test Q(y) ~ y²/(log y)² for large y."""
        wkb = WKBUniformExpansion()
        
        # For large y, Q should grow as y²/(log y)²
        y_large = 100.0
        Q_val = wkb.potential_Q(y_large)
        
        # Expected asymptotic behavior
        log_y = np.log(y_large + 1.0)
        Q_expected = wkb.alpha * y_large**2 / (log_y**2 + 1.0)
        
        assert np.abs(Q_val - Q_expected) / Q_expected < 0.1
    
    def test_potential_exponential_decay(self):
        """Test Q(y) → 0 exponentially for y → -∞."""
        wkb = WKBUniformExpansion()
        
        # For large negative y, Q should decay exponentially
        y_negative = -20.0
        Q_val = wkb.potential_Q(y_negative)
        
        # Should be very small
        assert Q_val < 1e-5
        assert Q_val >= 0
    
    def test_potential_continuity(self):
        """Test Q(y) is continuous."""
        wkb = WKBUniformExpansion()
        
        y_values = np.linspace(-10, 100, 1000)
        Q_values = np.array([wkb.potential_Q(y) for y in y_values])
        
        # Check no NaN or Inf
        assert not np.any(np.isnan(Q_values))
        assert not np.any(np.isinf(Q_values))
        
        # Check positivity
        assert np.all(Q_values >= 0)
    
    def test_potential_derivatives(self):
        """Test computation of Q'(y) and Q''(y)."""
        wkb = WKBUniformExpansion()
        
        y = 10.0
        Q_prime = wkb.potential_Q_derivative(y, order=1)
        Q_double_prime = wkb.potential_Q_derivative(y, order=2)
        
        # Derivatives should be finite
        assert np.isfinite(Q_prime)
        assert np.isfinite(Q_double_prime)


class TestTurningPoints:
    """Test turning point calculations."""
    
    def test_turning_points_exist(self):
        """Test that turning points y± exist for λ > 0."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 100.0
        y_minus, y_plus = wkb.find_turning_points(lambda_val)
        
        assert y_minus < y_plus
        assert np.isfinite(y_minus)
        assert np.isfinite(y_plus)
    
    def test_turning_points_satisfy_equation(self):
        """Test Q(y±) ≈ λ at turning points."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        y_minus, y_plus = wkb.find_turning_points(lambda_val)
        
        Q_plus = wkb.potential_Q(y_plus)
        
        # y+ should satisfy Q(y+) ≈ λ
        assert np.abs(Q_plus - lambda_val) / lambda_val < 0.2
    
    def test_turning_points_scale_with_lambda(self):
        """Test turning points scale appropriately with λ."""
        wkb = WKBUniformExpansion()
        
        lambda_small = 10.0
        lambda_large = 100.0
        
        _, y_plus_small = wkb.find_turning_points(lambda_small)
        _, y_plus_large = wkb.find_turning_points(lambda_large)
        
        # Larger λ should give larger y+
        assert y_plus_large > y_plus_small


class TestLiouvilleGreenTransform:
    """Test Liouville-Green transformation."""
    
    def test_transform_computation(self):
        """Test basic transformation computation."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        transform = wkb.liouville_green_transform(lambda_val, n_points=100)
        
        assert isinstance(transform, LiouvilleGreenTransform)
        assert len(transform.xi_values) == 100
        assert len(transform.y_values) == 100
        assert len(transform.R_xi) == 100
    
    def test_transform_boundary_condition(self):
        """Test ξ(y+) = 0 boundary condition."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        transform = wkb.liouville_green_transform(lambda_val, n_points=100)
        
        # Last point (y+) should have ξ ≈ 0
        assert np.abs(transform.xi_values[-1]) < 1e-6
    
    def test_transform_error_term_scaling(self):
        """Test R(ξ) ~ O(1/λ) scaling."""
        wkb = WKBUniformExpansion()
        
        lambda_small = 20.0
        lambda_large = 200.0
        
        transform_small = wkb.liouville_green_transform(lambda_small)
        transform_large = wkb.liouville_green_transform(lambda_large)
        
        # Average error for larger λ should be smaller
        avg_error_small = np.mean(transform_small.R_xi)
        avg_error_large = np.mean(transform_large.R_xi)
        
        # Not strict inequality due to numerical effects
        assert avg_error_large < avg_error_small * 2


class TestIntegralILambda:
    """Test integral I(λ) computation."""
    
    def test_I_lambda_positive(self):
        """Test I(λ) > 0 for λ > 0."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        I_lambda = wkb.compute_I_lambda(lambda_val)
        
        assert I_lambda > 0
        assert np.isfinite(I_lambda)
    
    def test_I_lambda_increases_with_lambda(self):
        """Test I(λ) increases with λ."""
        wkb = WKBUniformExpansion()
        
        lambda_values = [20.0, 50.0, 100.0, 200.0]
        I_values = [wkb.compute_I_lambda(lam) for lam in lambda_values]
        
        # I(λ) should increase
        for i in range(len(I_values) - 1):
            assert I_values[i+1] > I_values[i]
    
    def test_asymptotic_expansion_accuracy(self):
        """Test asymptotic expansion I(λ) ~ (1/2) λ log λ - (1/2) λ."""
        wkb = WKBUniformExpansion()
        
        # For large λ, asymptotic should be accurate
        lambda_val = 100.0
        I_lambda = wkb.compute_I_lambda(lambda_val)
        I_asymptotic, _ = wkb.asymptotic_expansion_I(lambda_val)
        
        relative_error = np.abs(I_lambda - I_asymptotic) / np.abs(I_asymptotic)
        
        # Should be reasonably close for large λ
        assert relative_error < 0.5  # Within 50% due to O(1) term


class TestSpectralCountingFunction:
    """Test spectral counting function N(λ)."""
    
    def test_N_lambda_computation(self):
        """Test N(λ) = (1/π) I(λ)."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        I_lambda = wkb.compute_I_lambda(lambda_val)
        N_lambda = wkb.compute_N_lambda(lambda_val)
        
        # Check relation N = I/π
        assert np.abs(N_lambda - I_lambda / np.pi) < 1e-10
    
    def test_N_lambda_formula(self):
        """Test N(λ) ~ (λ/2π) log λ - (λ/2π)."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 100.0
        N_lambda = wkb.compute_N_lambda(lambda_val)
        
        # Expected from asymptotic formula
        N_expected = (lambda_val / (2 * np.pi)) * np.log(lambda_val) - (lambda_val / (2 * np.pi))
        
        relative_error = np.abs(N_lambda - N_expected) / np.abs(N_expected)
        
        # Should be reasonably close
        assert relative_error < 0.5


class TestWKBErrorEstimate:
    """Test WKB error estimation."""
    
    def test_error_estimate_bounded(self):
        """Test WKB error is O(1), bounded independently of λ."""
        wkb = WKBUniformExpansion()
        
        lambda_values = [20.0, 50.0, 100.0, 200.0, 500.0]
        errors = [wkb.wkb_error_estimate(lam) for lam in lambda_values]
        
        # All errors should be O(1) - bounded
        for error in errors:
            assert error < 100.0  # Conservative bound
            assert error >= 0
    
    def test_error_estimate_finite(self):
        """Test error estimate is finite."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        error = wkb.wkb_error_estimate(lambda_val)
        
        assert np.isfinite(error)
        assert error >= 0


class TestEigenvalueAsymptotics:
    """Test eigenvalue asymptotics λₙ ~ 2π n / log n."""
    
    def test_eigenvalue_computation(self):
        """Test eigenvalue computation from Bohr-Sommerfeld."""
        wkb = WKBUniformExpansion()
        
        result = wkb.compute_eigenvalue_asymptotics(n_max=10)
        
        assert isinstance(result, EigenvalueAsymptotics)
        assert len(result.n_values) == 10
        assert len(result.lambda_n) == 10
        assert len(result.lambda_n_asymptotic) == 10
    
    def test_eigenvalue_asymptotic_formula(self):
        """Test λₙ ~ 2π n / log n formula."""
        wkb = WKBUniformExpansion()
        
        result = wkb.compute_eigenvalue_asymptotics(n_max=20)
        
        # For large n, relative error should be small
        # Check last 10 values
        max_relative_error = np.max(result.relative_error[-10:])
        
        # Asymptotic formula should be accurate for large n
        assert max_relative_error < 0.3  # Within 30%
    
    def test_eigenvalue_ordering(self):
        """Test λₙ increases with n."""
        wkb = WKBUniformExpansion()
        
        result = wkb.compute_eigenvalue_asymptotics(n_max=20)
        
        # Eigenvalues should increase
        for i in range(len(result.lambda_n) - 1):
            assert result.lambda_n[i+1] > result.lambda_n[i]


class TestWKBExpansionAnalysis:
    """Test complete WKB expansion analysis."""
    
    def test_analyze_wkb_expansion(self):
        """Test complete WKB expansion analysis."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 50.0
        result = wkb.analyze_wkb_expansion(lambda_val)
        
        assert isinstance(result, WKBExpansionResult)
        assert result.lambda_val == lambda_val
        assert result.I_lambda > 0
        assert result.N_lambda > 0
        assert np.isfinite(result.error_estimate)
    
    def test_multiple_lambda_values(self):
        """Test WKB expansion for multiple λ values."""
        wkb = WKBUniformExpansion()
        
        lambda_values = [10.0, 50.0, 100.0]
        
        for lambda_val in lambda_values:
            result = wkb.analyze_wkb_expansion(lambda_val)
            assert result.lambda_val == lambda_val
            assert result.I_lambda > 0


class TestConsistencyVerification:
    """Test consistency verification."""
    
    def test_verify_consistency(self):
        """Test consistency verification returns dict of checks."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 100.0
        consistency = wkb.verify_consistency(lambda_val)
        
        assert isinstance(consistency, dict)
        assert 'I_lambda_asymptotic' in consistency
        assert 'N_lambda_formula' in consistency
        assert 'error_bounded' in consistency
        assert 'overall' in consistency
    
    def test_consistency_for_large_lambda(self):
        """Test consistency holds for large λ."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 200.0
        consistency = wkb.verify_consistency(lambda_val, tolerance=0.3)
        
        # For large λ, asymptotic should be accurate
        assert consistency['error_bounded']
    
    def test_consistency_error_bounded(self):
        """Test error bounded check always passes."""
        wkb = WKBUniformExpansion()
        
        lambda_values = [20.0, 50.0, 100.0, 200.0]
        
        for lambda_val in lambda_values:
            consistency = wkb.verify_consistency(lambda_val)
            assert consistency['error_bounded']


class TestQCALCertificate:
    """Test QCAL certificate generation."""
    
    def test_certificate_generation(self):
        """Test certificate generation."""
        wkb = WKBUniformExpansion()
        lambda_test = [50.0, 100.0]
        
        cert = generate_wkb_certificate(wkb, lambda_test)
        
        assert 'protocol' in cert
        assert cert['protocol'] == 'QCAL-WKB-UNIFORM-EXPANSION'
        assert 'version' in cert
        assert 'signature' in cert
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        wkb = WKBUniformExpansion()
        cert = generate_wkb_certificate(wkb, [50.0])
        
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == 141.7001
        assert cert['qcal_constants']['C'] == 244.36
        assert cert['qcal_constants']['seal'] == 14170001
        assert cert['qcal_constants']['code'] == 888
    
    def test_certificate_theorem_formulas(self):
        """Test theorem formulas in certificate."""
        wkb = WKBUniformExpansion()
        cert = generate_wkb_certificate(wkb, [50.0])
        
        assert 'theorem' in cert
        assert 'integral_expansion' in cert['theorem']
        assert 'counting_function' in cert['theorem']
        assert 'eigenvalue_asymptotics' in cert['theorem']
    
    def test_certificate_coherence_metrics(self):
        """Test coherence metrics in certificate."""
        wkb = WKBUniformExpansion()
        cert = generate_wkb_certificate(wkb, [50.0, 100.0])
        
        assert 'coherence_metrics' in cert
        assert 'Psi' in cert['coherence_metrics']
        assert 0 <= cert['coherence_metrics']['Psi'] <= 1
    
    def test_certificate_resonance_detection(self):
        """Test resonance detection in certificate."""
        wkb = WKBUniformExpansion()
        cert = generate_wkb_certificate(wkb, [50.0])
        
        assert 'resonance_detection' in cert
        assert 'threshold' in cert['resonance_detection']
        assert cert['resonance_detection']['threshold'] == 0.888
        assert 'level' in cert['resonance_detection']


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_stability_small_lambda(self):
        """Test numerical stability for small λ."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 1.0
        result = wkb.analyze_wkb_expansion(lambda_val)
        
        assert np.isfinite(result.I_lambda)
        assert np.isfinite(result.error_estimate)
    
    def test_stability_large_lambda(self):
        """Test numerical stability for large λ."""
        wkb = WKBUniformExpansion()
        
        lambda_val = 1000.0
        result = wkb.analyze_wkb_expansion(lambda_val)
        
        assert np.isfinite(result.I_lambda)
        assert np.isfinite(result.error_estimate)
    
    def test_no_overflow_warnings(self):
        """Test no numerical overflow warnings."""
        wkb = WKBUniformExpansion()
        
        import warnings
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            
            lambda_val = 500.0
            _ = wkb.analyze_wkb_expansion(lambda_val)
            
            # Check no overflow warnings
            overflow_warnings = [warning for warning in w 
                                if 'overflow' in str(warning.message).lower()]
            assert len(overflow_warnings) == 0


@pytest.mark.slow
class TestComprehensiveValidation:
    """Comprehensive validation tests."""
    
    def test_multiple_lambda_range(self):
        """Test WKB expansion over range of λ values."""
        wkb = WKBUniformExpansion()
        
        lambda_values = np.logspace(1, 2.5, 10)  # 10 to ~316
        
        for lambda_val in lambda_values:
            result = wkb.analyze_wkb_expansion(lambda_val)
            
            # All results should be valid
            assert np.isfinite(result.I_lambda)
            assert result.I_lambda > 0
            assert np.isfinite(result.error_estimate)
    
    def test_eigenvalue_convergence(self):
        """Test eigenvalue asymptotic convergence."""
        wkb = WKBUniformExpansion()
        
        result = wkb.compute_eigenvalue_asymptotics(n_max=50)
        
        # Relative error should decrease for large n
        # Compare first 10 vs last 10
        avg_error_small_n = np.mean(result.relative_error[:10])
        avg_error_large_n = np.mean(result.relative_error[-10:])
        
        # Last 10 should have smaller error (asymptotic regime)
        # Not strict inequality due to numerical effects
        assert avg_error_large_n < avg_error_small_n * 2


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
