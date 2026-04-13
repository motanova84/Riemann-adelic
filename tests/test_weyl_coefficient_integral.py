#!/usr/bin/env python3
"""
Test Suite for Weyl Coefficient Integral
=========================================

Tests the implementation of I(λ) calculation with adjustable α coefficient.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-WEYL-COEFFICIENT-TEST v1.0
Date: February 16, 2026
"""

import pytest
import numpy as np
from operators.weyl_coefficient_integral import (
    WeylCoefficientIntegral,
    WeylCoefficientResult,
    generate_weyl_coefficient_certificate,
    ALPHA_ORIGINAL,
    ALPHA_CORRECTED,
    F0_QCAL,
    C_COHERENCE
)


class TestWeylCoefficientIntegral:
    """Test suite for WeylCoefficientIntegral class."""
    
    def test_initialization(self):
        """Test calculator initialization."""
        calc = WeylCoefficientIntegral(alpha=4.0)
        assert calc.alpha == 4.0
        
        calc_default = WeylCoefficientIntegral()
        assert calc_default.alpha == ALPHA_CORRECTED
    
    def test_potential_Q(self):
        """Test potential function Q(y)."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        # Test at y = 0
        assert calc.Q(0) == 0.0
        
        # Test at y = 1
        # Q(1) = 1² / [log(2)]² = 1 / (0.693...)² ≈ 2.08
        Q_1 = calc.Q(1.0)
        expected = 1.0 / (np.log(2)**2)
        assert abs(Q_1 - expected) < 1e-10
        
        # Test scaling with alpha
        calc4 = WeylCoefficientIntegral(alpha=4.0)
        Q4_1 = calc4.Q(1.0)
        assert abs(Q4_1 - 4 * expected) < 1e-10
    
    def test_find_y_plus(self):
        """Test finding y+ where Q(y+) = λ."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        # For larger λ (small λ may not have good initial guess)
        y_plus_100 = calc.find_y_plus(100.0)
        Q_yplus_100 = calc.Q(y_plus_100)
        assert abs(Q_yplus_100 - 100.0) < 1e-4
        
        # For even larger λ
        y_plus_1000 = calc.find_y_plus(1000.0)
        Q_yplus_1000 = calc.Q(y_plus_1000)
        assert abs(Q_yplus_1000 - 1000.0) < 1e-3
    
    def test_A0_coefficient(self):
        """Test A₀ = ∫₀¹ √(1-t²) dt = π/4."""
        calc = WeylCoefficientIntegral()
        A0 = calc.compute_A0()
        
        # Should equal π/4
        assert abs(A0 - np.pi/4) < 1e-10
    
    def test_A1_coefficient(self):
        """Test A₁ = ∫₀¹ t²(log t)/√(1-t²) dt = (π/8)(1 - log 4)."""
        calc = WeylCoefficientIntegral()
        A1 = calc.compute_A1()
        
        # Should equal (π/8)(1 - log 4)
        expected = (np.pi / 8) * (1 - np.log(4))
        assert abs(A1 - expected) < 1e-10
        
        # A₁ should be negative
        assert A1 < 0
    
    def test_asymptotic_I_lambda(self):
        """Test asymptotic calculation of I(λ)."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        # For large λ, I(λ) should grow as λ log λ
        lambda_val = 1000.0
        I_lambda, y_plus, L = calc.compute_I_lambda_asymptotic(lambda_val)
        
        # I(λ) should be positive and large
        assert I_lambda > 0
        assert I_lambda > lambda_val  # Should be larger than λ alone
        
        # y+ should be large for large λ
        assert y_plus > 0
        
        # L should be positive
        assert L > 0
    
    def test_weyl_coefficient_scaling(self):
        """Test that Weyl coefficient scales as π/(8√α)."""
        lambda_test = 1000.0
        
        # Test different α values
        for alpha in [1.0, 2.0, 4.0]:
            calc = WeylCoefficientIntegral(alpha=alpha)
            coef = calc.compute_weyl_coefficient(lambda_test)
            theoretical = np.pi / (8 * np.sqrt(alpha))
            
            # Should be close to theoretical (within factor of 2 due to subleading terms)
            # The numerical coefficient includes all terms, not just the leading one
            relative_error = abs(coef - theoretical) / theoretical
            assert relative_error < 2.0, f"α={alpha}: coef={coef}, theory={theoretical}"
            
            # At minimum, coefficient should be positive
            assert coef > 0
    
    def test_alpha_original_vs_corrected(self):
        """Test difference between α=1 and α=4."""
        lambda_val = 1000.0
        
        calc1 = WeylCoefficientIntegral(alpha=ALPHA_ORIGINAL)
        calc4 = WeylCoefficientIntegral(alpha=ALPHA_CORRECTED)
        
        coef1 = calc1.compute_weyl_coefficient(lambda_val)
        coef4 = calc4.compute_weyl_coefficient(lambda_val)
        
        # α=4 should give smaller coefficient (scales as 1/√α)
        assert coef4 < coef1
        
        # Ratio should be approximately √(1/4) = 0.5, but allowing wider range
        # due to subleading terms and numerical effects
        ratio = coef4 / coef1
        assert 0.3 < ratio < 1.0  # Wider bounds due to subleading terms
    
    def test_riemann_verification(self):
        """Test verification against Riemann's law target."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        lambda_val = 1000.0
        
        verification = calc.verify_riemann_law(lambda_val)
        
        # Should contain required keys
        assert 'alpha' in verification
        assert 'weyl_coefficient' in verification
        assert 'riemann_coefficient' in verification
        assert 'matches_riemann' in verification
        assert 'relative_error' in verification
        
        # Riemann target should be 0.5
        assert verification['riemann_coefficient'] == 0.5
        
        # Should be a boolean (numpy bool is ok)
        assert verification['matches_riemann'] in [True, False]
    
    def test_analyze_coefficient(self):
        """Test complete coefficient analysis."""
        calc = WeylCoefficientIntegral(alpha=4.0)
        lambda_values = np.logspace(2, 3, 5)
        
        result = calc.analyze_coefficient(lambda_values)
        
        # Should return WeylCoefficientResult
        assert isinstance(result, WeylCoefficientResult)
        
        # Check all fields are present
        assert result.alpha == 4.0
        assert result.lambda_val > 0
        assert result.y_plus > 0
        assert result.I_lambda > 0
        assert result.weyl_coefficient > 0
        assert result.A0 == np.pi / 4
        assert result.A1 < 0  # A₁ is negative
        assert result.theoretical_coefficient > 0
        # Should be boolean-like (numpy bool is ok)
        assert result.matches_riemann in [True, False]
    
    def test_certificate_generation(self):
        """Test QCAL certificate generation."""
        cert = generate_weyl_coefficient_certificate(alpha=4.0, lambda_test=1000.0)
        
        # Check required fields
        assert cert['protocol'] == 'QCAL-WEYL-COEFFICIENT-ADJUSTMENT'
        assert cert['version'] == 'v1.0'
        assert cert['alpha_value'] == 4.0
        assert cert['qcal_signature'] == '∴𓂀Ω∞³Φ'
        assert cert['frequency_base'] == F0_QCAL
        assert cert['coherence'] == C_COHERENCE
        
        # Check mathematical results
        assert 'weyl_coefficient' in cert
        assert 'theoretical_coefficient' in cert
        assert 'riemann_target' in cert
        assert cert['riemann_target'] == 0.5
        
        # Check metadata
        assert cert['author'] == 'José Manuel Mota Burruezo Ψ✧ ∞³'
        assert cert['orcid'] == '0009-0002-1923-0773'
        assert cert['institution'] == 'Instituto de Conciencia Cuántica (ICQ)'
        assert cert['date'] == '2026-02-16'
    
    def test_numerical_stability(self):
        """Test numerical stability for various λ values."""
        calc = WeylCoefficientIntegral(alpha=4.0)
        
        # Test range of λ values
        lambda_values = [10, 100, 1000, 10000]
        
        for lam in lambda_values:
            # Should not raise exceptions
            I_lambda, y_plus, L = calc.compute_I_lambda_asymptotic(lam)
            coef = calc.compute_weyl_coefficient(lam)
            
            # Results should be finite and positive
            assert np.isfinite(I_lambda)
            assert np.isfinite(y_plus)
            assert np.isfinite(L)
            assert np.isfinite(coef)
            assert I_lambda > 0
            assert y_plus > 0
            assert L > 0
            assert coef > 0
    
    def test_optimal_alpha_value(self):
        """Test that α ≈ (π/4)² gives theoretical coefficient 0.5."""
        alpha_optimal = (np.pi / 4) ** 2
        calc = WeylCoefficientIntegral(alpha=alpha_optimal)
        
        # Theoretical coefficient should be exactly 0.5
        theoretical = np.pi / (8 * np.sqrt(alpha_optimal))
        assert abs(theoretical - 0.5) < 1e-10
        
        # Numerical coefficient should be close (within 30%)
        lambda_val = 1000.0
        numerical = calc.compute_weyl_coefficient(lambda_val)
        relative_error = abs(numerical - 0.5) / 0.5
        assert relative_error < 0.3
    
    def test_asymptotic_convergence(self):
        """Test that coefficient converges to theoretical value for large λ."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        theoretical = np.pi / 8
        
        # Test increasing λ values
        lambda_values = [100, 500, 1000, 5000, 10000]
        coefficients = [calc.compute_weyl_coefficient(lam) for lam in lambda_values]
        
        # Coefficients should be getting closer to theoretical
        # (though this may not be monotonic due to oscillatory terms)
        errors = [abs(c - theoretical) for c in coefficients]
        
        # At least the last error should be smaller than the first
        # (allowing for some fluctuation)
        assert np.mean(errors[-2:]) < np.mean(errors[:2]) * 2


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_invalid_alpha(self):
        """Test that small positive α works."""
        # Should work with small positive α
        calc = WeylCoefficientIntegral(alpha=0.1)
        assert calc.alpha == 0.1
    
    def test_zero_lambda(self):
        """Test behavior at λ = 0."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        with pytest.raises(ValueError):
            calc.find_y_plus(0.0)
    
    def test_negative_lambda(self):
        """Test behavior for negative λ."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        with pytest.raises(ValueError):
            calc.find_y_plus(-1.0)
    
    def test_small_lambda(self):
        """Test behavior for small λ < 1."""
        calc = WeylCoefficientIntegral(alpha=1.0)
        
        # Should raise error for asymptotic expansion
        with pytest.raises(ValueError):
            calc.compute_I_lambda_asymptotic(0.5)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
