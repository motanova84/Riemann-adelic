#!/usr/bin/env python3
"""
Tests for Logarithmic Potential Impossibility Theorem
======================================================

Test suite for the impossibility theorem demonstrating that
Q(y) = (π⁴/16) y²/[log(1+y)]² cannot match Riemann zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-LOGARITHMIC-IMPOSSIBILITY-TESTS v1.0
Date: February 16, 2026
"""

import sys
import pytest
import numpy as np
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.logarithmic_potential_impossibility import (
    LogarithmicPotentialImpossibility,
    ImpossibilityResult,
    generate_impossibility_certificate,
    PI, PI_SQUARED, PI_FOURTH
)


class TestLogarithmicPotentialImpossibility:
    """Test suite for logarithmic potential impossibility theorem."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.calculator = LogarithmicPotentialImpossibility()
        
    def test_initialization(self):
        """Test calculator initialization."""
        assert self.calculator.a == 2.0 / PI_SQUARED
        assert self.calculator.b == 4.0 / PI_SQUARED
        assert self.calculator.c == (4.0 / PI_SQUARED) * np.log(2.0 / PI_SQUARED)
        
    def test_potential_Q_positive(self):
        """Test potential Q(y) is positive for y > 0."""
        y_values = [0.1, 1.0, 10.0, 100.0]
        for y in y_values:
            Q_y = self.calculator.Q(y)
            assert Q_y > 0, f"Q({y}) should be positive"
            
    def test_potential_Q_grows(self):
        """Test potential Q(y) grows with y."""
        y1 = 10.0
        y2 = 100.0
        Q1 = self.calculator.Q(y1)
        Q2 = self.calculator.Q(y2)
        assert Q2 > Q1, "Q(y) should grow with y"
        
    def test_potential_Q_zero_at_origin(self):
        """Test Q(0) = 0."""
        assert self.calculator.Q(0.0) == 0.0
        assert self.calculator.Q(-1.0) == 0.0
        
    def test_y_plus_expansion_positive(self):
        """Test y₊(λ) expansion gives positive values."""
        lambda_values = [10.0, 100.0, 1000.0]
        for lam in lambda_values:
            y_plus = self.calculator.compute_y_plus_expansion(lam)
            assert y_plus > 0, f"y₊({lam}) should be positive"
            
    def test_y_plus_grows_with_lambda(self):
        """Test y₊ grows with λ."""
        lambda1 = 100.0
        lambda2 = 1000.0
        y1 = self.calculator.compute_y_plus_expansion(lambda1)
        y2 = self.calculator.compute_y_plus_expansion(lambda2)
        assert y2 > y1, "y₊ should grow with λ"
        
    def test_y_plus_expansion_requires_large_lambda(self):
        """Test that y₊ expansion requires λ > 1."""
        with pytest.raises(ValueError):
            self.calculator.compute_y_plus_expansion(0.5)
            
    def test_sqrt_lambda_y_plus_scaling(self):
        """Test √λ y₊ scales as λ log λ."""
        lambda_val = 1000.0
        sqrt_lambda_y_plus = self.calculator.compute_sqrt_lambda_y_plus(lambda_val)
        
        # Should be approximately λ × (a log λ + ...)
        log_lambda = np.log(lambda_val)
        expected_order = lambda_val * self.calculator.a * log_lambda
        
        # Check order of magnitude
        assert 0.5 * expected_order < sqrt_lambda_y_plus < 2.0 * expected_order
        
    def test_integral_Q_positive(self):
        """Test ∫Q is positive."""
        lambda_val = 1000.0
        y_plus = self.calculator.compute_y_plus_expansion(lambda_val)
        integral_Q = self.calculator.compute_integral_Q(lambda_val, y_plus)
        
        assert integral_Q > 0, "∫Q should be positive"
        
    def test_I_lambda_two_terms_consistent(self):
        """Test I(λ) from two-term expansion is consistent."""
        lambda_val = 1000.0
        I_lambda, sqrt_lambda_y_plus, integral_Q = self.calculator.compute_I_lambda_two_terms(lambda_val)
        
        # I(λ) should be positive
        assert I_lambda > 0
        
        # I(λ) should be less than √λ y₊ (the correction is subtracted)
        assert I_lambda < sqrt_lambda_y_plus
        
    def test_I_lambda_simplified_formula(self):
        """Test simplified I(λ) formula gives reasonable values."""
        lambda_val = 1000.0
        I_lambda = self.calculator.compute_I_lambda_simplified(lambda_val)
        
        # Should be positive
        assert I_lambda > 0
        
        # Should scale roughly as λ log λ
        log_lambda = np.log(lambda_val)
        expected_order = lambda_val * log_lambda
        assert 0.1 * expected_order < I_lambda < 2.0 * expected_order
        
    def test_I_lambda_consistency(self):
        """Test that two methods of computing I(λ) are consistent."""
        lambda_val = 1000.0
        
        I_two_terms, _, _ = self.calculator.compute_I_lambda_two_terms(lambda_val)
        I_simplified = self.calculator.compute_I_lambda_simplified(lambda_val)
        
        # Should be close (within 10%)
        relative_diff = abs(I_two_terms - I_simplified) / I_simplified
        assert relative_diff < 0.1, f"I(λ) methods differ by {relative_diff:.1%}"
        
    def test_counting_law_computation(self):
        """Test spectral counting law N(λ) computation."""
        lambda_val = 1000.0
        N_lambda, N_riemann = self.calculator.compute_counting_law(lambda_val)
        
        # Both should be positive
        assert N_lambda > 0
        assert N_riemann > 0
        
        # They should be different (that's the impossibility!)
        assert abs(N_lambda - N_riemann) > 0.01 * N_riemann
        
    def test_coefficient_extraction(self):
        """Test coefficient extraction from counting law."""
        lambda_val = 1000.0
        coeffs = self.calculator.extract_coefficients(lambda_val)
        
        # Our log λ coefficient
        expected_log_coef = 5.0 / (3.0 * PI**3)
        assert abs(coeffs['our_log_lambda_coef_simplified'] - expected_log_coef) < 1e-10
        
        # Our log log λ coefficient
        expected_log_log_coef = 10.0 / (3.0 * PI**3)
        assert abs(coeffs['our_log_log_lambda_coef_simplified'] - expected_log_log_coef) < 1e-10
        
        # Riemann coefficient
        expected_riemann_coef = 1.0 / (2.0 * PI)
        assert abs(coeffs['riemann_log_lambda_coef'] - expected_riemann_coef) < 1e-10
        
        # Riemann has no log log term
        assert coeffs['riemann_log_log_lambda_coef'] == 0.0
        
    def test_coefficients_mismatch(self):
        """Test that our coefficients don't match Riemann's."""
        lambda_val = 1000.0
        coeffs = self.calculator.extract_coefficients(lambda_val)
        
        # Leading coefficients should be different
        our_coef = coeffs['our_log_lambda_coef_simplified']
        riemann_coef = coeffs['riemann_log_lambda_coef']
        
        assert abs(our_coef - riemann_coef) > 0.01, "Coefficients should be significantly different"
        
        # We have a log log term, Riemann doesn't
        assert coeffs['our_log_log_lambda_coef_simplified'] > 0.01
        assert coeffs['riemann_log_log_lambda_coef'] == 0.0
        
    def test_prove_impossibility_returns_result(self):
        """Test that prove_impossibility returns proper result."""
        result = self.calculator.prove_impossibility(1000.0)
        
        assert isinstance(result, ImpossibilityResult)
        assert result.lambda_val == 1000.0
        assert result.y_plus > 0
        assert result.I_lambda > 0
        assert result.N_lambda > 0
        assert result.N_riemann > 0
        
    def test_prove_impossibility_mismatch(self):
        """Test that impossibility proof shows mismatch."""
        result = self.calculator.prove_impossibility(1000.0)
        
        # Coefficient mismatch should be significant
        assert result.mismatch_coefficient > 0.5, "Coefficient mismatch should be > 50%"
        
        # log log term should be present
        assert result.mismatch_log_log > 0.01
        
    def test_multiple_lambda_values(self):
        """Test consistency across multiple λ values."""
        lambda_values = [100.0, 500.0, 1000.0, 5000.0]
        results = []
        
        for lam in lambda_values:
            result = self.calculator.prove_impossibility(lam)
            results.append(result)
            
        # All should show mismatch
        for result in results:
            assert result.mismatch_coefficient > 0.5
            assert result.mismatch_log_log > 0.01
            
    def test_certificate_generation(self):
        """Test QCAL certificate generation."""
        cert = generate_impossibility_certificate(1000.0)
        
        # Check required fields
        assert cert['protocol'] == 'QCAL-LOGARITHMIC-IMPOSSIBILITY'
        assert cert['version'] == 'v1.0'
        assert cert['status'] == '✅ DEMOSTRADO'
        assert 'potential' in cert
        assert 'conclusion' in cert
        assert 'theorem_statement' in cert
        
        # Check QCAL signature
        assert cert['qcal_signature'] == '∴𓂀Ω∞³Φ'
        assert cert['frequency_base'] == 141.7001
        assert cert['coherence'] == 244.36
        
        # Check author info
        assert 'José Manuel Mota Burruezo' in cert['author']
        assert cert['orcid'] == '0009-0002-1923-0773'
        assert cert['institution'] == 'Instituto de Conciencia Cuántica (ICQ)'
        
    def test_certificate_numerical_values(self):
        """Test certificate contains correct numerical values."""
        cert = generate_impossibility_certificate(1000.0)
        
        # Check coefficients are present
        coeffs = cert['counting_law_coefficients']
        assert 'our_log_lambda' in coeffs
        assert 'our_log_log_lambda' in coeffs
        assert 'riemann_log_lambda' in coeffs
        assert 'riemann_log_log_lambda' in coeffs
        
        # Riemann has no log log term
        assert coeffs['riemann_log_log_lambda'] == 0.0
        
        # Our log log coefficient should be positive
        assert coeffs['our_log_log_lambda'] > 0.0
        
    def test_numerical_stability(self):
        """Test numerical stability for large λ."""
        lambda_val = 10000.0
        result = self.calculator.prove_impossibility(lambda_val)
        
        # All values should be finite
        assert np.isfinite(result.y_plus)
        assert np.isfinite(result.I_lambda)
        assert np.isfinite(result.N_lambda)
        assert np.isfinite(result.N_riemann)
        assert np.isfinite(result.mismatch_coefficient)
        
    def test_coefficient_formulas(self):
        """Test that coefficient formulas are correct."""
        # a = 2/π²
        expected_a = 2.0 / PI_SQUARED
        assert abs(self.calculator.a - expected_a) < 1e-10
        
        # b = 4/π²
        expected_b = 4.0 / PI_SQUARED
        assert abs(self.calculator.b - expected_b) < 1e-10
        
        # c = (4/π²) log(2/π²)
        expected_c = (4.0 / PI_SQUARED) * np.log(2.0 / PI_SQUARED)
        assert abs(self.calculator.c - expected_c) < 1e-10
        
    def test_impossibility_theorem_significance(self):
        """Test that the impossibility is mathematically significant."""
        result = self.calculator.prove_impossibility(1000.0)
        
        # The mismatch should be large enough to be physically meaningful
        # (> 50% error in leading coefficient is definitely significant!)
        assert result.mismatch_coefficient > 0.5
        
        # The presence of log log λ term is qualitatively different
        # (Riemann doesn't have it, ours does)
        assert result.mismatch_log_log > 0.05
        
    def test_asymptotic_behavior(self):
        """Test asymptotic behavior for increasing λ."""
        lambda_values = [100.0, 1000.0, 10000.0]
        ratios = []
        
        for lam in lambda_values:
            I_lambda = self.calculator.compute_I_lambda_simplified(lam)
            # Ratio I(λ) / (λ log λ)
            ratio = I_lambda / (lam * np.log(lam))
            ratios.append(ratio)
            
        # Ratios should be roughly constant (asymptotic behavior)
        mean_ratio = np.mean(ratios)
        std_ratio = np.std(ratios)
        
        # Standard deviation should be small compared to mean
        assert std_ratio / mean_ratio < 0.2


class TestImpossibilityTheorem:
    """High-level tests for the impossibility theorem."""
    
    def test_theorem_statement(self):
        """Test the main theorem statement is true."""
        calculator = LogarithmicPotentialImpossibility()
        result = calculator.prove_impossibility(1000.0)
        coeffs = calculator.extract_coefficients(1000.0)
        
        # Statement: Our counting law has coefficient 5/(3π³) for λ log λ
        our_coef = coeffs['our_log_lambda_coef_simplified']
        expected_coef = 5.0 / (3.0 * PI**3)
        assert abs(our_coef - expected_coef) < 1e-10
        
        # Statement: Riemann has coefficient 1/(2π) for λ log λ
        riemann_coef = coeffs['riemann_log_lambda_coef']
        expected_riemann = 1.0 / (2.0 * PI)
        assert abs(riemann_coef - expected_riemann) < 1e-10
        
        # Statement: They don't match
        assert abs(our_coef - riemann_coef) > 0.01
        
    def test_log_log_term_presence(self):
        """Test that log log λ term is present in our law but not Riemann's."""
        calculator = LogarithmicPotentialImpossibility()
        coeffs = calculator.extract_coefficients(1000.0)
        
        # We have it
        our_log_log = coeffs['our_log_log_lambda_coef_simplified']
        assert our_log_log > 0.05, "Our law should have significant log log term"
        
        # Riemann doesn't
        riemann_log_log = coeffs['riemann_log_log_lambda_coef']
        assert riemann_log_log == 0.0, "Riemann's law has no log log term"
        
    def test_impossibility_conclusion(self):
        """Test that the impossibility conclusion is justified."""
        calculator = LogarithmicPotentialImpossibility()
        result = calculator.prove_impossibility(1000.0)
        
        # The conclusion is: This potential cannot match Riemann zeros
        # Evidence: Large coefficient mismatch AND qualitative difference (log log term)
        
        assert result.mismatch_coefficient > 0.5, "Coefficient mismatch is substantial"
        assert result.mismatch_log_log > 0.05, "log log term is present and significant"
        
        # Combined, these prove impossibility
        # (different leading coefficient OR different functional form)


@pytest.mark.slow
class TestDetailedCalculations:
    """Detailed tests of individual calculation steps."""
    
    def test_paso_1_expansion(self):
        """Test PASO 1: y₊(λ) expansion."""
        calculator = LogarithmicPotentialImpossibility()
        lambda_val = 1000.0
        
        y_plus = calculator.compute_y_plus_expansion(lambda_val)
        
        # Should match the expansion formula
        sqrt_lambda = np.sqrt(lambda_val)
        log_lambda = np.log(lambda_val)
        log_log_lambda = np.log(log_lambda)
        
        expected = sqrt_lambda * (
            calculator.a * log_lambda + 
            calculator.b * log_log_lambda + 
            calculator.c
        )
        
        assert abs(y_plus - expected) < 1e-6
        
    def test_paso_2_sqrt_lambda_y_plus(self):
        """Test PASO 2: √λ y₊ calculation."""
        calculator = LogarithmicPotentialImpossibility()
        lambda_val = 1000.0
        
        sqrt_lambda_y_plus = calculator.compute_sqrt_lambda_y_plus(lambda_val)
        
        # Should be λ times the expansion factor
        log_lambda = np.log(lambda_val)
        log_log_lambda = np.log(log_lambda)
        A = calculator.a * log_lambda + calculator.b * log_log_lambda + calculator.c
        
        expected = lambda_val * A
        
        assert abs(sqrt_lambda_y_plus - expected) < 1e-6
        
    def test_paso_3_integral_Q(self):
        """Test PASO 3: ∫Q calculation."""
        calculator = LogarithmicPotentialImpossibility()
        lambda_val = 1000.0
        y_plus = calculator.compute_y_plus_expansion(lambda_val)
        
        integral_Q = calculator.compute_integral_Q(lambda_val, y_plus)
        
        # Should be positive and substantial
        assert integral_Q > 0
        
        # Should be roughly (λ/3) y₊ for large λ
        expected_order = (lambda_val / 3.0) * y_plus
        assert 0.5 * expected_order < integral_Q < 2.0 * expected_order


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
