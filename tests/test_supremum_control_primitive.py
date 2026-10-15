#!/usr/bin/env python3
"""
Pytest Tests for Supremum Control of Primitive W(x)
====================================================

Comprehensive test suite for the supremum control demonstration
of the oscillatory potential primitive.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from supremum_control_primitive import (
    compute_primitive_W,
    estimate_supremum_bound,
    compute_quadratic_mean,
    verify_relative_form_boundedness,
    generate_certificate,
    _sieve_primes,
)


class TestPrimitiveComputation:
    """Tests for primitive W(x) computation."""
    
    def test_primitive_zero_at_zero(self):
        """Test W(0) = 0 with zero phases."""
        primes = _sieve_primes(50)
        x = np.array([0.0])
        W = compute_primitive_W(x, primes, p_max=50)
        
        assert np.abs(W[0]) < 1e-10, "W(0) should be ~ 0 with zero phases"
    
    def test_primitive_is_continuous(self):
        """Test W(x) continuity."""
        primes = _sieve_primes(50)
        x = np.linspace(0.1, 10.0, 100)
        W = compute_primitive_W(x, primes, p_max=50)
        
        # Check no NaN or Inf
        assert np.all(np.isfinite(W)), "W(x) must be finite everywhere"
        
        # Check smoothness: large jumps indicate discontinuity
        dW = np.diff(W)
        dx = np.diff(x)
        dW_dx = dW / dx
        
        # Derivative should be bounded
        assert np.max(np.abs(dW_dx)) < 100.0, "W(x) derivative should be bounded"
    
    def test_primitive_oscillatory_behavior(self):
        """Test W(x) has oscillatory character."""
        primes = _sieve_primes(50)
        x = np.linspace(0.1, 20.0, 200)
        W = compute_primitive_W(x, primes, p_max=50)
        
        # Count zero crossings (sign changes)
        sign_changes = np.sum(np.diff(np.sign(W)) != 0)
        
        # Should have multiple oscillations
        assert sign_changes > 5, "W(x) should oscillate"
    
    def test_primitive_with_phases(self):
        """Test W(x) with non-zero phases."""
        primes = _sieve_primes(50)
        phases = np.random.uniform(0, 2*np.pi, len(primes))
        
        x = np.linspace(0.1, 10.0, 100)
        W = compute_primitive_W(x, primes, phases=phases, p_max=50)
        
        assert np.all(np.isfinite(W)), "W(x) with phases must be finite"


class TestSupremumBound:
    """Tests for supremum bound estimation."""
    
    def test_supremum_is_finite(self):
        """Test sup_x |W(x)|²/(1+x²) < ∞."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        
        assert np.isfinite(result.supremum_ratio), "Supremum must be finite"
        assert result.supremum_ratio > 0, "Supremum must be positive"
    
    def test_sub_quadratic_growth(self):
        """Test |W(x)|² = o(x²)."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        
        assert result.is_sub_quadratic, "Growth must be sub-quadratic"
        assert result.growth_exponent < 2.0, "Growth exponent must be < 2"
    
    def test_decay_at_large_x(self):
        """Test |W(x)|²/x² → 0 as x → ∞."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=1000.0,
            n_points=2000,
            p_max=50,
        )
        
        # Check ratio decays
        large_x_mask = result.x_values > 500.0
        ratios_large = result.W_squared[large_x_mask] / (result.x_values[large_x_mask] ** 2)
        
        small_x_mask = (result.x_values > 10.0) & (result.x_values < 100.0)
        ratios_small = result.W_squared[small_x_mask] / (result.x_values[small_x_mask] ** 2)
        
        if len(ratios_large) > 0 and len(ratios_small) > 0:
            max_large = np.max(ratios_large)
            max_small = np.max(ratios_small)
            
            # Ratio should decay
            assert max_large < max_small, "Ratio should decay at large x"
    
    def test_supremum_independence_of_grid(self):
        """Test supremum estimate is stable across different grids."""
        results = []
        for n_points in [500, 1000, 2000]:
            result = estimate_supremum_bound(
                x_min=0.1,
                x_max=500.0,
                n_points=n_points,
                p_max=50,
            )
            results.append(result.supremum_ratio)
        
        # All estimates should be similar (within 20%)
        mean_sup = np.mean(results)
        for sup_val in results:
            relative_error = np.abs(sup_val - mean_sup) / (mean_sup + 1e-10)
            assert relative_error < 0.2, "Supremum should be grid-independent"


class TestQuadraticMean:
    """Tests for quadratic mean computation."""
    
    def test_quadratic_mean_positive(self):
        """Test ∫₀^T |W(x)|² dx > 0."""
        result = compute_quadratic_mean(T=50.0, p_max=50, n_points=1000)
        
        assert result.quadratic_mean > 0, "Quadratic mean must be positive"
        assert np.isfinite(result.quadratic_mean), "Quadratic mean must be finite"
    
    def test_quadratic_mean_grows_with_T(self):
        """Test integral grows with T."""
        T_values = [10.0, 50.0, 100.0]
        integrals = []
        
        for T in T_values:
            result = compute_quadratic_mean(T=T, p_max=50, n_points=1000)
            integrals.append(result.quadratic_mean)
        
        # Integral should increase with T
        for i in range(len(integrals) - 1):
            assert integrals[i+1] > integrals[i], "Integral must grow with T"
    
    def test_montgomery_vaughan_asymptotic(self):
        """Test ∫|W|² ~ T log log T."""
        result = compute_quadratic_mean(T=100.0, p_max=100, n_points=2000)
        
        # Ratio should be order 1 (within factor of 5)
        assert 0.1 < result.ratio < 5.0, "Ratio to theory should be O(1)"


class TestKLMNConditions:
    """Tests for KLMN theorem conditions."""
    
    def test_relative_coefficient_less_than_one(self):
        """Test relative form bound coefficient a < 1."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        
        form_result = verify_relative_form_boundedness(result, epsilon=0.1)
        
        assert form_result['relative_coefficient_a'] < 1.0, "Must have a < 1"
        assert form_result['form_bound_satisfied'], "Form bound must be satisfied"
    
    def test_klmn_theorem_satisfied(self):
        """Test KLMN theorem conditions hold."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        
        form_result = verify_relative_form_boundedness(result)
        
        assert form_result['klmn_theorem_satisfied'], "KLMN must be satisfied"
        assert form_result['is_sub_quadratic'], "Sub-quadratic required for KLMN"


class TestCertificateGeneration:
    """Tests for certificate generation."""
    
    def test_certificate_structure(self):
        """Test certificate has required fields."""
        supremum_result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        qm_result = compute_quadratic_mean(T=50.0, p_max=50, n_points=1000)
        form_result = verify_relative_form_boundedness(supremum_result)
        
        cert = generate_certificate(supremum_result, qm_result, form_result)
        
        # Check required fields
        assert 'title' in cert
        assert 'author' in cert
        assert 'orcid' in cert
        assert 'doi' in cert
        assert 'supremum_bound' in cert
        assert 'quadratic_mean' in cert
        assert 'relative_form_boundedness' in cert
        assert 'essential_self_adjointness_proven' in cert
        assert 'conclusion' in cert
    
    def test_certificate_essential_self_adjointness(self):
        """Test certificate proves essential self-adjointness."""
        supremum_result = estimate_supremum_bound(
            x_min=0.1,
            x_max=500.0,
            n_points=1000,
            p_max=50,
        )
        qm_result = compute_quadratic_mean(T=50.0, p_max=50, n_points=1000)
        form_result = verify_relative_form_boundedness(supremum_result)
        
        cert = generate_certificate(supremum_result, qm_result, form_result)
        
        assert cert['essential_self_adjointness_proven'], (
            "Certificate must prove essential self-adjointness"
        )


class TestEdgeCases:
    """Tests for edge cases and boundary conditions."""
    
    def test_small_p_max(self):
        """Test with few primes."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=100.0,
            n_points=500,
            p_max=10,  # Only first 4 primes: 2, 3, 5, 7
        )
        
        assert np.isfinite(result.supremum_ratio), "Must work with few primes"
        assert result.is_sub_quadratic, "Should still be sub-quadratic"
    
    def test_large_x_range(self):
        """Test with large x values."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=10000.0,
            n_points=2000,
            p_max=50,
        )
        
        assert np.isfinite(result.supremum_ratio), "Must handle large x"
        assert result.is_sub_quadratic, "Should remain sub-quadratic"
    
    def test_near_origin_behavior(self):
        """Test behavior near x = 0."""
        primes = _sieve_primes(50)
        x_near_zero = np.array([0.001, 0.01, 0.1])
        
        W = compute_primitive_W(x_near_zero, primes, p_max=50)
        
        # Should be finite and bounded
        assert np.all(np.isfinite(W)), "Must be finite near origin"
        assert np.max(np.abs(W)) < 50.0, "Should be bounded near origin"


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_no_overflow(self):
        """Test no numerical overflow."""
        result = estimate_supremum_bound(
            x_min=0.1,
            x_max=1000.0,
            n_points=2000,
            p_max=100,
        )
        
        assert np.all(np.isfinite(result.W_values)), "No overflow in W"
        assert np.all(np.isfinite(result.W_squared)), "No overflow in W²"
    
    def test_consistent_random_phases(self):
        """Test consistency with random phases."""
        primes = _sieve_primes(50)
        
        # Two runs with same seed should give same result
        np.random.seed(42)
        phases1 = np.random.uniform(0, 2*np.pi, len(primes))
        x = np.linspace(0.1, 10.0, 100)
        W1 = compute_primitive_W(x, primes, phases=phases1, p_max=50)
        
        np.random.seed(42)
        phases2 = np.random.uniform(0, 2*np.pi, len(primes))
        W2 = compute_primitive_W(x, primes, phases=phases2, p_max=50)
        
        np.testing.assert_array_almost_equal(W1, W2, decimal=10)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
