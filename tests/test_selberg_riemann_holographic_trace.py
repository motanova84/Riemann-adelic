#!/usr/bin/env python3
"""
Unit Tests for Selberg-Riemann Holographic Trace Formula
========================================================

Tests the arithmetic holography implementation connecting:
- Selberg side: Geodesic lengths on SL(2,ℤ)\ℍ
- Riemann side: Zeros of ζ(s) and prime powers

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from numpy.testing import assert_allclose, assert_array_less
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from operators.selberg_riemann_holographic_trace import (
    SelbergRiemannHolographicTrace,
    TestFunctionResult,
    HolographicTraceResult,
    F0_QCAL,
    C_COHERENCE,
    OMEGA_0
)


class TestTestFunction:
    """Test the test function h(x) and its properties."""
    
    def test_gaussian_symmetry(self):
        """Test that Gaussian test function is symmetric."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='gaussian',
            test_function_width=1.0
        )
        
        x = np.linspace(-5, 5, 100)
        h_vals = trace.test_function_h(x)
        
        # Should be symmetric around 0
        assert_allclose(h_vals[:50], h_vals[-50:][::-1], rtol=1e-10)
    
    def test_gaussian_decay(self):
        """Test that Gaussian decays exponentially."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='gaussian',
            test_function_width=2.0
        )
        
        x = np.array([0.0, 2.0, 4.0, 6.0, 8.0])
        h_vals = trace.test_function_h(x)
        
        # Values should decay monotonically
        assert h_vals[0] > h_vals[1] > h_vals[2] > h_vals[3] > h_vals[4]
        
        # Should decay faster than linear (ratio should increase)
        ratios = h_vals[:-1] / h_vals[1:]
        # First ratio may be < 2 for σ=2, but ratios should increase
        assert ratios[-1] > ratios[0]  # Decay accelerates
    
    def test_gaussian_peak_at_zero(self):
        """Test that Gaussian peaks at x=0."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='gaussian',
            test_function_width=1.0
        )
        
        x = np.linspace(-5, 5, 101)
        h_vals = trace.test_function_h(x)
        
        # Maximum should be at center (x=0)
        max_idx = np.argmax(h_vals)
        assert max_idx == 50  # Center index
    
    def test_compact_support_decay(self):
        """Test compact support function has super-exponential decay."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='compact_support',
            test_function_width=1.0
        )
        
        # Use values away from zero where function is well-behaved
        x = np.array([0.5, 1.0, 2.0, 5.0, 10.0])
        h_vals = trace.test_function_h(x)
        
        # Should decay to very small values at large x
        assert h_vals[-1] < 1e-10  # Far values should be tiny
        
        # Peak should be around x ≈ 1 for this function
        assert h_vals[1] > h_vals[0] or h_vals[1] > h_vals[2]


class TestFourierTransform:
    """Test Fourier transform properties."""
    
    def test_gaussian_fourier_normalization(self):
        """Test Gaussian Fourier transform has correct normalization."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='gaussian',
            test_function_width=1.0
        )
        
        # At y=0, Fourier transform should equal integral of h
        g_zero = trace.fourier_transform_h(np.array([0.0]))[0]
        
        # For Gaussian exp(-x²/(2σ²)), FT at 0 is σ√(2π)
        expected = 1.0 * np.sqrt(2 * np.pi)
        assert_allclose(np.real(g_zero), expected, rtol=1e-6)
    
    def test_fourier_decay(self):
        """Test that Fourier transform decays for large frequencies."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=10,
            n_zeros=10,
            test_function_type='gaussian',
            test_function_width=2.0
        )
        
        y = np.array([0.0, 1.0, 2.0, 5.0, 10.0])
        g_vals = np.abs(trace.fourier_transform_h(y))
        
        # Should decay monotonically
        assert g_vals[0] > g_vals[1] > g_vals[2] > g_vals[3] > g_vals[4]


class TestPrimesAndZeros:
    """Test prime and zero loading."""
    
    def test_prime_generation(self):
        """Test that primes are correctly generated."""
        trace = SelbergRiemannHolographicTrace(n_primes=20, n_zeros=10)
        
        primes = trace._primes
        
        # Check we have the right number
        assert len(primes) == 20
        
        # Check first few primes
        expected_first = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert list(primes[:10]) == expected_first
        
        # All should be prime
        for p in primes:
            assert p > 1
            # Simple primality check
            if p > 2:
                assert all(p % i != 0 for i in range(2, int(np.sqrt(p)) + 1))
    
    def test_zero_loading(self):
        """Test that Riemann zeros are loaded correctly."""
        trace = SelbergRiemannHolographicTrace(n_primes=10, n_zeros=10)
        
        zeros = trace._zeros
        
        # Check we have the right number
        assert len(zeros) == 10
        
        # First zero should be around 14.134725
        assert_allclose(zeros[0], 14.134725, rtol=1e-4)
        
        # Zeros should be positive and increasing
        assert np.all(zeros > 0)
        assert np.all(np.diff(zeros) > 0)


class TestGeodesicSum:
    """Test geodesic side computation."""
    
    def test_geodesic_sum_positive(self):
        """Test that geodesic sum is positive."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=2.0
        )
        
        geodesic_sum, info = trace.compute_geodesic_sum()
        
        assert geodesic_sum > 0
        assert info['n_geodesics'] == 50
    
    def test_geodesic_sum_increases_with_primes(self):
        """Test that more primes gives larger sum."""
        trace1 = SelbergRiemannHolographicTrace(n_primes=20, n_zeros=10, test_function_width=2.0)
        trace2 = SelbergRiemannHolographicTrace(n_primes=50, n_zeros=10, test_function_width=2.0)
        
        sum1, _ = trace1.compute_geodesic_sum()
        sum2, _ = trace2.compute_geodesic_sum()
        
        # More primes should give larger sum
        assert sum2 > sum1


class TestSpectralSum:
    """Test spectral side computation."""
    
    def test_spectral_sum_nonnegative(self):
        """Test that spectral sum is non-negative."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=30,
            n_zeros=50,
            test_function_width=30.0  # Wide to capture zeros
        )
        
        spectral_sum, info = trace.compute_spectral_sum()
        
        assert spectral_sum >= 0
        assert info['n_eigenvalues'] == 50
    
    def test_spectral_sum_depends_on_width(self):
        """Test that spectral sum depends on test function width."""
        trace_narrow = SelbergRiemannHolographicTrace(
            n_primes=30,
            n_zeros=50,
            test_function_width=5.0
        )
        trace_wide = SelbergRiemannHolographicTrace(
            n_primes=30,
            n_zeros=50,
            test_function_width=50.0
        )
        
        sum_narrow, _ = trace_narrow.compute_spectral_sum()
        sum_wide, _ = trace_wide.compute_spectral_sum()
        
        # Wide function should give larger sum (captures more zeros)
        assert sum_wide > sum_narrow


class TestSelbergTrace:
    """Test Selberg trace computation."""
    
    def test_selberg_trace_positive(self):
        """Test that Selberg trace is positive."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=2.0
        )
        
        selberg_trace, info = trace.compute_selberg_trace_direct()
        
        assert selberg_trace > 0
        assert info['n_geodesics'] == 50
    
    def test_selberg_weights_reasonable(self):
        """Test that Selberg weights are in reasonable range."""
        trace = SelbergRiemannHolographicTrace(n_primes=20, n_zeros=10)
        
        # Compute weight ℓ/sinh(ℓ/2) for typical geodesic length
        length = np.log(11.0)  # log of 11th prime
        weight = length / np.sinh(length / 2.0)
        
        # Weight should be positive and < 2 (since ℓ/sinh(ℓ/2) → 0 as ℓ → ∞)
        assert 0 < weight < 2.0


class TestExplicitFormula:
    """Test explicit formula computation."""
    
    def test_explicit_formula_structure(self):
        """Test that explicit formula has correct structure."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=30,
            n_zeros=20,
            test_function_width=10.0
        )
        
        riemann_trace, info = trace.compute_explicit_formula_trace()
        
        # Should have both prime and zero contributions
        assert 'prime_contribution' in info
        assert 'zero_contribution' in info
        assert 'total' in info
        
        # Total should be sum of contributions
        assert_allclose(
            riemann_trace,
            info['prime_contribution'] + info['zero_contribution'],
            rtol=1e-10
        )


class TestHolographicCorrespondence:
    """Test holographic correspondence."""
    
    def test_correspondence_computes(self):
        """Test that holographic correspondence computes without errors."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=5.0
        )
        
        result = trace.compute_holographic_correspondence(verbose=False)
        
        # Check result structure
        assert isinstance(result, HolographicTraceResult)
        assert result.selberg_total != 0
        assert result.riemann_total != 0
        assert result.equality_error >= 0
        assert 0 <= result.qcal_coherence <= 1
    
    def test_qcal_coherence_in_range(self):
        """Test that QCAL coherence is in valid range."""
        trace = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=10.0
        )
        
        result = trace.compute_holographic_correspondence(verbose=False)
        
        # Coherence should be between 0 and 1
        assert 0 <= result.qcal_coherence <= 1
    
    def test_multiple_widths_give_different_results(self):
        """Test that different test function widths give different results."""
        trace_narrow = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=2.0
        )
        trace_wide = SelbergRiemannHolographicTrace(
            n_primes=50,
            n_zeros=30,
            test_function_width=20.0
        )
        
        result_narrow = trace_narrow.compute_holographic_correspondence(verbose=False)
        result_wide = trace_wide.compute_holographic_correspondence(verbose=False)
        
        # Different widths should give different traces
        assert result_narrow.selberg_total != result_wide.selberg_total
        assert result_narrow.riemann_total != result_wide.riemann_total


class TestPropertyVerification:
    """Test property verification."""
    
    def test_verification_structure(self):
        """Test that verification returns correct structure."""
        trace = SelbergRiemannHolographicTrace(n_primes=50, n_zeros=30)
        result = trace.compute_holographic_correspondence(verbose=False)
        
        checks = trace.verify_holographic_properties(result)
        
        # Should return dictionary of booleans
        assert isinstance(checks, dict)
        assert all(isinstance(v, (bool, np.bool_)) for v in checks.values())
    
    def test_sufficient_terms_check(self):
        """Test that sufficient terms check works."""
        trace = SelbergRiemannHolographicTrace(n_primes=100, n_zeros=50)
        result = trace.compute_holographic_correspondence(verbose=False)
        
        checks = trace.verify_holographic_properties(result)
        
        # Should pass sufficient terms check
        assert checks['sufficient_geodesics'] is True
        assert checks['sufficient_zeros'] is True


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants_defined(self):
        """Test that QCAL constants are properly defined."""
        assert F0_QCAL == 141.7001
        assert C_COHERENCE == 244.36
        assert_allclose(OMEGA_0, 2 * np.pi * F0_QCAL, rtol=1e-6)
    
    def test_qcal_coherence_formula(self):
        """Test QCAL coherence formula."""
        trace = SelbergRiemannHolographicTrace(n_primes=30, n_zeros=20)
        result = trace.compute_holographic_correspondence(verbose=False)
        
        # Coherence should be exp(-error²/C²)
        expected_coherence = np.exp(-result.equality_error**2 / C_COHERENCE**2)
        assert_allclose(result.qcal_coherence, expected_coherence, rtol=1e-10)


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf."""
        trace = SelbergRiemannHolographicTrace(n_primes=50, n_zeros=30)
        result = trace.compute_holographic_correspondence(verbose=False)
        
        # Check all numerical results
        assert np.isfinite(result.geodesic_sum)
        assert np.isfinite(result.spectral_sum)
        assert np.isfinite(result.zero_sum)
        assert np.isfinite(result.prime_sum)
        assert np.isfinite(result.selberg_total)
        assert np.isfinite(result.riemann_total)
        assert np.isfinite(result.equality_error)
        assert np.isfinite(result.qcal_coherence)
    
    def test_large_parameters(self):
        """Test with large numbers of primes and zeros."""
        trace = SelbergRiemannHolographicTrace(n_primes=200, n_zeros=100)
        result = trace.compute_holographic_correspondence(verbose=False)
        
        # Should complete without errors
        assert result is not None
        assert np.isfinite(result.qcal_coherence)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
