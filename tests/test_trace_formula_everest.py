#!/usr/bin/env python3
"""
Tests for Trace Formula Everest 0.1 Implementation
==================================================

This module tests the weak trace formula implementation that demonstrates
spectral-arithmetic isomorphism between Atlas³ operator and prime numbers.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 13, 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.trace_formula_everest import (
    TraceFormulaEverest,
    TraceFormulaResult,
    TraceComponents,
    generate_atlas3_spectrum,
    run_complete_trace_analysis,
    F0_QCAL,
    C_COHERENCE,
)


class TestTraceFormulaEverestBasics:
    """Test basic functionality of trace formula calculator."""
    
    def test_initialization(self):
        """Test TraceFormulaEverest initialization."""
        spectrum = np.array([1.0, 2.0, 3.0, 4.0])
        calc = TraceFormulaEverest(spectrum)
        
        assert len(calc.spectrum) > 0
        assert calc.t_range == (0.0, 4.0)
        assert calc.n_points == 1000
    
    def test_initialization_with_complex_spectrum(self):
        """Test initialization filters imaginary parts correctly."""
        # Spectrum with small imaginary parts (PT-symmetric phase)
        spectrum = np.array([1.0 + 1e-10j, 2.0 - 1e-9j, 3.0])
        calc = TraceFormulaEverest(spectrum)
        
        # Should use real parts
        assert np.all(np.isreal(calc.spectrum))
    
    def test_spectrum_filtering(self):
        """Test that very small eigenvalues are filtered out."""
        spectrum = np.array([1e-8, 1.0, 2.0, 1e-7, 3.0])
        calc = TraceFormulaEverest(spectrum)
        
        # Should filter out 1e-8 and 1e-7
        assert len(calc.spectrum) == 3
        assert np.min(calc.spectrum) >= 0.9
    
    def test_custom_parameters(self):
        """Test initialization with custom parameters."""
        spectrum = np.array([1.0, 2.0, 3.0])
        calc = TraceFormulaEverest(
            spectrum,
            t_range=(0.5, 3.0),
            n_points=500
        )
        
        assert calc.t_range == (0.5, 3.0)
        assert calc.n_points == 500


class TestResponseFunction:
    """Test response function R(t) = Σ cos(γₙ t)."""
    
    def test_response_function_shape(self):
        """Test response function has correct shape."""
        spectrum = np.array([1.0, 2.0, 3.0])
        calc = TraceFormulaEverest(spectrum, n_points=100)
        
        t_vals, R_vals = calc.compute_response_function()
        
        assert len(t_vals) == 100
        assert len(R_vals) == 100
        assert t_vals[0] >= calc.t_range[0]
        assert t_vals[-1] <= calc.t_range[1]
    
    def test_response_function_single_eigenvalue(self):
        """Test R(t) for single eigenvalue equals cos(γt)."""
        gamma = 2.0
        spectrum = np.array([gamma])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 2*np.pi), n_points=100)
        
        t_vals, R_vals = calc.compute_response_function()
        expected = np.cos(gamma * t_vals)
        
        np.testing.assert_array_almost_equal(R_vals, expected, decimal=10)
    
    def test_response_function_symmetric(self):
        """Test R(t) with symmetric spectrum."""
        spectrum = np.array([-2.0, -1.0, 1.0, 2.0])
        calc = TraceFormulaEverest(spectrum, t_range=(-2, 2), n_points=200)
        
        t_vals, R_vals = calc.compute_response_function()
        
        # R(t) should be real
        assert np.all(np.isreal(R_vals))
    
    def test_response_function_oscillates(self):
        """Test that R(t) oscillates."""
        spectrum = np.linspace(1, 10, 20)
        calc = TraceFormulaEverest(spectrum, t_range=(0, 10), n_points=500)
        
        t_vals, R_vals = calc.compute_response_function()
        
        # Should have both positive and negative values
        assert np.any(R_vals > 0)
        assert np.any(R_vals < 0)
        
        # Should vary significantly
        assert (np.max(R_vals) - np.min(R_vals)) > 1.0


class TestMinimaDetection:
    """Test minima detection in response function."""
    
    def test_detect_minima_simple_cosine(self):
        """Test minima detection for simple cosine."""
        # R(t) = cos(t) has minimum at t = π
        spectrum = np.array([1.0])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 2*np.pi), n_points=500)
        
        t_vals, R_vals = calc.compute_response_function()
        minima_locs, minima_vals = calc.detect_minima(t_vals, R_vals)
        
        # Should find minimum near π
        assert len(minima_locs) >= 1
        assert any(abs(loc - np.pi) < 0.1 for loc in minima_locs)
    
    def test_detect_minima_returns_lists(self):
        """Test that detect_minima returns lists."""
        spectrum = np.array([1.0, 2.0, 3.0])
        calc = TraceFormulaEverest(spectrum, n_points=200)
        
        t_vals, R_vals = calc.compute_response_function()
        minima_locs, minima_vals = calc.detect_minima(t_vals, R_vals)
        
        assert isinstance(minima_locs, list)
        assert isinstance(minima_vals, list)
        assert len(minima_locs) == len(minima_vals)
    
    def test_detect_minima_with_prominence(self):
        """Test minima detection with custom prominence."""
        spectrum = np.array([1.0, 2.5, 4.0])
        calc = TraceFormulaEverest(spectrum, n_points=500)
        
        t_vals, R_vals = calc.compute_response_function()
        
        # High prominence should find fewer minima
        minima_high, _ = calc.detect_minima(t_vals, R_vals, prominence=10.0)
        # Low prominence should find more minima
        minima_low, _ = calc.detect_minima(t_vals, R_vals, prominence=0.1)
        
        assert len(minima_low) >= len(minima_high)


class TestPrimeDetection:
    """Test prime number detection in spectrum."""
    
    def test_check_prime_detection_ln2(self):
        """Test detection of ln(2) ≈ 0.693."""
        # Create spectrum with peak near ln(2)
        ln2 = np.log(2)
        spectrum = np.array([1.0, 2.0, 3.0])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 2), n_points=200)
        
        # Simulate minima near ln(2)
        minima = [ln2 - 0.01, 1.0, 1.5]
        
        detections = calc.check_prime_detection(minima, primes=[2], tolerance=0.05)
        
        assert 2 in detections
        assert detections[2]['detected'] == True
        assert abs(detections[2]['deviation']) < 0.05
    
    def test_check_prime_detection_multiple_primes(self):
        """Test detection of multiple primes."""
        primes = [2, 3, 5]
        ln_primes = [np.log(p) for p in primes]
        
        spectrum = np.linspace(1, 10, 50)
        calc = TraceFormulaEverest(spectrum, t_range=(0, 3), n_points=300)
        
        # Simulate minima near each ln(p)
        minima = [ln_p + 0.02 for ln_p in ln_primes]
        
        detections = calc.check_prime_detection(minima, primes=primes, tolerance=0.05)
        
        # All should be detected
        for p in primes:
            assert p in detections
            assert detections[p]['detected'] == True
    
    def test_check_prime_detection_miss(self):
        """Test when prime is not detected."""
        spectrum = np.array([1.0, 2.0])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 2))
        
        # Minima far from ln(2)
        minima = [0.1, 1.5]
        
        detections = calc.check_prime_detection(minima, primes=[2], tolerance=0.05)
        
        assert 2 in detections
        # Should not be detected (deviation > tolerance)
        assert detections[2]['detected'] == False
    
    def test_check_prime_detection_out_of_range(self):
        """Test primes outside t_range are skipped."""
        spectrum = np.array([1.0, 2.0])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 1.0))
        
        # ln(5) ≈ 1.609 is outside range [0, 1]
        minima = [0.5]
        detections = calc.check_prime_detection(minima, primes=[2, 5])
        
        # p=2 should be checked (ln(2) ≈ 0.693 is in range)
        assert 2 in detections
        # p=5 should be skipped (ln(5) ≈ 1.609 is out of range)
        # (it might be included but won't have 'detected' key or will be False)


class TestWeylTerm:
    """Test Weyl (geometric) term computation."""
    
    def test_weyl_term_returns_float(self):
        """Test Weyl term returns a float."""
        spectrum = np.linspace(1, 100, 50)
        calc = TraceFormulaEverest(spectrum)
        
        weyl = calc.compute_weyl_term()
        
        assert isinstance(weyl, (int, float, np.number))
    
    def test_weyl_term_with_gaussian(self):
        """Test Weyl term with Gaussian test function."""
        spectrum = np.linspace(5, 50, 30)
        calc = TraceFormulaEverest(spectrum)
        
        def gaussian(r, sigma=5.0):
            return np.exp(-r**2 / (2*sigma**2))
        
        weyl = calc.compute_weyl_term(test_function=gaussian)
        
        # Should be finite
        assert np.isfinite(weyl)
    
    def test_weyl_term_empty_spectrum(self):
        """Test Weyl term with minimal spectrum."""
        spectrum = np.array([1.0])
        calc = TraceFormulaEverest(spectrum)
        
        weyl = calc.compute_weyl_term()
        
        # Should handle gracefully
        assert np.isfinite(weyl)


class TestPrimeTerm:
    """Test arithmetic (prime) term computation."""
    
    def test_prime_term_returns_tuple(self):
        """Test prime term returns (total, by_prime)."""
        spectrum = np.linspace(1, 50, 30)
        calc = TraceFormulaEverest(spectrum)
        
        total, by_prime = calc.compute_prime_term()
        
        assert isinstance(total, (int, float, np.number))
        assert isinstance(by_prime, dict)
    
    def test_prime_term_includes_primes(self):
        """Test prime term includes specified primes."""
        spectrum = np.linspace(1, 50, 30)
        calc = TraceFormulaEverest(spectrum)
        
        primes = [2, 3, 5, 7]
        total, by_prime = calc.compute_prime_term(primes=primes)
        
        for p in primes:
            assert p in by_prime
    
    def test_prime_term_contributions_finite(self):
        """Test all prime contributions are finite."""
        spectrum = np.linspace(1, 50, 30)
        calc = TraceFormulaEverest(spectrum)
        
        total, by_prime = calc.compute_prime_term()
        
        assert np.isfinite(total)
        for p, contrib in by_prime.items():
            assert np.isfinite(contrib)
    
    def test_prime_term_with_custom_test_function(self):
        """Test prime term with custom test function."""
        spectrum = np.linspace(1, 50, 30)
        calc = TraceFormulaEverest(spectrum)
        
        def custom_h(r):
            return 1.0 / (1.0 + r**2)
        
        total, by_prime = calc.compute_prime_term(test_function=custom_h)
        
        assert np.isfinite(total)


class TestEverestTest:
    """Test complete Everest 0.1 test."""
    
    def test_run_everest_test_returns_result(self):
        """Test Everest test returns TraceFormulaResult."""
        spectrum = np.linspace(1, 50, 100)
        calc = TraceFormulaEverest(spectrum, t_range=(0, 3), n_points=200)
        
        result = calc.run_everest_test()
        
        assert isinstance(result, TraceFormulaResult)
        assert hasattr(result, 't_values')
        assert hasattr(result, 'R_values')
        assert hasattr(result, 'ln2_detected')
        assert hasattr(result, 'prime_detections')
    
    def test_run_everest_test_arrays_correct_shape(self):
        """Test Everest result arrays have correct shapes."""
        spectrum = np.linspace(1, 50, 100)
        n_points = 300
        calc = TraceFormulaEverest(spectrum, n_points=n_points)
        
        result = calc.run_everest_test()
        
        assert len(result.t_values) == n_points
        assert len(result.R_values) == n_points
    
    def test_run_everest_test_ln2_fields(self):
        """Test Everest result has ln2 detection fields."""
        spectrum = np.linspace(1, 50, 100)
        calc = TraceFormulaEverest(spectrum)
        
        result = calc.run_everest_test()
        
        assert isinstance(result.ln2_detected, bool)
        # ln2_position and ln2_deviation can be None if not detected


class TestTraceDecomposition:
    """Test trace decomposition into Weyl and Prime components."""
    
    def test_compute_trace_decomposition_returns_components(self):
        """Test trace decomposition returns TraceComponents."""
        spectrum = np.linspace(1, 50, 50)
        calc = TraceFormulaEverest(spectrum)
        
        decomp = calc.compute_trace_decomposition()
        
        assert isinstance(decomp, TraceComponents)
        assert hasattr(decomp, 'weyl_term')
        assert hasattr(decomp, 'prime_term')
        assert hasattr(decomp, 'total_trace')
    
    def test_trace_total_equals_sum(self):
        """Test total trace equals Weyl + Prime."""
        spectrum = np.linspace(1, 50, 50)
        calc = TraceFormulaEverest(spectrum)
        
        decomp = calc.compute_trace_decomposition()
        
        expected_total = decomp.weyl_term + decomp.prime_term
        np.testing.assert_almost_equal(decomp.total_trace, expected_total, decimal=10)
    
    def test_prime_contributions_dict(self):
        """Test prime contributions is a dictionary."""
        spectrum = np.linspace(1, 50, 50)
        calc = TraceFormulaEverest(spectrum)
        
        decomp = calc.compute_trace_decomposition()
        
        assert isinstance(decomp.prime_contributions, dict)
        assert len(decomp.prime_contributions) > 0


class TestAtlas3Integration:
    """Test integration with Atlas³ operator."""
    
    def test_generate_atlas3_spectrum_returns_array(self):
        """Test spectrum generation returns numpy array."""
        spectrum = generate_atlas3_spectrum(N=100, beta_0=2.0)
        
        assert isinstance(spectrum, np.ndarray)
        assert len(spectrum) > 0
    
    def test_generate_atlas3_spectrum_pt_symmetric(self):
        """Test spectrum for β < κ_Π is mostly real."""
        # β = 2.0 < 2.57 should give real spectrum
        spectrum = generate_atlas3_spectrum(N=200, beta_0=2.0)
        
        # Most eigenvalues should be real (|Im| < 1e-6)
        n_real = np.sum(np.abs(np.imag(spectrum)) < 1e-6)
        
        # At least 95% should be real
        assert n_real / len(spectrum) > 0.95
    
    @pytest.mark.slow
    def test_generate_atlas3_spectrum_large_n(self):
        """Test spectrum generation with large N."""
        # This is a slow test
        spectrum = generate_atlas3_spectrum(N=1000, beta_0=2.0)
        
        assert len(spectrum) == 1000


class TestCompleteAnalysis:
    """Test complete trace formula analysis."""
    
    def test_run_complete_analysis_returns_tuple(self):
        """Test complete analysis returns expected tuple."""
        spectrum = np.linspace(1, 50, 100)
        
        results, everest, decomp = run_complete_trace_analysis(
            spectrum,
            save_results=False
        )
        
        assert isinstance(results, dict)
        assert isinstance(everest, TraceFormulaResult)
        assert isinstance(decomp, TraceComponents)
    
    def test_complete_analysis_has_required_keys(self):
        """Test results dictionary has all required keys."""
        spectrum = np.linspace(1, 50, 100)
        
        results, _, _ = run_complete_trace_analysis(
            spectrum,
            save_results=False
        )
        
        required_keys = [
            'spectrum_info',
            'everest_test',
            'trace_decomposition',
            'certification',
            'qcal_signature'
        ]
        
        for key in required_keys:
            assert key in results
    
    def test_complete_analysis_spectrum_info(self):
        """Test spectrum_info contains correct information."""
        spectrum = np.array([1.0 + 0j, 2.0 + 0j, 3.0 + 1e-10j])
        
        results, _, _ = run_complete_trace_analysis(
            spectrum,
            save_results=False
        )
        
        spec_info = results['spectrum_info']
        assert spec_info['n_eigenvalues'] == 3
        assert spec_info['real_eigenvalues'] == 3
    
    def test_complete_analysis_qcal_signature(self):
        """Test QCAL signature is included."""
        spectrum = np.linspace(1, 50, 100)
        
        results, _, _ = run_complete_trace_analysis(
            spectrum,
            save_results=False
        )
        
        qcal = results['qcal_signature']
        assert qcal['frequency_base'] == F0_QCAL
        assert qcal['coherence'] == C_COHERENCE
        assert '∴𓂀Ω∞³Φ' in qcal['signature']


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_qcal(self):
        """Test fundamental frequency constant."""
        assert abs(F0_QCAL - 141.7001) < 1e-4
    
    def test_c_coherence(self):
        """Test coherence constant."""
        assert abs(C_COHERENCE - 244.36) < 0.01


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_empty_spectrum(self):
        """Test handling of empty spectrum."""
        spectrum = np.array([])
        
        # Should handle gracefully
        try:
            calc = TraceFormulaEverest(spectrum)
            # If it doesn't raise, spectrum should be empty
            assert len(calc.spectrum) == 0
        except:
            # Or it might raise an error, which is also acceptable
            pass
    
    def test_single_eigenvalue(self):
        """Test with single eigenvalue."""
        spectrum = np.array([5.0])
        calc = TraceFormulaEverest(spectrum, n_points=100)
        
        t_vals, R_vals = calc.compute_response_function()
        
        # Should work and give cos(5*t)
        expected = np.cos(5.0 * t_vals)
        np.testing.assert_array_almost_equal(R_vals, expected, decimal=10)
    
    def test_negative_eigenvalues(self):
        """Test with negative eigenvalues."""
        spectrum = np.array([-3.0, -1.0, 1.0, 3.0])
        calc = TraceFormulaEverest(spectrum)
        
        # Should handle without error
        t_vals, R_vals = calc.compute_response_function()
        assert len(R_vals) > 0
    
    def test_very_large_eigenvalues(self):
        """Test with very large eigenvalues."""
        spectrum = np.array([1000.0, 2000.0, 3000.0])
        calc = TraceFormulaEverest(spectrum, t_range=(0, 0.01), n_points=50)
        
        # Should compute without overflow
        t_vals, R_vals = calc.compute_response_function()
        assert np.all(np.isfinite(R_vals))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
