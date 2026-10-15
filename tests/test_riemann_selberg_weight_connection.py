#!/usr/bin/env python3
"""
Tests for Riemann-Selberg Weight Connection
===========================================

Comprehensive test suite for the mathematical connection between Riemann 
and Selberg weight functions.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
from numpy.testing import assert_allclose, assert_array_less
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from operators.riemann_selberg_weight_connection import (
    RiemannWeight,
    SelbergWeight,
    RiemannSelbergConnection,
    compare_riemann_selberg_weights,
    validate_weight_correspondence,
    generate_comparison_certificate
)


class TestRiemannWeight:
    """Tests for RiemannWeight class."""
    
    def test_initialization(self):
        """Test RiemannWeight initialization."""
        rw = RiemannWeight(precision=30)
        assert rw.precision == 30
    
    def test_weight_computation_basic(self):
        """Test basic weight computation for small primes."""
        rw = RiemannWeight()
        
        # p=2, k=1: W = log(2) / 2^(1/2) ≈ 0.693 / 1.414 ≈ 0.490
        w1 = rw.compute_weight(2, 1)
        assert 0.45 < w1 < 0.52
        
        # p=3, k=1: W = log(3) / 3^(1/2) ≈ 1.099 / 1.732 ≈ 0.635
        w2 = rw.compute_weight(3, 1)
        assert 0.6 < w2 < 0.7
    
    def test_weight_decreases_with_k(self):
        """Test that weight decreases exponentially with k."""
        rw = RiemannWeight()
        
        weights = [rw.compute_weight(5, k) for k in range(1, 6)]
        
        # Weights should decrease
        for i in range(len(weights) - 1):
            assert weights[i] > weights[i + 1]
        
        # Should decrease roughly by factor of sqrt(5) each time
        ratios = [weights[i] / weights[i+1] for i in range(len(weights) - 1)]
        expected_ratio = np.sqrt(5)
        assert_allclose(ratios, expected_ratio, rtol=0.01)
    
    def test_compute_sum(self):
        """Test sum computation over primes."""
        rw = RiemannWeight()
        
        total_sum, weight_list = rw.compute_sum(p_max=10, k_max=3)
        
        # Should have entries for primes 2, 3, 5, 7 with k=1,2,3
        assert len(weight_list) == 4 * 3  # 4 primes × 3 k values
        
        # Sum should be positive and finite
        assert total_sum > 0
        assert np.isfinite(total_sum)
        
        # Verify a few specific weights
        primes_in_list = [item[0] for item in weight_list]
        assert 2 in primes_in_list
        assert 7 in primes_in_list
    
    def test_is_prime(self):
        """Test prime checking function."""
        rw = RiemannWeight()
        
        # Known primes
        assert rw._is_prime(2)
        assert rw._is_prime(3)
        assert rw._is_prime(5)
        assert rw._is_prime(7)
        assert rw._is_prime(11)
        assert rw._is_prime(97)
        
        # Non-primes
        assert not rw._is_prime(1)
        assert not rw._is_prime(4)
        assert not rw._is_prime(6)
        assert not rw._is_prime(100)
    
    def test_primes_up_to(self):
        """Test prime generation."""
        rw = RiemannWeight()
        
        primes = rw._primes_up_to(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected
        
        primes_100 = rw._primes_up_to(100)
        assert len(primes_100) == 25  # There are 25 primes ≤ 100


class TestSelbergWeight:
    """Tests for SelbergWeight class."""
    
    def test_initialization(self):
        """Test SelbergWeight initialization."""
        sw = SelbergWeight(precision=30)
        assert sw.precision == 30
    
    def test_weight_computation_small_ell(self):
        """Test weight computation for small ℓ values."""
        sw = SelbergWeight()
        
        # ℓ=1, k=1: W = 1 / (2 sinh(0.5))
        w1 = sw.compute_weight(1.0, 1)
        sinh_half = np.sinh(0.5)
        expected1 = 1.0 / (2 * sinh_half)
        assert_allclose(w1, expected1, rtol=1e-10)
        
        # ℓ=2, k=1: W = 2 / (2 sinh(1))
        w2 = sw.compute_weight(2.0, 1)
        expected2 = 2.0 / (2 * np.sinh(1.0))
        assert_allclose(w2, expected2, rtol=1e-10)
    
    def test_asymptotic_computation(self):
        """Test asymptotic weight computation."""
        sw = SelbergWeight()
        
        # ℓ=3, k=1: W_asymp = 3 * e^(-1.5)
        w_asymp = sw.compute_asymptotic(3.0, 1)
        expected = 3.0 * np.exp(-1.5)
        assert_allclose(w_asymp, expected, rtol=1e-10)
    
    def test_asymptotic_convergence(self):
        """Test that asymptotic formula converges for large ℓ."""
        sw = SelbergWeight()
        
        ell_values = [1.0, 2.0, 3.0, 5.0, 10.0]
        
        for ell in ell_values:
            rel_error = sw.relative_error(ell, k=1)
            
            # Error should decrease with increasing ℓ
            if ell >= 3.0:
                assert rel_error < 0.1  # Within 10% for ℓ ≥ 3
    
    def test_convergence_regime(self):
        """Test convergence regime classification."""
        sw = SelbergWeight()
        
        # Small ℓ: non-asymptotic
        regime_small = sw.convergence_regime(0.5, 1, threshold=0.01)
        assert regime_small == "non-asymptotic"
        
        # Large ℓ: asymptotic
        regime_large = sw.convergence_regime(10.0, 1, threshold=0.01)
        assert regime_large == "asymptotic"
    
    def test_weight_decreases_with_k(self):
        """Test that Selberg weight decreases with k."""
        sw = SelbergWeight()
        
        ell = 2.0
        weights = [sw.compute_weight(ell, k) for k in range(1, 6)]
        
        # Weights should decrease
        for i in range(len(weights) - 1):
            assert weights[i] > weights[i + 1]
    
    def test_invalid_inputs(self):
        """Test error handling for invalid inputs."""
        sw = SelbergWeight()
        
        # Negative ℓ
        with pytest.raises(ValueError, match="ℓ must be positive"):
            sw.compute_weight(-1.0, 1)
        
        # Zero ℓ
        with pytest.raises(ValueError, match="ℓ must be positive"):
            sw.compute_weight(0.0, 1)
        
        # k < 1
        with pytest.raises(ValueError, match="k must be ≥ 1"):
            sw.compute_weight(1.0, 0)


class TestRiemannSelbergConnection:
    """Tests for RiemannSelbergConnection class."""
    
    def test_initialization(self):
        """Test connection initialization."""
        conn = RiemannSelbergConnection(precision=30)
        assert conn.precision == 30
        assert conn.riemann.precision == 30
        assert conn.selberg.precision == 30
    
    def test_compare_weights_basic(self):
        """Test basic weight comparison."""
        conn = RiemannSelbergConnection()
        
        result = conn.compare_weights(p=2, k=1)
        
        # Check all fields are present
        assert hasattr(result, 'riemann_weight')
        assert hasattr(result, 'selberg_weight')
        assert hasattr(result, 'selberg_asymptotic')
        assert hasattr(result, 'relative_error')
        assert hasattr(result, 'correspondence_quality')
        
        # All values should be positive
        assert result.riemann_weight > 0
        assert result.selberg_weight > 0
        assert result.selberg_asymptotic > 0
        
        # Relative error should be in [0, 1]
        assert 0 <= result.relative_error <= 1
    
    def test_correspondence_for_small_primes(self):
        """Test correspondence holds for small primes."""
        conn = RiemannSelbergConnection()
        
        # For primes 2, 3, 5, 7 with k=1, correspondence should be good
        primes = [2, 3, 5, 7]
        
        for p in primes:
            result = conn.compare_weights(p, k=1)
            
            # Riemann and asymptotic Selberg should be close
            # (within 20% for these small cases)
            if p >= 5:
                assert result.correspondence_quality < 0.2
    
    def test_correspondence_improves_with_p(self):
        """Test that correspondence improves for larger primes."""
        conn = RiemannSelbergConnection()
        
        # Test for k=1, varying p
        primes = [3, 5, 7, 11, 13, 17, 19]
        k = 1
        
        qualities = []
        for p in primes:
            result = conn.compare_weights(p, k)
            qualities.append(result.correspondence_quality)
        
        # For larger primes (p > 5), quality should be reasonably good
        for i, p in enumerate(primes):
            if p > 5:
                assert qualities[i] < 0.15  # Within 15%
    
    def test_demonstrate_convergence(self):
        """Test convergence demonstration over multiple primes."""
        conn = RiemannSelbergConnection()
        
        primes = [2, 3, 5, 7]
        k_values = [1, 2, 3]
        
        results = conn.demonstrate_convergence(primes, k_values)
        
        # Check all arrays have correct shape
        assert results['riemann_weights'].shape == (len(primes), len(k_values))
        assert results['selberg_weights'].shape == (len(primes), len(k_values))
        assert results['selberg_asymptotic'].shape == (len(primes), len(k_values))
        assert results['relative_errors'].shape == (len(primes), len(k_values))
        
        # All values should be positive
        assert np.all(results['riemann_weights'] > 0)
        assert np.all(results['selberg_weights'] > 0)
        assert np.all(results['selberg_asymptotic'] > 0)
        
        # Relative errors should be in [0, 1]
        assert np.all(results['relative_errors'] >= 0)
        assert np.all(results['relative_errors'] <= 1)
    
    def test_validate_correspondence(self):
        """Test correspondence validation."""
        conn = RiemannSelbergConnection()
        
        validation = conn.validate_correspondence(p_max=30, k_max=3, tolerance=0.15)
        
        # Check validation structure
        assert 'validation_passed' in validation
        assert 'success_rate' in validation
        assert 'total_comparisons' in validation
        
        # Should have reasonable success rate
        assert validation['success_rate'] > 0.5  # At least 50% should pass
        
        # Total comparisons should match expected count
        n_primes = len(conn.riemann._primes_up_to(30))
        expected_comparisons = n_primes * 3  # k=1,2,3
        assert validation['total_comparisons'] == expected_comparisons
    
    def test_asymptotic_expansion_analysis(self):
        """Test asymptotic expansion analysis."""
        conn = RiemannSelbergConnection()
        
        ell_values = np.linspace(1.0, 5.0, 20)
        results = conn.asymptotic_expansion_analysis(ell_values, k=1)
        
        # Check structure
        assert 'ell_values' in results
        assert 'sinh_exact' in results
        assert 'exp_asymptotic' in results
        assert 'relative_errors' in results
        assert 'convergence_threshold' in results
        
        # All values should be positive
        assert np.all(results['sinh_exact'] > 0)
        assert np.all(results['exp_asymptotic'] > 0)
        
        # Errors should decrease with ℓ
        errors = results['relative_errors']
        # For large ℓ, errors should be small
        assert errors[-1] < errors[0]  # Error at ℓ=5 < error at ℓ=1


class TestConvenienceFunctions:
    """Tests for convenience functions."""
    
    def test_compare_riemann_selberg_weights(self):
        """Test convenience comparison function."""
        result = compare_riemann_selberg_weights(p=5, k=2)
        
        assert hasattr(result, 'riemann_weight')
        assert hasattr(result, 'selberg_asymptotic')
        assert result.riemann_weight > 0
    
    def test_validate_weight_correspondence(self):
        """Test convenience validation function."""
        is_valid = validate_weight_correspondence(p_max=30, k_max=3)
        
        # Should return boolean
        assert isinstance(is_valid, bool)


class TestMathematicalProperties:
    """Tests for mathematical properties of the connection."""
    
    def test_weight_ratio_consistency(self):
        """Test that weight ratios are consistent across k."""
        conn = RiemannSelbergConnection()
        
        p = 7
        k1, k2 = 1, 2
        
        result1 = conn.compare_weights(p, k1)
        result2 = conn.compare_weights(p, k2)
        
        # Ratio of Riemann weights should match p
        ratio_riemann = result1.riemann_weight / result2.riemann_weight
        expected_ratio = np.sqrt(p)
        assert_allclose(ratio_riemann, expected_ratio, rtol=0.01)
    
    def test_logarithmic_correspondence(self):
        """Test that ℓ = log(p) correspondence is used correctly."""
        conn = RiemannSelbergConnection()
        
        p = 11
        k = 1
        
        result = conn.compare_weights(p, k)
        
        # Metadata should contain ℓ = log(p)
        expected_ell = np.log(p)
        assert_allclose(result.metadata['ell'], expected_ell, rtol=1e-10)
    
    def test_asymptotic_formula_accuracy(self):
        """Test accuracy of asymptotic formula for large ℓ."""
        sw = SelbergWeight()
        
        # For ℓ ≥ 5, asymptotic should be very accurate
        large_ell_values = [5.0, 7.0, 10.0, 15.0]
        
        for ell in large_ell_values:
            rel_error = sw.relative_error(ell, k=1)
            # Should be within 1% for ℓ ≥ 5
            assert rel_error < 0.01, f"For ℓ={ell}, error={rel_error} > 1%"
    
    def test_exponential_decay(self):
        """Test that both weights exhibit exponential decay in k."""
        conn = RiemannSelbergConnection()
        
        p = 13
        k_values = range(1, 8)
        
        riemann_weights = []
        selberg_weights = []
        
        for k in k_values:
            result = conn.compare_weights(p, k)
            riemann_weights.append(result.riemann_weight)
            selberg_weights.append(result.selberg_asymptotic)
        
        # Both should decay roughly exponentially
        # Check that log(weight) is roughly linear in k
        log_riemann = np.log(riemann_weights)
        log_selberg = np.log(selberg_weights)
        
        # Fit linear model: log(w) = a*k + b
        k_array = np.array(k_values)
        
        # Riemann: log(weight) = log(log p) - (k/2)*log(p)
        # Slope should be ~ -log(p)/2
        slope_riemann = np.polyfit(k_array, log_riemann, deg=1)[0]
        expected_slope = -np.log(p) / 2
        assert_allclose(slope_riemann, expected_slope, rtol=0.01)
        
        # Selberg asymptotic has same decay rate (by construction)
        slope_selberg = np.polyfit(k_array, log_selberg, deg=1)[0]
        assert_allclose(slope_selberg, expected_slope, rtol=0.01)


class TestCertificateGeneration:
    """Tests for certificate generation."""
    
    def test_generate_comparison_certificate(self):
        """Test certificate generation."""
        cert = generate_comparison_certificate()
        
        # Check required fields
        assert 'title' in cert
        assert 'qcal_signature' in cert
        assert 'validation' in cert
        assert 'test_cases' in cert
        assert 'psi_coherence' in cert
        
        # Check QCAL signature format
        assert cert['qcal_signature'].startswith('0xQCAL_RIEMANN_SELBERG_CONNECTION_')
        
        # Ψ coherence should be 0 or 1
        assert cert['psi_coherence'] in [0.0, 1.0]
        
        # Should have test cases
        assert len(cert['test_cases']) > 0
        
        # Each test case should have required fields
        for case in cert['test_cases']:
            assert 'p' in case
            assert 'k' in case
            assert 'riemann_weight' in case
            assert 'selberg_asymptotic' in case


class TestEdgeCases:
    """Tests for edge cases and boundary conditions."""
    
    def test_k_equals_1(self):
        """Test k=1 case specifically."""
        conn = RiemannSelbergConnection()
        
        # For k=1, weights should match well for moderate primes
        for p in [5, 7, 11, 13]:
            result = conn.compare_weights(p, 1)
            # Should be within 10% for these primes
            assert result.correspondence_quality < 0.1
    
    def test_very_large_prime(self):
        """Test with very large prime."""
        conn = RiemannSelbergConnection()
        
        # Use a larger prime
        p = 97
        k = 1
        
        result = conn.compare_weights(p, k)
        
        # For large p, correspondence should be excellent
        assert result.correspondence_quality < 0.05
    
    def test_high_k_values(self):
        """Test with high k values."""
        conn = RiemannSelbergConnection()
        
        p = 7
        high_k_values = [5, 7, 10]
        
        for k in high_k_values:
            result = conn.compare_weights(p, k)
            
            # Weights should be very small but positive
            assert result.riemann_weight > 0
            assert result.riemann_weight < 0.01
            assert result.selberg_asymptotic > 0
            assert result.selberg_asymptotic < 0.01
    
    def test_precision_independence(self):
        """Test that results are consistent across precision settings."""
        conn1 = RiemannSelbergConnection(precision=30)
        conn2 = RiemannSelbergConnection(precision=50)
        
        p, k = 7, 2
        
        result1 = conn1.compare_weights(p, k)
        result2 = conn2.compare_weights(p, k)
        
        # Results should match to reasonable precision
        assert_allclose(result1.riemann_weight, result2.riemann_weight, rtol=1e-8)
        assert_allclose(result1.selberg_asymptotic, result2.selberg_asymptotic, rtol=1e-8)


def test_module_imports():
    """Test that module imports work correctly."""
    from operators.riemann_selberg_weight_connection import (
        RiemannWeight,
        SelbergWeight,
        RiemannSelbergConnection,
        F0_QCAL,
        C_COHERENCE
    )
    
    assert F0_QCAL == 141.7001
    assert C_COHERENCE == 244.36


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
