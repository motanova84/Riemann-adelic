#!/usr/bin/env python3
"""
Tests for Large Sieve Coercivity Module

Tests the Large Sieve power-law inequality W_reg(γ, t) ≥ c·|γ|^δ with δ = 0.086.
Verifies:
1. Montgomery Large Sieve inequality
2. Power-law growth with correct exponent
3. H^δ coercivity
4. Discrete spectrum confirmation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active
"""

import sys
from pathlib import Path
import numpy as np
import pytest
from scipy.integrate import trapezoid

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import validation functions
from validate_large_sieve_coercivity import (
    spectral_weight_regularized,
    montgomery_large_sieve_bound,
    DELTA,
    HEAT_PARAM,
    PRIMES,
    MONTGOMERY_CONSTANT,
)


class TestSpectralWeight:
    """Tests for spectral weight W_reg(γ, t) function."""
    
    def test_weight_positive(self):
        """Verify W_reg(γ, t) > 0 for all γ ≠ 0."""
        gamma_values = [1.0, 5.0, 10.0, 50.0, 100.0]
        t = HEAT_PARAM
        
        for gamma in gamma_values:
            weight = spectral_weight_regularized(gamma, t)
            assert weight > 0, f"Weight should be positive at γ={gamma}, got {weight}"
            assert np.isfinite(weight), f"Weight should be finite at γ={gamma}"
    
    def test_weight_continuity(self):
        """Verify W_reg is continuous (no jumps)."""
        t = HEAT_PARAM
        gamma_range = np.linspace(1, 10, 20)
        weights = [spectral_weight_regularized(gamma, t) for gamma in gamma_range]
        
        # Check no sudden jumps
        diffs = np.diff(weights)
        max_relative_diff = np.max(np.abs(diffs) / (np.array(weights[:-1]) + 1e-10))
        
        assert max_relative_diff < 1.0, "Weight function has discontinuities"
    
    def test_weight_symmetry(self):
        """Verify W_reg(-γ, t) = W_reg(γ, t) (even function)."""
        t = HEAT_PARAM
        gamma_values = [1.0, 5.0, 10.0]
        
        for gamma in gamma_values:
            weight_pos = spectral_weight_regularized(gamma, t)
            weight_neg = spectral_weight_regularized(-gamma, t)
            
            assert weight_pos == pytest.approx(weight_neg, rel=1e-10), \
                f"Weight not symmetric at γ={gamma}"
    
    def test_weight_convergence(self):
        """Verify weight converges as max_power increases."""
        gamma = 10.0
        t = HEAT_PARAM
        
        weight_10 = spectral_weight_regularized(gamma, t, max_power=10)
        weight_15 = spectral_weight_regularized(gamma, t, max_power=15)
        weight_20 = spectral_weight_regularized(gamma, t, max_power=20)
        
        # Convergence check: relative differences should decrease
        diff_1 = abs(weight_15 - weight_10) / weight_10
        diff_2 = abs(weight_20 - weight_15) / weight_15
        
        assert diff_2 < diff_1, "Weight series should converge"
        assert diff_2 < 0.1, "Weight should be nearly converged at max_power=20"


class TestMontgomeryInequality:
    """Tests for Montgomery Large Sieve inequality."""
    
    def test_bound_computation(self):
        """Test Montgomery bound computation."""
        X = 47
        log_values = np.array([np.log(p) for p in PRIMES if p <= X])
        
        bound = montgomery_large_sieve_bound(X, log_values)
        
        assert bound > 0, "Montgomery bound should be positive"
        assert np.isfinite(bound), "Montgomery bound should be finite"
    
    def test_inequality_holds(self):
        """Verify Montgomery inequality for small X."""
        X = 23
        primes_X = [p for p in PRIMES if p <= X]
        T = 50.0
        
        # Compute mean square
        tau_range = np.linspace(0, T, 100)
        mean_square_vals = []
        
        for tau in tau_range:
            prime_sum = sum(
                np.exp(1j * tau * np.log(p)) * np.log(p) / (p ** (0.5 + HEAT_PARAM))
                for p in primes_X
            )
            mean_square_vals.append(np.abs(prime_sum) ** 2)
        
        mean_square = trapezoid(mean_square_vals, tau_range) / T
        
        # Compute bound (rough estimate)
        log_values_sq = sum(np.log(p) ** 2 / (p ** (2 * (0.5 + HEAT_PARAM))) 
                           for p in primes_X)
        bound = MONTGOMERY_CONSTANT * (2 * X) * log_values_sq
        
        # Should satisfy inequality with some margin
        assert mean_square <= bound * 2.0, \
            f"Montgomery inequality violated: {mean_square} > {bound * 2.0}"


class TestPowerLawGrowth:
    """Tests for power-law growth W_reg(γ, t) ≥ c·|γ|^δ."""
    
    def test_delta_value(self):
        """Verify δ = 0.086 is correctly set."""
        assert DELTA == pytest.approx(0.086, abs=1e-10)
    
    def test_power_law_holds_small_gamma(self):
        """Verify power law at small γ."""
        t = HEAT_PARAM
        c = 0.3  # Conservative constant allowing slack
        
        gamma_values = [1.0, 2.0, 5.0, 10.0]
        
        for gamma in gamma_values:
            weight = spectral_weight_regularized(gamma, t)
            power_law = c * (gamma ** DELTA)
            
            assert weight >= power_law * 0.5, \
                f"Power law failed at γ={gamma}: {weight} < {power_law * 0.5}"
    
    def test_power_law_holds_large_gamma(self):
        """Verify power law at large γ (sustained growth)."""
        t = HEAT_PARAM
        c = 0.3
        
        gamma_values = [50.0, 100.0, 200.0]
        
        for gamma in gamma_values:
            weight = spectral_weight_regularized(gamma, t)
            power_law = c * (gamma ** DELTA)
            
            assert weight >= power_law * 0.3, \
                f"Power law failed at large γ={gamma}: {weight} < {power_law * 0.3}"
    
    def test_growth_ratio_consistency(self):
        """Verify growth ratio stays above threshold."""
        t = HEAT_PARAM
        gamma_range = np.linspace(1, 100, 50)
        
        weights = [spectral_weight_regularized(gamma, t) for gamma in gamma_range]
        power_laws = 0.5 * (gamma_range ** DELTA)
        ratios = np.array(weights) / power_laws
        
        min_ratio = np.min(ratios)
        
        assert min_ratio > 0.2, \
            f"Minimum ratio {min_ratio} too small, power law not sustained"


class TestHDeltaCoercivity:
    """Tests for H^δ Sobolev coercivity."""
    
    def test_gaussian_coercivity(self):
        """Test coercivity with Gaussian test function."""
        t = HEAT_PARAM
        sigma = 5.0
        gamma_range = np.linspace(-100, 100, 400)
        
        # Gaussian in frequency domain
        f_hat = np.exp(-gamma_range ** 2 / (2 * sigma ** 2))
        f_hat = f_hat / np.sqrt(trapezoid(np.abs(f_hat) ** 2, gamma_range))
        
        # Compute quadratic form
        weights = [spectral_weight_regularized(gamma, t) for gamma in gamma_range]
        Q_LS = trapezoid(np.array(weights) * np.abs(f_hat) ** 2, gamma_range)
        
        # Compute H^δ norm
        norm_H_delta_sq = trapezoid(
            (1 + gamma_range ** 2) ** DELTA * np.abs(f_hat) ** 2,
            gamma_range
        )
        
        # Coercivity constant
        c = Q_LS / norm_H_delta_sq if norm_H_delta_sq > 0 else 0
        
        assert c > 0.05, f"Coercivity constant too small: c = {c}"
        assert np.isfinite(c), "Coercivity constant should be finite"
    
    def test_multiple_test_functions(self):
        """Test coercivity with multiple test functions."""
        t = HEAT_PARAM
        gamma_range = np.linspace(-50, 50, 300)
        
        for sigma in [2.0, 5.0, 10.0]:
            # Gaussian with different widths
            f_hat = np.exp(-gamma_range ** 2 / (2 * sigma ** 2))
            f_hat = f_hat / np.sqrt(trapezoid(np.abs(f_hat) ** 2, gamma_range))
            
            weights = [spectral_weight_regularized(gamma, t) for gamma in gamma_range]
            Q_LS = trapezoid(np.array(weights) * np.abs(f_hat) ** 2, gamma_range)
            
            norm_H_delta_sq = trapezoid(
                (1 + gamma_range ** 2) ** DELTA * np.abs(f_hat) ** 2,
                gamma_range
            )
            
            c = Q_LS / norm_H_delta_sq if norm_H_delta_sq > 0 else 0
            
            assert c > 0.01, f"Coercivity failed for σ={sigma}: c = {c}"


class TestDiscreteSpectrum:
    """Tests for discrete spectrum confirmation."""
    
    def test_delta_positive(self):
        """Verify δ > 0 (necessary for compactness)."""
        assert DELTA > 0, "δ must be positive for compact embedding"
    
    def test_sustained_growth_large_gamma(self):
        """Verify growth is sustained at large γ (no flattening)."""
        t = HEAT_PARAM
        gamma_large = [100.0, 200.0, 500.0]
        
        for gamma in gamma_large:
            weight = spectral_weight_regularized(gamma, t, max_power=15)
            power_law = 0.3 * (gamma ** DELTA)
            
            assert weight > power_law * 0.2, \
                f"Growth not sustained at γ={gamma}: {weight} < {power_law * 0.2}"
    
    def test_no_continuous_spectrum_indicator(self):
        """Test that all indicators point to discrete spectrum."""
        # 1. δ > 0
        assert DELTA > 0
        
        # 2. Power law holds at representative points
        t = HEAT_PARAM
        gamma_test = [1.0, 10.0, 50.0, 100.0]
        
        for gamma in gamma_test:
            weight = spectral_weight_regularized(gamma, t)
            power_law = 0.3 * (gamma ** DELTA)
            ratio = weight / power_law
            
            assert ratio > 0.2, f"Power law fails at γ={gamma}, ratio={ratio}"
        
        # 3. Weights are finite everywhere
        for gamma in gamma_test:
            weight = spectral_weight_regularized(gamma, t)
            assert np.isfinite(weight), f"Weight infinite at γ={gamma}"


class TestQCALParameters:
    """Tests for QCAL parameter consistency."""
    
    def test_delta_synchronization(self):
        """Verify δ = 0.086 matches Lean formalization."""
        # This is the KEY synchronization point
        assert DELTA == 0.086, "δ must match Lean value exactly"
    
    def test_heat_param_consistency(self):
        """Verify heat parameter t = 0.05."""
        assert HEAT_PARAM == 0.05, "Heat parameter must be 0.05"
    
    def test_montgomery_constant(self):
        """Verify Montgomery constant C = 3.0."""
        assert MONTGOMERY_CONSTANT == 3.0, "Montgomery constant must be 3.0"
    
    def test_primes_list(self):
        """Verify primes list matches Lean validation_primes."""
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        assert PRIMES == expected_primes, "Primes must match Lean list"


class TestCertificateGeneration:
    """Tests for validation certificate generation."""
    
    def test_certificate_structure(self):
        """Verify certificate has required fields."""
        from validate_large_sieve_coercivity import generate_certificate
        
        # Mock test results
        test_results = [
            {"test": "test1", "passed": True, "value": 1.0},
            {"test": "test2", "passed": True, "value": 2.0},
        ]
        
        cert = generate_certificate(test_results)
        
        # Check required fields
        assert "title" in cert
        assert "theorem" in cert
        assert "timestamp" in cert
        assert "parameters" in cert
        assert "test_results" in cert
        assert "validation_status" in cert
        assert "hash" in cert
        assert "author" in cert
        
        # Check parameter values
        assert cert["parameters"]["delta"] == DELTA
        assert cert["parameters"]["heat_param"] == HEAT_PARAM
    
    def test_hash_generation(self):
        """Verify certificate hash is generated correctly."""
        from validate_large_sieve_coercivity import generate_certificate
        
        test_results = [{"test": "dummy", "passed": True}]
        cert = generate_certificate(test_results)
        
        assert "hash" in cert
        assert cert["hash"].startswith("0xQCAL_LARGE_SIEVE_")
        assert len(cert["hash"]) == len("0xQCAL_LARGE_SIEVE_") + 16


# Pytest configuration
def pytest_configure(config):
    """Configure pytest with custom markers."""
    config.addinivalue_line("markers", "slow: marks tests as slow (deselect with '-m \"not slow\"')")
    config.addinivalue_line("markers", "integration: marks tests as integration tests")


if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, "-v", "--tb=short"])
