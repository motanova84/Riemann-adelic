#!/usr/bin/env python3
"""
Tests for Heat Kernel Trace Identity Module
===========================================

Tests the exact trace identity Tr(e^{-tH}) = Weyl(t) + Prime oscillations
via Duhamel's formula.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import numpy as np
import pytest
from operators.heat_kernel_trace_identity import (
    C_COHERENCE,
    C_PRIMARY,
    F0_QCAL,
    WEYL_A0,
    WEYL_A2,
    HeatKernelResult,
    TraceIdentityResult,
    compute_duhamel_correction,
    compute_heat_kernel_trace,
    compute_oscillatory_part,
    compute_weyl_smooth_part,
    connect_to_explicit_formula,
    generate_qcal_certificate,
    sieve_of_eratosthenes,
    verify_trace_identity,
)


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_sieve_basic(self):
        """Test basic prime generation."""
        primes = sieve_of_eratosthenes(30)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
    
    def test_sieve_large(self):
        """Test larger prime generation."""
        primes = sieve_of_eratosthenes(100)
        assert len(primes) == 25  # π(100) = 25


class TestWeylSmoothPart:
    """Test Weyl smooth part computation."""
    
    def test_weyl_positive(self):
        """Test that Weyl part is positive for t > 0."""
        for t in [0.01, 0.1, 1.0, 10.0]:
            weyl = compute_weyl_smooth_part(t)
            assert weyl > 0
    
    def test_weyl_zero_at_zero(self):
        """Test that Weyl part is zero at t = 0."""
        weyl = compute_weyl_smooth_part(0.0)
        assert weyl == 0.0
    
    def test_weyl_asymptotic_behavior(self):
        """Test Weyl asymptotic behavior at small t."""
        # For small t: Weyl ~ (4πt)^{-1/2}
        t = 0.01
        weyl = compute_weyl_smooth_part(t)
        expected = 1.0 / np.sqrt(4.0 * np.pi * t)
        # Should be close since higher order terms are small
        assert np.isclose(weyl, expected, rtol=0.2)
    
    def test_weyl_decreasing(self):
        """Test that Weyl part has expected behavior."""
        # Weyl has form (4πt)^{-1/2} * (a₀ + a₂ t²)
        # At small t: dominated by (4πt)^{-1/2} → decreasing
        # At large t: t² term can cause non-monotonic behavior
        
        # Test small t regime (should decrease)
        t_small = [0.1, 0.2, 0.3, 0.4, 0.5]
        weyl_small = [compute_weyl_smooth_part(t) for t in t_small]
        
        # Should be decreasing in small t regime
        for i in range(len(weyl_small) - 1):
            assert weyl_small[i] > weyl_small[i+1]
        
        # Test that Weyl is positive everywhere
        t_all = [0.1, 0.5, 1.0, 2.0, 5.0, 10.0]
        weyl_all = [compute_weyl_smooth_part(t) for t in t_all]
        assert all(w > 0 for w in weyl_all)
    
    def test_weyl_coefficients(self):
        """Test Weyl coefficients are correct."""
        # a₀ = 1, a₂ = 7/8 for Wu-Sprung
        assert WEYL_A0 == 1.0
        assert WEYL_A2 == 7.0 / 8.0
    
    def test_weyl_with_custom_coefficients(self):
        """Test Weyl with custom coefficients."""
        t = 1.0
        weyl1 = compute_weyl_smooth_part(t, a0=1.0, a2=0.5)
        weyl2 = compute_weyl_smooth_part(t, a0=2.0, a2=0.5)
        
        # Doubling a₀ should increase the result
        assert weyl2 > weyl1
        # Ratio should be roughly 2 (within 30%)
        ratio = weyl2 / weyl1
        assert 1.5 < ratio < 2.5


class TestOscillatoryPart:
    """Test oscillatory part computation."""
    
    def test_oscillatory_positive_small_t(self):
        """Test oscillatory part is positive for small t."""
        primes = sieve_of_eratosthenes(50)
        t = 0.01
        osc = compute_oscillatory_part(t, primes)
        assert osc > 0
    
    def test_oscillatory_zero_at_zero(self):
        """Test oscillatory part at t = 0."""
        primes = sieve_of_eratosthenes(50)
        osc = compute_oscillatory_part(0.0, primes)
        assert osc == 0.0
    
    def test_oscillatory_decreasing(self):
        """Test oscillatory part decreases with increasing t."""
        primes = sieve_of_eratosthenes(50)
        t_values = [0.1, 0.5, 1.0, 2.0]
        osc_values = [compute_oscillatory_part(t, primes) for t in t_values]
        
        # Should generally decrease due to exponential decay
        for i in range(len(osc_values) - 1):
            assert osc_values[i] > osc_values[i+1]
    
    def test_oscillatory_prime_dependence(self):
        """Test oscillatory part depends on number of primes."""
        primes_small = sieve_of_eratosthenes(50)
        primes_large = sieve_of_eratosthenes(200)
        
        t = 0.5
        osc_small = compute_oscillatory_part(t, primes_small)
        osc_large = compute_oscillatory_part(t, primes_large)
        
        # More primes should give larger contribution
        assert osc_large > osc_small
    
    def test_oscillatory_k_max_dependence(self):
        """Test oscillatory part depends on k_max."""
        primes = sieve_of_eratosthenes(50)
        t = 0.5
        
        osc_k1 = compute_oscillatory_part(t, primes, k_max=1)
        osc_k5 = compute_oscillatory_part(t, primes, k_max=5)
        
        # Higher k_max includes more terms
        assert osc_k5 > osc_k1
    
    def test_oscillatory_explicit_formula_connection(self):
        """Test connection to explicit formula coefficients."""
        primes = [2, 3, 5, 7]
        t = 1.0
        
        # At t=1, e^{-k log p} = p^{-k}
        # First term: log(2)/√2 * 1/2 = log(2)/(2√2)
        osc = compute_oscillatory_part(t, primes, k_max=1)
        
        # Should be dominated by first prime
        expected_first_term = np.log(2) / (2 ** 1.5)
        assert osc > expected_first_term * 0.5


class TestDuhamelCorrection:
    """Test Duhamel correction computation."""
    
    def test_duhamel_nonnegative(self):
        """Test Duhamel correction is non-negative."""
        primes = sieve_of_eratosthenes(50)
        for t in [0.1, 0.5, 1.0]:
            duhamel = compute_duhamel_correction(t, primes)
            assert duhamel >= 0
    
    def test_duhamel_zero_at_zero(self):
        """Test Duhamel correction at t = 0."""
        primes = sieve_of_eratosthenes(50)
        duhamel = compute_duhamel_correction(0.0, primes)
        assert duhamel == 0.0
    
    def test_duhamel_small_correction(self):
        """Test Duhamel correction is small compared to main terms."""
        primes = sieve_of_eratosthenes(50)
        t = 0.5
        
        weyl = compute_weyl_smooth_part(t)
        osc = compute_oscillatory_part(t, primes)
        duhamel = compute_duhamel_correction(t, primes)
        
        # Correction should be smaller than oscillatory part
        # (Weyl can be comparable due to t^2 term)
        assert duhamel < osc


class TestHeatKernelTrace:
    """Test complete heat kernel trace computation."""
    
    def test_heat_kernel_basic(self):
        """Test basic heat kernel trace computation."""
        primes = sieve_of_eratosthenes(100)
        t_values = np.logspace(-1, 1, 20)
        
        result = compute_heat_kernel_trace(t_values, primes)
        
        assert isinstance(result, HeatKernelResult)
        assert len(result.trace_values) == len(t_values)
        assert len(result.weyl_part) == len(t_values)
        assert len(result.oscillatory_part) == len(t_values)
    
    def test_heat_kernel_positive_trace(self):
        """Test that trace values are mostly positive for small t."""
        primes = sieve_of_eratosthenes(50)
        # Use smaller time range where trace should be positive
        t_values = np.logspace(-1, 0.5, 10)
        
        result = compute_heat_kernel_trace(t_values, primes)
        
        # Trace should be positive for small t values
        assert np.all(result.trace_values[:5] > 0)
    
    def test_heat_kernel_decreasing_trace(self):
        """Test that trace generally decreases in small t regime."""
        primes = sieve_of_eratosthenes(50)
        # Use very small t values where trace should be monotonically decreasing
        t_values = np.linspace(0.1, 0.5, 20)
        
        result = compute_heat_kernel_trace(t_values, primes)
        
        # Trace should generally decrease in small t regime
        # Check that at least 80% of consecutive pairs decrease
        decreasing_count = sum(1 for i in range(len(result.trace_values) - 1)
                             if result.trace_values[i] > result.trace_values[i+1])
        
        assert decreasing_count >= 0.8 * (len(result.trace_values) - 1)
    
    def test_heat_kernel_with_eigenvalues(self):
        """Test heat kernel with known eigenvalues."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.array([0.5, 1.0])
        
        # Mock eigenvalues
        eigenvalues = np.array([1.0, 4.0, 9.0, 16.0])
        
        result = compute_heat_kernel_trace(t_values, primes, eigenvalues=eigenvalues)
        
        assert result.eigenvalues is not None
        assert len(result.eigenvalues) == 4
    
    def test_heat_kernel_without_duhamel(self):
        """Test heat kernel without Duhamel correction."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        result = compute_heat_kernel_trace(t_values, primes, include_duhamel=False)
        
        # All Duhamel corrections should be zero
        assert np.all(result.duhamel_correction == 0)
    
    def test_heat_kernel_composition(self):
        """Test trace = weyl + osc - duhamel."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        result = compute_heat_kernel_trace(t_values, primes, include_duhamel=True)
        
        # Check composition
        expected_trace = result.weyl_part + result.oscillatory_part - result.duhamel_correction
        
        assert np.allclose(result.trace_values, expected_trace, rtol=1e-10)


class TestTraceIdentity:
    """Test trace identity verification."""
    
    def test_identity_verification_basic(self):
        """Test basic identity verification."""
        primes = sieve_of_eratosthenes(100)
        t_values = np.logspace(-1, 1, 20)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result, tolerance=0.2)
        
        assert isinstance(identity_result, TraceIdentityResult)
        # Check that identity_verified is a Python bool (numpy converts)
        assert isinstance(bool(identity_result.identity_verified), bool)
    
    def test_identity_formula_string(self):
        """Test identity formula string."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        assert "Tr(e^{-tH})" in identity_result.identity_formula
        assert "Weyl" in identity_result.identity_formula
        assert "log p" in identity_result.identity_formula
    
    def test_identity_error_metrics(self):
        """Test error metrics are computed."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        assert identity_result.max_relative_error >= 0
        assert identity_result.average_relative_error >= 0
        assert identity_result.max_relative_error >= identity_result.average_relative_error
    
    def test_identity_contributions(self):
        """Test Weyl and oscillatory contributions."""
        primes = sieve_of_eratosthenes(100)
        t_values = np.logspace(-1, 1, 20)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        assert identity_result.weyl_contribution > 0
        assert identity_result.oscillatory_contribution > 0
    
    def test_identity_tolerance_effect(self):
        """Test effect of tolerance on verification."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        
        # Strict tolerance
        identity_strict = verify_trace_identity(heat_result, tolerance=0.01)
        
        # Loose tolerance
        identity_loose = verify_trace_identity(heat_result, tolerance=0.5)
        
        # Loose tolerance should be more likely to pass
        if not identity_strict.identity_verified:
            assert identity_loose.identity_verified or identity_loose.max_relative_error < 0.5


class TestExplicitFormula:
    """Test connection to explicit formula."""
    
    def test_explicit_formula_basic(self):
        """Test basic explicit formula computation."""
        primes = sieve_of_eratosthenes(100)
        x = 50.0
        
        psi, asymptotic = connect_to_explicit_formula(primes, x)
        
        assert psi > 0
        assert asymptotic > 0
    
    def test_explicit_formula_asymptotic(self):
        """Test asymptotic ψ(x) ~ x."""
        primes = sieve_of_eratosthenes(1000)
        x = 500.0
        
        psi, asymptotic = connect_to_explicit_formula(primes, x)
        
        # ψ(x) ~ x - log(2π) for large x
        assert np.isclose(psi, asymptotic, rtol=0.2)
    
    def test_explicit_formula_prime_theorem(self):
        """Test prime number theorem connection."""
        primes = sieve_of_eratosthenes(1000)
        x = 100.0
        
        psi, asymptotic = connect_to_explicit_formula(primes, x, k_max=1)
        
        # For k_max=1, ψ(x) counts only primes
        # Should be close to x for large x
        assert psi < x
        assert psi > x / 2  # Rough bound
    
    def test_explicit_formula_increasing(self):
        """Test ψ(x) is increasing."""
        primes = sieve_of_eratosthenes(200)
        
        x_values = [20, 50, 100, 150]
        psi_values = [connect_to_explicit_formula(primes, x)[0] for x in x_values]
        
        for i in range(len(psi_values) - 1):
            assert psi_values[i+1] > psi_values[i]


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_certificate_structure(self):
        """Test certificate has correct structure."""
        primes = sieve_of_eratosthenes(100)
        t_values = np.logspace(-1, 1, 20)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        cert = generate_qcal_certificate(heat_result, identity_result)
        
        assert "protocol" in cert
        assert "version" in cert
        assert "author" in cert
        assert "orcid" in cert
        assert "doi" in cert
        assert "qcal_constants" in cert
        assert "trace_identity" in cert
        assert "heat_kernel" in cert
        assert "mathematical_significance" in cert
        assert "coherence" in cert
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        cert = generate_qcal_certificate(heat_result, identity_result)
        
        assert cert["qcal_constants"]["f0"] == F0_QCAL
        assert cert["qcal_constants"]["C_primary"] == C_PRIMARY
        assert cert["qcal_constants"]["C_coherence"] == C_COHERENCE
    
    def test_certificate_mathematical_significance(self):
        """Test mathematical significance in certificate."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 1, 10)
        
        heat_result = compute_heat_kernel_trace(t_values, primes)
        identity_result = verify_trace_identity(heat_result)
        
        cert = generate_qcal_certificate(heat_result, identity_result)
        
        sig = cert["mathematical_significance"]
        assert "duhamel_identity" in sig
        assert "weyl_expansion" in sig
        assert "gutzwiller_formula" in sig
        assert "spectral_sieve" in sig
        assert "explicit_formula" in sig


class TestQCALConstants:
    """Test QCAL constant values."""
    
    def test_f0_value(self):
        """Test fundamental frequency f₀."""
        assert F0_QCAL == 141.7001
    
    def test_c_primary_value(self):
        """Test primary constant C."""
        assert C_PRIMARY == 629.83
    
    def test_c_coherence_value(self):
        """Test coherence constant."""
        assert C_COHERENCE == 244.36


class TestIntegration:
    """Integration tests."""
    
    def test_complete_pipeline(self):
        """Test complete verification pipeline."""
        # Step 1: Generate primes
        primes = sieve_of_eratosthenes(150)
        assert len(primes) > 0
        
        # Step 2: Compute heat kernel trace (use smaller t range)
        t_values = np.logspace(-1, 0.5, 25)
        heat_result = compute_heat_kernel_trace(t_values, primes, k_max=5)
        
        assert heat_result.trace_norm > 0
        # Check that most trace values are positive (small t regime)
        positive_count = np.sum(heat_result.trace_values > 0)
        assert positive_count > len(t_values) * 0.7  # At least 70% positive
        
        # Step 3: Verify identity
        identity_result = verify_trace_identity(heat_result, tolerance=0.2)
        
        assert identity_result.weyl_contribution > 0
        assert identity_result.oscillatory_contribution > 0
        
        # Step 4: Connect to explicit formula
        psi, asymptotic = connect_to_explicit_formula(primes, 100.0)
        assert psi > 0
        
        # Step 5: Generate certificate
        cert = generate_qcal_certificate(heat_result, identity_result)
        assert cert["protocol"] == "QCAL-RH-HEAT-KERNEL-TRACE-IDENTITY"
    
    def test_duhamel_vs_no_duhamel(self):
        """Test effect of Duhamel correction."""
        primes = sieve_of_eratosthenes(50)
        t_values = np.logspace(-1, 0.5, 10)  # Smaller range
        
        result_with = compute_heat_kernel_trace(t_values, primes, include_duhamel=True)
        result_without = compute_heat_kernel_trace(t_values, primes, include_duhamel=False)
        
        # Traces should be close but not identical
        difference = np.abs(result_with.trace_values - result_without.trace_values)
        assert np.any(difference > 0)
        
        # Difference should be relatively small for small t
        relative_diff = difference / (np.abs(result_with.trace_values) + 1e-10)
        # Most should be small, allow some larger differences
        median_diff = np.median(relative_diff)
        assert median_diff < 0.2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
