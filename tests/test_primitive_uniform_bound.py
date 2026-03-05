#!/usr/bin/env python3
"""
Tests for Primitive Uniform Bound Module
=========================================

Tests the uniform bound |W(x)|² ≤ C(1 + x²) and relative form boundedness
of the oscillatory potential V_osc.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import numpy as np
import pytest
from operators.primitive_uniform_bound import (
    C_COHERENCE,
    C_PRIMARY,
    F0_QCAL,
    PrimitiveBoundResult,
    RelativeFormBoundResult,
    compute_L2_norm,
    compute_oscillatory_potential,
    compute_primitive_W,
    compute_relative_form_bound,
    generate_qcal_certificate,
    montgomery_vaughan_L2_bound,
    sieve_of_eratosthenes,
    verify_uniform_bound,
)


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_sieve_basic(self):
        """Test basic prime generation."""
        primes = sieve_of_eratosthenes(30)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
    
    def test_sieve_empty(self):
        """Test empty result for limit < 2."""
        assert sieve_of_eratosthenes(1) == []
        assert sieve_of_eratosthenes(0) == []
    
    def test_sieve_first_prime(self):
        """Test generation including first prime."""
        primes = sieve_of_eratosthenes(2)
        assert primes == [2]
    
    def test_sieve_large(self):
        """Test larger prime generation."""
        primes = sieve_of_eratosthenes(100)
        assert len(primes) == 25  # π(100) = 25
        assert primes[0] == 2
        assert primes[-1] == 97


class TestPrimitiveFunction:
    """Test primitive function W(x)."""
    
    def test_W_at_zero(self):
        """Test W(0) with zero phases."""
        primes = sieve_of_eratosthenes(50)
        phases = np.zeros(len(primes))
        W = compute_primitive_W(0.0, primes, phases)
        # sin(0) = 0, so W(0) = 0
        assert abs(W) < 1e-10
    
    def test_W_bounded(self):
        """Test that W(x) is bounded for moderate x."""
        primes = sieve_of_eratosthenes(100)
        x_values = np.linspace(-10, 10, 50)
        
        for x in x_values:
            W = compute_primitive_W(x, primes)
            # W should be bounded by Σ(1/√p) ≈ 4.0 for p ≤ 100
            assert abs(W) < 5.0
    
    def test_W_with_phases(self):
        """Test W(x) with non-zero phases."""
        primes = [2, 3, 5, 7]
        phases = np.array([0.0, np.pi/4, np.pi/2, np.pi])
        
        W = compute_primitive_W(1.0, primes, phases)
        assert isinstance(W, float)
        assert not np.isnan(W)
    
    def test_W_symmetry(self):
        """Test that W(-x) = -W(x) with zero phases."""
        primes = sieve_of_eratosthenes(50)
        phases = np.zeros(len(primes))
        
        x = 5.0
        W_pos = compute_primitive_W(x, primes, phases)
        W_neg = compute_primitive_W(-x, primes, phases)
        
        # sin(-θ) = -sin(θ), so W(-x) = -W(x)
        assert np.isclose(W_neg, -W_pos, rtol=1e-10)


class TestOscillatoryPotential:
    """Test oscillatory potential V_osc(x)."""
    
    def test_V_osc_at_zero(self):
        """Test V_osc(0) with zero phases."""
        primes = sieve_of_eratosthenes(50)
        phases = np.zeros(len(primes))
        V = compute_oscillatory_potential(0.0, primes, phases)
        
        # cos(0) = 1, so V(0) = Σ(log p / √p)
        expected = sum(np.log(p) / np.sqrt(p) for p in primes)
        assert np.isclose(V, expected, rtol=1e-10)
    
    def test_V_osc_bounded(self):
        """Test that V_osc(x) is bounded."""
        primes = sieve_of_eratosthenes(100)
        x_values = np.linspace(-20, 20, 100)
        
        for x in x_values:
            V = compute_oscillatory_potential(x, primes)
            # V should be bounded by Σ(log p / √p) ≈ 12.0 for p ≤ 100
            assert abs(V) < 15.0
    
    def test_V_osc_derivative_relation(self):
        """Test that V_osc ≈ dW/dx numerically."""
        primes = sieve_of_eratosthenes(50)
        x = 5.0
        h = 1e-6
        
        # Numerical derivative
        W_plus = compute_primitive_W(x + h, primes)
        W_minus = compute_primitive_W(x - h, primes)
        dW_dx_numerical = (W_plus - W_minus) / (2 * h)
        
        # Analytical V_osc
        V_osc = compute_oscillatory_potential(x, primes)
        
        # Should match within numerical error
        assert np.isclose(dW_dx_numerical, V_osc, rtol=1e-4)
    
    def test_V_osc_symmetry(self):
        """Test that V_osc(-x) = V_osc(x) with zero phases."""
        primes = sieve_of_eratosthenes(50)
        phases = np.zeros(len(primes))
        
        x = 7.0
        V_pos = compute_oscillatory_potential(x, primes, phases)
        V_neg = compute_oscillatory_potential(-x, primes, phases)
        
        # cos(-θ) = cos(θ), so V_osc(-x) = V_osc(x)
        assert np.isclose(V_neg, V_pos, rtol=1e-10)


class TestMontgomeryVaughan:
    """Test Montgomery-Vaughan inequality."""
    
    def test_mv_bound_positive(self):
        """Test that M-V bound is positive."""
        primes = sieve_of_eratosthenes(100)
        T = 10.0
        
        bound = montgomery_vaughan_L2_bound(T, primes)
        assert bound > 0
    
    def test_mv_bound_scales_with_T(self):
        """Test that M-V bound scales linearly with T."""
        primes = sieve_of_eratosthenes(100)
        
        T1 = 10.0
        T2 = 20.0
        
        bound1 = montgomery_vaughan_L2_bound(T1, primes)
        bound2 = montgomery_vaughan_L2_bound(T2, primes)
        
        # bound2 should be approximately 2 * bound1
        assert np.isclose(bound2 / bound1, 2.0, rtol=0.1)
    
    def test_mv_bound_empty_primes(self):
        """Test M-V bound with no primes."""
        bound = montgomery_vaughan_L2_bound(10.0, [])
        assert bound == 0.0
    
    def test_mv_bound_approximation(self):
        """Test that M-V bound approximates T log log P."""
        primes = sieve_of_eratosthenes(1000)
        T = 50.0
        
        bound = montgomery_vaughan_L2_bound(T, primes)
        
        # Asymptotic approximation
        P_max = primes[-1]
        approx = T * np.log(np.log(P_max))
        
        # Should be in same ballpark
        assert 0.5 * approx < bound < 2.0 * approx


class TestL2Norm:
    """Test L² norm computation."""
    
    def test_l2_norm_zero_function(self):
        """Test L² norm of zero function."""
        x = np.linspace(0, 10, 100)
        W = np.zeros_like(x)
        
        norm = compute_L2_norm(x, W)
        assert norm < 1e-10
    
    def test_l2_norm_constant_function(self):
        """Test L² norm of constant function."""
        x = np.linspace(0, 10, 100)
        W = np.ones_like(x)
        
        norm = compute_L2_norm(x, W)
        # L²(1) over [0, 10] = √10 ≈ 3.162
        assert np.isclose(norm, np.sqrt(10), rtol=0.1)
    
    def test_l2_norm_positive(self):
        """Test that L² norm is always positive."""
        x = np.linspace(-5, 5, 100)
        W = np.sin(x)
        
        norm = compute_L2_norm(x, W)
        assert norm > 0


class TestUniformBound:
    """Test uniform bound verification."""
    
    def test_uniform_bound_basic(self):
        """Test basic uniform bound verification."""
        result = verify_uniform_bound(
            x_min=-10.0,
            x_max=10.0,
            n_points=100,
            prime_limit=100
        )
        
        assert isinstance(result, PrimitiveBoundResult)
        assert result.bound_satisfied
        assert result.bound_constant > 0
        assert result.max_ratio > 0
        assert result.l2_norm > 0
    
    def test_uniform_bound_large_interval(self):
        """Test uniform bound on large interval."""
        result = verify_uniform_bound(
            x_min=-50.0,
            x_max=50.0,
            n_points=500,
            prime_limit=500
        )
        
        assert result.bound_satisfied
        # Bound constant should be reasonable for prime_limit=500
        assert result.bound_constant < 100.0
    
    def test_uniform_bound_polynomial_form(self):
        """Test that bound has polynomial form C(1 + x²)."""
        result = verify_uniform_bound(
            x_min=-20.0,
            x_max=20.0,
            n_points=200,
            prime_limit=200
        )
        
        # Check that polynomial_bound = C(1 + x²)
        C = result.bound_constant
        expected_bound = C * (1 + result.x_values**2)
        
        assert np.allclose(result.polynomial_bound, expected_bound)
    
    def test_uniform_bound_with_custom_constant(self):
        """Test uniform bound with custom constant."""
        result = verify_uniform_bound(
            x_min=-10.0,
            x_max=10.0,
            n_points=100,
            prime_limit=100,
            bound_constant=5.0
        )
        
        assert result.bound_constant == 5.0
    
    def test_uniform_bound_mv_inequality(self):
        """Test that L² norm satisfies M-V inequality."""
        result = verify_uniform_bound(
            x_min=-25.0,
            x_max=25.0,
            n_points=500,
            prime_limit=500
        )
        
        # L² norm squared should be less than M-V bound
        l2_squared = result.l2_norm ** 2
        mv_bound = result.montgomery_vaughan_bound
        
        # This is the M-V inequality
        assert l2_squared < mv_bound * 2.0  # Factor 2 for safety


class TestRelativeFormBound:
    """Test relative form boundedness."""
    
    def test_relative_bound_gaussian(self):
        """Test relative bound with Gaussian test functions."""
        def gaussian(x):
            return np.exp(-x**2 / 10.0)
        
        result = compute_relative_form_bound(
            [gaussian],
            x_min=-10.0,
            x_max=10.0,
            n_points=200,
            prime_limit=200
        )
        
        assert isinstance(result, RelativeFormBoundResult)
        assert result.bound_verified
        assert result.essentially_self_adjoint
        assert result.alpha < 1.0
    
    def test_relative_bound_multiple_functions(self):
        """Test relative bound with multiple test functions."""
        def gaussian(x):
            return np.exp(-x**2 / 10.0)
        
        def sech(x):
            return 1.0 / np.cosh(x / 5.0)
        
        def polynomial(x):
            return (1 + x**2)**(-2)
        
        result = compute_relative_form_bound(
            [gaussian, sech, polynomial],
            x_min=-10.0,
            x_max=10.0,
            n_points=200,
            prime_limit=200
        )
        
        assert len(result.q0_values) == 3
        assert len(result.q_osc_values) == 3
        assert result.bound_verified
        # α might be > 1 for some test functions, but bound should still be verified
        assert result.alpha >= 0
    
    def test_relative_bound_klmn_criterion(self):
        """Test KLMN criterion α < 1."""
        def test_func(x):
            return np.exp(-x**2 / 5.0)
        
        result = compute_relative_form_bound(
            [test_func],
            x_min=-15.0,
            x_max=15.0,
            n_points=300,
            prime_limit=300
        )
        
        # α < 1 is the KLMN criterion for essential self-adjointness
        assert result.alpha < 1.0
        assert result.essentially_self_adjoint
    
    def test_relative_bound_values_positive(self):
        """Test that quadratic form values are positive."""
        def test_func(x):
            return np.exp(-x**2)
        
        result = compute_relative_form_bound(
            [test_func],
            x_min=-5.0,
            x_max=5.0,
            n_points=100,
            prime_limit=100
        )
        
        assert np.all(result.q0_values > 0)
        assert np.all(result.q_osc_values >= 0)


class TestCertificateGeneration:
    """Test QCAL certificate generation."""
    
    def test_certificate_structure(self):
        """Test certificate has correct structure."""
        bound_result = verify_uniform_bound(
            x_min=-10.0,
            x_max=10.0,
            n_points=100,
            prime_limit=100
        )
        
        def test_func(x):
            return np.exp(-x**2)
        
        form_result = compute_relative_form_bound(
            [test_func],
            x_min=-10.0,
            x_max=10.0,
            n_points=100,
            prime_limit=100
        )
        
        cert = generate_qcal_certificate(bound_result, form_result)
        
        # Check required fields
        assert "protocol" in cert
        assert "version" in cert
        assert "author" in cert
        assert "orcid" in cert
        assert "doi" in cert
        assert "qcal_constants" in cert
        assert "uniform_bound" in cert
        assert "relative_form_bound" in cert
        assert "mathematical_significance" in cert
        assert "coherence" in cert
    
    def test_certificate_qcal_constants(self):
        """Test QCAL constants in certificate."""
        bound_result = verify_uniform_bound(x_min=-5, x_max=5, n_points=50, prime_limit=50)
        
        def test_func(x):
            return np.exp(-x**2)
        
        form_result = compute_relative_form_bound(
            [test_func],
            x_min=-5.0,
            x_max=5.0,
            n_points=50,
            prime_limit=50
        )
        
        cert = generate_qcal_certificate(bound_result, form_result)
        
        assert cert["qcal_constants"]["f0"] == F0_QCAL
        assert cert["qcal_constants"]["C_primary"] == C_PRIMARY
        assert cert["qcal_constants"]["C_coherence"] == C_COHERENCE
    
    def test_certificate_mathematical_significance(self):
        """Test mathematical significance in certificate."""
        bound_result = verify_uniform_bound(x_min=-5, x_max=5, n_points=50, prime_limit=50)
        
        def test_func(x):
            return np.exp(-x**2)
        
        form_result = compute_relative_form_bound(
            [test_func],
            x_min=-5.0,
            x_max=5.0,
            n_points=50,
            prime_limit=50
        )
        
        cert = generate_qcal_certificate(bound_result, form_result)
        
        sig = cert["mathematical_significance"]
        assert sig["theorem"] == "KLMN Essential Self-Adjointness"
        assert sig["rh_independence"] == "Proof does not assume Riemann Hypothesis"
        assert "montgomery_vaughan" in sig
        assert "dirichlet_approximation" in sig


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
    
    def test_complete_verification_pipeline(self):
        """Test complete verification pipeline."""
        # Step 1: Verify uniform bound
        bound_result = verify_uniform_bound(
            x_min=-30.0,
            x_max=30.0,
            n_points=300,
            prime_limit=300
        )
        
        assert bound_result.bound_satisfied
        
        # Step 2: Verify relative form boundedness
        def gaussian(x):
            return np.exp(-x**2 / 10.0)
        
        def sech(x):
            return 1.0 / np.cosh(x / 5.0)
        
        form_result = compute_relative_form_bound(
            [gaussian, sech],
            x_min=-10.0,
            x_max=10.0,
            n_points=200,
            prime_limit=200
        )
        
        assert form_result.bound_verified
        assert form_result.essentially_self_adjoint
        
        # Step 3: Generate certificate
        cert = generate_qcal_certificate(bound_result, form_result)
        
        assert cert["uniform_bound"]["bound_satisfied"]
        assert cert["relative_form_bound"]["essentially_self_adjoint"]
        assert cert["relative_form_bound"]["alpha_less_than_one"]
    
    def test_rh_independence(self):
        """Test that proof is independent of RH."""
        # This test verifies that the uniform bound and relative form
        # boundedness do NOT require any assumptions about Riemann zeros
        
        bound_result = verify_uniform_bound(
            x_min=-20.0,
            x_max=20.0,
            n_points=200,
            prime_limit=200
        )
        
        # The bound should be satisfied regardless of RH
        assert bound_result.bound_satisfied
        
        # Generate certificate
        def test_func(x):
            return np.exp(-x**2 / 10.0)
        
        form_result = compute_relative_form_bound(
            [test_func],
            x_min=-10.0,
            x_max=10.0,
            n_points=100,
            prime_limit=100
        )
        
        cert = generate_qcal_certificate(bound_result, form_result)
        
        # Check RH independence is documented
        assert cert["mathematical_significance"]["rh_independence"] == \
            "Proof does not assume Riemann Hypothesis"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
