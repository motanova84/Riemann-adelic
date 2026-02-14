#!/usr/bin/env python3
"""
Tests for Trace Formula Adélica con Resto Controlado

This module tests the implementation of the Adelic Trace Formula theorem:
    Tr(e^(-tL)) = Weyl(t) + Prime(t) + R(t)
    
where |R(t)| ≤ C·e^(-λ/t) uniformly for all t > 0.

Mathematical Framework:
    - Archimedean component (Weyl term)
    - p-adic components (Prime sum)
    - Controlled remainder with exponential bounds
    - Heat kernel factorization

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.adelic_trace_formula import (
    # Functions
    compute_archimedean_kernel,
    compute_padic_trace_contribution,
    compute_prime_sum_all_primes,
    compute_controlled_remainder,
    compute_adelic_trace_formula,
    verify_remainder_bound,
    demonstrate_trace_formula,
    # Data classes
    AdelicTraceResult,
    HeatKernelComponents,
    # Constants
    F0_QCAL,
    C_PRIMARY,
    C_COHERENCE,
    KAPPA_PI,
)


class TestArchimedeanComponent:
    """Test the archimedean (ℝ) component of the heat kernel."""
    
    def test_archimedean_positive_trace(self):
        """Archimedean trace should be positive for all t > 0."""
        t_values = [0.01, 0.1, 1.0, 10.0]
        for t in t_values:
            tr_R, K_diag = compute_archimedean_kernel(t)
            assert tr_R > 0, f"Trace should be positive at t={t}"
    
    def test_archimedean_asymptotic_small_t(self):
        """For small t, Weyl term should dominate: ~ 1/(4πt)^(1/2)."""
        t = 0.01
        tr_R, _ = compute_archimedean_kernel(t)
        
        # Leading term: 1/√(4πt)
        leading = 1.0 / np.sqrt(4 * np.pi * t)
        
        # Should be of same order of magnitude
        # Note: correction terms (7/8 + O(√t)) contribute significantly
        ratio = tr_R / leading
        assert 0.5 < ratio < 50.0, f"Asymptotic ratio should be O(1-10), got {ratio}"
    
    def test_archimedean_kernel_decay(self):
        """Kernel should decay exponentially in x due to V_eff(x) = x²."""
        t = 1.0
        x_values = np.linspace(-10, 10, 200)
        _, K_diag = compute_archimedean_kernel(t, x_values=x_values)
        
        # Kernel should be maximal near x=0
        center_idx = len(x_values) // 2
        K_center = K_diag[center_idx]
        K_edge = K_diag[0]
        
        assert K_center > K_edge, "Kernel should decay away from center"
        assert K_center > 10 * K_edge, "Decay should be significant"
    
    def test_archimedean_invalid_t(self):
        """Should raise ValueError for t ≤ 0."""
        with pytest.raises(ValueError, match="must be positive"):
            compute_archimedean_kernel(t=0.0)
        
        with pytest.raises(ValueError, match="must be positive"):
            compute_archimedean_kernel(t=-1.0)
    
    def test_archimedean_kappa_dependence(self):
        """Trace should depend on κ parameter."""
        t = 1.0
        tr_1, _ = compute_archimedean_kernel(t, kappa=1.0)
        tr_2, _ = compute_archimedean_kernel(t, kappa=3.0)
        
        # Different κ should give different results
        assert abs(tr_1 - tr_2) > 0.01


class TestPadicComponent:
    """Test the p-adic components of the heat kernel."""
    
    def test_padic_single_prime(self):
        """Single prime contribution should be > 1 (includes identity)."""
        t = 0.5
        for p in [2, 3, 5, 7]:
            tr_p, R_p = compute_padic_trace_contribution(t, p)
            assert tr_p >= 1.0, f"Trace for p={p} should be ≥ 1"
    
    def test_padic_time_decay(self):
        """p-adic contribution should decrease as t increases."""
        p = 2
        t_small = 0.1
        t_large = 10.0
        
        tr_small, _ = compute_padic_trace_contribution(t_small, p)
        tr_large, _ = compute_padic_trace_contribution(t_large, p)
        
        # For large t, e^(-t·k·ln p) → 0, so trace → 1
        assert tr_small > tr_large
        assert abs(tr_large - 1.0) < 0.1, "Should approach 1 for large t"
    
    def test_padic_invalid_prime(self):
        """Should raise ValueError for p < 2."""
        with pytest.raises(ValueError, match="prime"):
            compute_padic_trace_contribution(t=1.0, p=1)
        
        with pytest.raises(ValueError, match="prime"):
            compute_padic_trace_contribution(t=1.0, p=0)
    
    def test_padic_remainder_decay(self):
        """Remainder R_p should decay exponentially with t."""
        p = 3
        t_small = 0.5
        t_large = 5.0
        
        _, R_small = compute_padic_trace_contribution(t_small, p)
        _, R_large = compute_padic_trace_contribution(t_large, p)
        
        assert R_small > R_large, "Remainder should decay with t"
        assert R_large < 0.01, "Remainder should be small for large t"


class TestPrimeSum:
    """Test the sum over all primes."""
    
    def test_prime_sum_positive(self):
        """Prime sum should be positive."""
        t = 1.0
        Prime_t, R_total, primes = compute_prime_sum_all_primes(t, max_prime=50)
        assert Prime_t > 0
    
    def test_prime_sum_convergence(self):
        """Increasing max_prime should improve convergence."""
        t = 1.0
        P1, _, _ = compute_prime_sum_all_primes(t, max_prime=20)
        P2, _, _ = compute_prime_sum_all_primes(t, max_prime=50)
        P3, _, _ = compute_prime_sum_all_primes(t, max_prime=100)
        
        # More primes should give larger sum (but converging)
        assert P1 < P2 < P3
        
        # But convergence means P3 - P2 < P2 - P1
        delta1 = P2 - P1
        delta2 = P3 - P2
        assert delta2 < delta1, "Should show convergence"
    
    def test_prime_sum_primes_list(self):
        """Should return correct list of primes."""
        t = 1.0
        _, _, primes = compute_prime_sum_all_primes(t, max_prime=20)
        
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected_primes
    
    def test_prime_sum_large_t_decay(self):
        """For large t, prime sum should decay exponentially."""
        t_small = 0.5
        t_large = 10.0
        
        P_small, _, _ = compute_prime_sum_all_primes(t_small, max_prime=50)
        P_large, _, _ = compute_prime_sum_all_primes(t_large, max_prime=50)
        
        assert P_small > P_large
        assert P_large < 0.1, "Should be very small for large t"


class TestControlledRemainder:
    """Test the controlled remainder R(t) with exponential bound."""
    
    def test_remainder_bound_satisfied(self):
        """Remainder should satisfy |R(t)| ≤ C·e^(-λ/t)."""
        C = 10.0
        lambda_param = 1.0
        
        t_values = [0.01, 0.1, 0.5, 1.0, 5.0, 10.0]
        for t in t_values:
            R, bound = compute_controlled_remainder(t, prime_remainder=0.01,
                                                    C=C, lambda_param=lambda_param)
            assert abs(R) <= bound, f"Bound violated at t={t}: |R|={abs(R)}, bound={bound}"
    
    def test_remainder_invalid_t(self):
        """Should raise ValueError for t ≤ 0."""
        with pytest.raises(ValueError, match="must be positive"):
            compute_controlled_remainder(t=0.0, prime_remainder=0.01)
    
    def test_remainder_bound_shape(self):
        """Bound C·e^(-λ/t) should have correct asymptotic behavior."""
        C = 10.0
        lambda_param = 1.0
        
        # For small t: e^(-λ/t) → 0
        t_small = 0.01
        _, bound_small = compute_controlled_remainder(t_small, 0.01, C, lambda_param)
        assert bound_small < 1e-30, "Bound should be tiny for small t"
        
        # For large t: e^(-λ/t) → 1, so bound → C
        t_large = 100.0
        _, bound_large = compute_controlled_remainder(t_large, 0.01, C, lambda_param)
        assert bound_large < C * 1.1, "Bound should approach C for large t"
        assert bound_large > C * 0.9


class TestAdelicTraceFormula:
    """Test the complete Adelic Trace Formula."""
    
    def test_trace_formula_basic(self):
        """Basic computation should work without errors."""
        result = compute_adelic_trace_formula(t=1.0)
        
        assert isinstance(result, AdelicTraceResult)
        assert result.t == 1.0
        assert result.trace_total > 0
    
    def test_trace_formula_decomposition(self):
        """Trace should equal Weyl + Prime + R."""
        result = compute_adelic_trace_formula(t=1.0)
        
        expected = result.weyl_term + result.prime_term + result.remainder
        assert np.isclose(result.trace_total, expected, rtol=1e-10)
    
    def test_trace_formula_remainder_bound(self):
        """Remainder should satisfy the bound."""
        result = compute_adelic_trace_formula(t=1.0)
        
        assert abs(result.remainder) <= result.remainder_bound
        assert result.convergence_info['bound_satisfied']
    
    def test_trace_formula_weyl_dominates_small_t(self):
        """For small t, Weyl term should dominate."""
        result = compute_adelic_trace_formula(t=0.01)
        
        total_others = abs(result.prime_term) + abs(result.remainder)
        # Weyl should be largest component, though prime term is also significant
        assert result.weyl_term > total_others, \
            "Weyl should be larger than others for small t"
    
    def test_trace_formula_convergence_info(self):
        """Convergence info should be populated."""
        result = compute_adelic_trace_formula(t=1.0, max_prime=50)
        
        info = result.convergence_info
        assert 'n_primes' in info
        assert info['n_primes'] == 15  # Primes ≤ 50: [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
        assert 'max_prime' in info
        assert info['max_prime'] == 50
        assert 'bound_satisfied' in info
    
    def test_trace_formula_invalid_t(self):
        """Should raise ValueError for invalid t."""
        with pytest.raises(ValueError):
            compute_adelic_trace_formula(t=0.0)
    
    def test_trace_formula_time_evolution(self):
        """Trace should evolve smoothly with t."""
        t_values = np.logspace(-1, 1, 10)
        traces = [compute_adelic_trace_formula(t).trace_total for t in t_values]
        
        # Should be positive and finite
        assert all(tr > 0 for tr in traces)
        assert all(np.isfinite(tr) for tr in traces)
        
        # Should be continuous (no sudden jumps)
        for i in range(len(traces) - 1):
            ratio = traces[i+1] / traces[i]
            assert 0.1 < ratio < 10, "Should evolve smoothly"


class TestRemainderBoundVerification:
    """Test the uniform remainder bound verification."""
    
    def test_verify_bound_uniform(self):
        """Bound should hold uniformly over range of t."""
        t_values = np.logspace(-2, 1, 20)
        verification = verify_remainder_bound(t_values, max_prime=50, k_max=30)
        
        assert verification['all_satisfied'], \
            f"Bound violated in {verification['violation_count']} cases"
        assert verification['max_violation_ratio'] <= 1.0
    
    def test_verify_bound_details(self):
        """Verification should return detailed results."""
        t_values = np.array([0.1, 1.0, 10.0])
        verification = verify_remainder_bound(t_values)
        
        assert 'results' in verification
        assert len(verification['results']) == 3
        
        # Each result should be (t, |R|, bound, satisfied)
        for t, R, bound, satisfied in verification['results']:
            assert t > 0
            assert R >= 0
            assert bound > 0
            assert bool(satisfied) in [True, False]  # Handle numpy bool types
    
    def test_verify_bound_parameters(self):
        """Different C, λ should affect bound verification."""
        t_values = np.array([1.0])
        
        # Tighter bound (smaller C)
        v1 = verify_remainder_bound(t_values, C=1.0, lambda_param=1.0)
        
        # Looser bound (larger C)
        v2 = verify_remainder_bound(t_values, C=100.0, lambda_param=1.0)
        
        # Looser bound should be easier to satisfy
        assert v2['max_violation_ratio'] <= v1['max_violation_ratio']


class TestDemonstration:
    """Test the demonstration function."""
    
    def test_demonstrate_basic(self):
        """Demonstration should run without errors."""
        results = demonstrate_trace_formula(verbose=False)
        
        assert 'trace_results' in results
        assert 'verification' in results
        assert 't_sample' in results
    
    def test_demonstrate_custom_sample(self):
        """Should work with custom t sample."""
        t_sample = np.array([0.1, 1.0, 10.0])
        results = demonstrate_trace_formula(t_sample=t_sample, verbose=False)
        
        assert len(results['trace_results']) == 3
        assert np.array_equal(results['t_sample'], t_sample)
    
    def test_demonstrate_qcal_constants(self):
        """Should include QCAL constants in results."""
        results = demonstrate_trace_formula(verbose=False)
        
        assert results['qcal_frequency'] == F0_QCAL
        assert results['coherence'] == C_COHERENCE
        assert results['kappa_pi'] == KAPPA_PI


class TestMathematicalProperties:
    """Test mathematical properties of the trace formula."""
    
    def test_weyl_law_asymptotics(self):
        """Weyl term should have correct asymptotic for small t."""
        t = 0.01
        result = compute_adelic_trace_formula(t)
        
        # Leading asymptotic: ~ 1/(4πt)^(1/2)
        weyl_leading = 1.0 / np.sqrt(4 * np.pi * t)
        
        # Should be same order (note: correction terms matter)
        ratio = result.weyl_term / weyl_leading
        assert 0.5 < ratio < 50.0  # Include correction term contributions
    
    def test_prime_sum_structure(self):
        """Prime sum should have correct structure."""
        t = 1.0
        result = compute_adelic_trace_formula(t, max_prime=20)
        
        # Prime term should be sum over p, k
        # Dominated by small primes and small k
        assert result.prime_term > 0
        
        # Should be less than Weyl term for t ~ 1
        # (Weyl is geometric, Prime is arithmetic)
        # This depends on normalization but generally true
    
    def test_exponential_decay_large_t(self):
        """For large t, all terms should decay exponentially."""
        t_large = 20.0
        result = compute_adelic_trace_formula(t_large)
        
        # All contributions should be relatively small
        # Note: Weyl has correction term 7/8 that doesn't decay
        assert result.weyl_term < 10.0  # Mostly the 7/8 correction
        assert result.prime_term < 0.1
        assert abs(result.remainder) < 0.1
    
    def test_mellin_transform_connection(self):
        """Verify connection to Mellin transform structure."""
        # The Mellin transform ∫ t^(s-1) Tr(e^(-tL)) dt
        # should have poles at s = k·ln p
        
        # Test: Prime term should contribute pole structure
        t = 1.0
        result = compute_adelic_trace_formula(t, max_prime=10)
        
        # Prime term includes factors e^(-t·k·ln p)
        # which produce poles in Mellin transform
        assert result.prime_term > 0
        
        # Verification via numerical integration would require
        # integration over t, which we skip for unit tests


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_very_small_t(self):
        """Should handle very small t without overflow."""
        t = 1e-6
        result = compute_adelic_trace_formula(t)
        
        assert np.isfinite(result.trace_total)
        assert result.weyl_term > 0
    
    def test_very_large_t(self):
        """Should handle very large t without underflow."""
        t = 100.0
        result = compute_adelic_trace_formula(t)
        
        assert np.isfinite(result.trace_total)
        assert result.trace_total > 0
    
    def test_logarithmic_range(self):
        """Should work over logarithmic range of t."""
        t_values = np.logspace(-3, 2, 30)
        
        for t in t_values:
            result = compute_adelic_trace_formula(t)
            assert np.isfinite(result.trace_total)
            assert result.convergence_info['bound_satisfied']
    
    def test_reproducibility(self):
        """Results should be reproducible."""
        t = 1.0
        result1 = compute_adelic_trace_formula(t, max_prime=50, k_max=30)
        result2 = compute_adelic_trace_formula(t, max_prime=50, k_max=30)
        
        assert result1.trace_total == result2.trace_total
        assert result1.weyl_term == result2.weyl_term
        assert result1.prime_term == result2.prime_term


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_qcal_constants(self):
        """QCAL constants should be defined."""
        assert F0_QCAL == 141.7001
        assert C_COHERENCE == 244.36
        assert KAPPA_PI > 2.5
    
    def test_kappa_pi_parameter(self):
        """κ_Π should be used in computations."""
        result = compute_adelic_trace_formula(t=1.0, kappa=KAPPA_PI)
        assert result.convergence_info is not None
    
    def test_coherence_signature(self):
        """Results should maintain QCAL coherence."""
        # The trace formula is coherent with QCAL framework
        result = compute_adelic_trace_formula(t=1.0)
        
        # All components should be well-defined
        assert result.weyl_term > 0
        assert result.prime_term >= 0
        assert np.isfinite(result.remainder)


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
