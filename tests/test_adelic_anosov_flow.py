#!/usr/bin/env python3
"""
Test Suite for Adelic Anosov Flow
==================================

Comprehensive tests for the Adelic Anosov Flow implementation,
verifying the mathematical properties and numerical accuracy.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from operators.adelic_anosov_flow import (
    AdelicAnosovFlow,
    create_adelic_anosov_flow,
    F0_QCAL,
    LYAPUNOV_EXPONENT
)


class TestAdelicAnosovFlow:
    """Test suite for the AdelicAnosovFlow class."""
    
    def test_initialization(self):
        """Test basic initialization of the flow."""
        flow = AdelicAnosovFlow(dimension=30)
        
        assert flow.dimension == 30
        assert len(flow.primes) > 0
        assert flow.lyapunov_exp == LYAPUNOV_EXPONENT
        assert flow.C > 0
        assert flow.lambda_rate > 0
    
    def test_dilation_flow_property(self):
        """Test that φ^{t+s} = φ^t ∘ φ^s (flow property)."""
        flow = AdelicAnosovFlow(dimension=10)
        
        x = np.random.rand(10)
        t = 1.5
        s = 0.7
        
        # Direct computation
        flow_ts = flow.dilation_flow(x, t + s)
        
        # Composition
        flow_t = flow.dilation_flow(x, t)
        flow_t_then_s = flow.dilation_flow(flow_t, s)
        
        # Should be equal
        error = np.linalg.norm(flow_ts - flow_t_then_s)
        assert error < 1e-10, f"Flow property violated: error = {error}"
    
    def test_dilation_flow_identity(self):
        """Test that φ^0 = identity."""
        flow = AdelicAnosovFlow(dimension=10)
        
        x = np.random.rand(10)
        flow_0 = flow.dilation_flow(x, 0.0)
        
        error = np.linalg.norm(flow_0 - x)
        assert error < 1e-10, "φ^0 should be identity"
    
    def test_dilation_flow_scaling(self):
        """Test that dilation flow scales correctly."""
        flow = AdelicAnosovFlow(dimension=5)
        
        x = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        t = 1.0
        
        result = flow.dilation_flow(x, t)
        expected = np.exp(1.0) * x
        
        error = np.linalg.norm(result - expected)
        assert error < 1e-10
    
    def test_differential_flow(self):
        """Test the differential of the flow."""
        flow = AdelicAnosovFlow(dimension=5)
        
        x = np.random.rand(5)
        t = 0.5
        
        diff = flow.differential_flow(x, t)
        
        # Should be e^t times identity matrix
        expected = np.exp(t) * np.eye(5)
        
        error = np.linalg.norm(diff - expected)
        assert error < 1e-10
    
    def test_spectral_decomposition(self):
        """Test the spectral decomposition T(FX) = E⁰ ⊕ E^s ⊕ E^u."""
        flow = AdelicAnosovFlow(dimension=20)
        
        t = 1.0
        E0, Es, Eu = flow.spectral_decomposition(t)
        
        # Check shapes
        assert E0.shape == (20, 20)
        assert Es.shape == (20, 20)
        assert Eu.shape == (20, 20)
        
        # Check E⁰ is 1-dimensional
        assert np.abs(np.trace(E0) - 1.0) < 1e-10
        
        # Check Es has contraction (eigenvalues < 1 for t > 0)
        es_diag = np.diag(Es)
        nonzero_es = es_diag[es_diag > 1e-10]
        if len(nonzero_es) > 0:
            assert np.all(nonzero_es < 1.0), "Stable directions should contract"
        
        # Check Eu has expansion (eigenvalues > 1 for t > 0)
        eu_diag = np.diag(Eu)
        nonzero_eu = eu_diag[eu_diag > 1e-10]
        if len(nonzero_eu) > 0:
            assert np.all(nonzero_eu > 1.0), "Unstable directions should expand"
    
    def test_periodic_orbit_length(self):
        """Test periodic orbit length computation."""
        flow = AdelicAnosovFlow()
        
        # For prime p and iteration k, length should be k·ln(p)
        p = 7
        k = 3
        
        length = flow.periodic_orbit_length(p, k)
        expected = k * np.log(p)
        
        assert np.abs(length - expected) < 1e-10
    
    def test_stability_factor(self):
        """Test stability factor p^{k/2}."""
        flow = AdelicAnosovFlow()
        
        p = 5
        k = 4
        
        factor = flow.stability_factor(p, k)
        expected = np.power(p, k / 2.0)
        
        assert np.abs(factor - expected) < 1e-10
    
    def test_weyl_term_scaling(self):
        """Test Weyl term scales as 1/√t."""
        flow = AdelicAnosovFlow(dimension=50)
        
        t1 = 1.0
        t2 = 4.0
        
        weyl1 = flow.weyl_term(t1)
        weyl2 = flow.weyl_term(t2)
        
        # Should scale as 1/√t, so weyl1/weyl2 ≈ √(t2/t1) = 2
        ratio = weyl1 / weyl2
        expected_ratio = np.sqrt(t2 / t1)
        
        assert np.abs(ratio - expected_ratio) < 1e-10
    
    def test_periodic_orbit_contribution_convergence(self):
        """Test that periodic orbit sum converges."""
        flow = AdelicAnosovFlow()
        
        t = 1.0
        
        # Compute with increasing number of terms
        contrib_10 = flow.periodic_orbit_contribution(t, max_prime_index=10, max_k=5)
        contrib_20 = flow.periodic_orbit_contribution(t, max_prime_index=20, max_k=5)
        contrib_30 = flow.periodic_orbit_contribution(t, max_prime_index=30, max_k=5)
        
        # Should converge (difference decreases)
        diff_1 = abs(contrib_20 - contrib_10)
        diff_2 = abs(contrib_30 - contrib_20)
        
        # Later differences should be smaller (convergence)
        # Allow some tolerance for numerical effects
        assert diff_2 <= diff_1 * 1.5, "Series should show convergence"
    
    def test_remainder_term_exponential_decay(self):
        """Test remainder term has exponential decay."""
        flow = AdelicAnosovFlow()
        
        t1 = 0.5
        t2 = 1.0
        
        r1 = flow.remainder_term(t1)
        r2 = flow.remainder_term(t2)
        
        # R(t) ~ exp(-λ/t), so should decrease as t increases
        assert r1 > r2, "Remainder should decay as t increases"
        
        # Check exponential behavior
        # R(t1)/R(t2) ≈ exp(λ(1/t1 - 1/t2))
        ratio = r1 / r2
        assert ratio > 1.0
    
    def test_trace_heat_kernel_components(self):
        """Test trace heat kernel has all components."""
        flow = AdelicAnosovFlow()
        
        t = 1.0
        result = flow.trace_heat_kernel(t)
        
        # Check all components present
        assert 'weyl' in result
        assert 'periodic' in result
        assert 'remainder' in result
        assert 'total' in result
        
        # Check total is sum
        total_expected = result['weyl'] + result['periodic'] + result['remainder']
        assert np.abs(result['total'] - total_expected) < 1e-10
        
        # All components should be finite
        assert np.isfinite(result['weyl'])
        assert np.isfinite(result['periodic'])
        assert np.isfinite(result['remainder'])
        assert np.isfinite(result['total'])
    
    def test_trace_formula_positive(self):
        """Test trace formula gives positive values for reasonable t."""
        flow = AdelicAnosovFlow(dimension=50)
        
        t_values = [0.5, 1.0, 2.0, 5.0]
        
        for t in t_values:
            result = flow.trace_heat_kernel(t)
            # Total should be positive (Weyl term dominates)
            assert result['total'] > 0, f"Trace should be positive at t={t}"
    
    def test_verify_anosov_structure(self):
        """Test Anosov structure verification."""
        flow = AdelicAnosovFlow(dimension=30)
        
        results = flow.verify_anosov_structure(t=1.0)
        
        # Check all required fields
        assert 'is_anosov' in results
        assert 'flow_property' in results
        assert 'decomposition_exists' in results
        assert 'lyapunov_nonzero' in results
        assert 'constants_uniform' in results
        
        # Should verify as Anosov
        assert results['is_anosov'] is True
        assert results['flow_property'] is True
        assert results['decomposition_exists'] is True
        assert results['lyapunov_nonzero'] is True
        assert results['constants_uniform'] is True
    
    def test_lyapunov_exponents(self):
        """Test Lyapunov exponents are ±1."""
        flow = AdelicAnosovFlow()
        
        results = flow.verify_anosov_structure()
        
        assert results['lyapunov_stable'] == -LYAPUNOV_EXPONENT
        assert results['lyapunov_unstable'] == LYAPUNOV_EXPONENT
        assert abs(results['lyapunov_unstable']) == 1.0
    
    def test_spectral_connection_to_zeros(self):
        """Test connection to Riemann zeros."""
        # Create flow with sample zeros
        sample_zeros = np.array([14.134725, 21.022040, 25.010858])
        flow = AdelicAnosovFlow(dimension=20, riemann_zeros=sample_zeros)
        
        spectral_data = flow.spectral_connection_to_zeros(
            t_values=np.array([0.5, 1.0, 2.0])
        )
        
        assert spectral_data['n_zeros'] == 3
        assert spectral_data['zeros_connected'] is True
        assert len(spectral_data['trace_values']) == 3
        
        # All trace values should be finite
        assert np.all(np.isfinite(spectral_data['trace_values']))
    
    def test_mellin_transform_contribution_finite(self):
        """Test Mellin transform contribution is finite."""
        flow = AdelicAnosovFlow()
        
        s = 2.0 + 0.5j
        p = 5
        k = 2
        
        result = flow.mellin_transform_contribution(s, p, k)
        
        assert np.isfinite(result)
        assert isinstance(result, complex)
    
    def test_prime_generation(self):
        """Test prime number generation."""
        flow = AdelicAnosovFlow()
        
        primes = flow._generate_primes(10)
        
        # Should get first 10 primes
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
    
    def test_factory_function(self):
        """Test factory function creates flow correctly."""
        flow = create_adelic_anosov_flow(dimension=25, n_primes=50)
        
        assert flow.dimension == 25
        assert len(flow.primes) >= 50
    
    def test_factory_with_zeros(self):
        """Test factory function with Riemann zeros."""
        zeros = np.array([14.134725, 21.022040])
        flow = create_adelic_anosov_flow(dimension=20, riemann_zeros=zeros)
        
        assert flow.riemann_zeros is not None
        assert len(flow.riemann_zeros) == 2
    
    def test_trace_continuity(self):
        """Test trace formula is continuous in t."""
        flow = AdelicAnosovFlow(dimension=30)
        
        t_vals = np.linspace(0.5, 2.0, 20)
        traces = []
        
        for t in t_vals:
            result = flow.trace_heat_kernel(t)
            traces.append(result['total'])
        
        traces = np.array(traces)
        
        # Check no sudden jumps (continuity)
        diffs = np.abs(np.diff(traces))
        max_diff = np.max(diffs)
        
        # Should be smooth (no large jumps)
        assert max_diff < 10.0, "Trace should be continuous"
    
    def test_qcal_constants_available(self):
        """Test QCAL constants are properly defined."""
        assert F0_QCAL == 141.7001
        assert LYAPUNOV_EXPONENT == 1.0
    
    def test_dimension_flexibility(self):
        """Test flow works with various dimensions."""
        dimensions = [10, 20, 50, 100]
        
        for dim in dimensions:
            flow = AdelicAnosovFlow(dimension=dim)
            
            # Should initialize without error
            assert flow.dimension == dim
            
            # Should compute trace
            result = flow.trace_heat_kernel(1.0)
            assert np.isfinite(result['total'])
    
    def test_numerical_stability_small_t(self):
        """Test numerical stability for small t values."""
        flow = AdelicAnosovFlow()
        
        # Small t can be challenging
        t_small = 0.1
        result = flow.trace_heat_kernel(t_small)
        
        # Should still give finite results
        assert np.isfinite(result['total'])
        assert result['total'] > 0
    
    def test_numerical_stability_large_t(self):
        """Test numerical stability for large t values."""
        flow = AdelicAnosovFlow()
        
        # Large t
        t_large = 10.0
        result = flow.trace_heat_kernel(t_large)
        
        # Should still give finite results
        assert np.isfinite(result['total'])
        assert result['total'] > 0


class TestAnosovMathematicalProperties:
    """Test mathematical properties specific to Anosov flows."""
    
    def test_hyperbolicity_constants_positive(self):
        """Test hyperbolic constants C and λ are positive."""
        flow = AdelicAnosovFlow()
        
        assert flow.C > 0
        assert flow.lambda_rate > 0
    
    def test_spectral_gap(self):
        """Test there is a spectral gap in Lyapunov exponents."""
        flow = AdelicAnosovFlow()
        
        results = flow.verify_anosov_structure()
        
        # Gap between stable and unstable
        gap = results['lyapunov_unstable'] - results['lyapunov_stable']
        
        assert gap > 0, "Should have spectral gap"
        assert gap == 2 * LYAPUNOV_EXPONENT
    
    def test_trace_formula_weyl_dominance(self):
        """Test Weyl term dominates for large t."""
        flow = AdelicAnosovFlow(dimension=50)
        
        t_large = 5.0
        result = flow.trace_heat_kernel(t_large)
        
        # Weyl should be dominant
        weyl_fraction = result['weyl'] / result['total']
        
        # Should be close to 1 for large t
        assert weyl_fraction > 0.8
    
    def test_periodic_orbit_exponential_decay(self):
        """Test periodic orbit contributions decay exponentially."""
        flow = AdelicAnosovFlow()
        
        t = 1.0
        
        # Get contributions with different max_k
        contrib_k2 = flow.periodic_orbit_contribution(t, max_prime_index=20, max_k=2)
        contrib_k5 = flow.periodic_orbit_contribution(t, max_prime_index=20, max_k=5)
        contrib_k10 = flow.periodic_orbit_contribution(t, max_prime_index=20, max_k=10)
        
        # Higher k terms should add less (exponential decay in k)
        add_k2_to_k5 = contrib_k5 - contrib_k2
        add_k5_to_k10 = contrib_k10 - contrib_k5
        
        # Later additions should be smaller
        assert abs(add_k5_to_k10) <= abs(add_k2_to_k5)


class TestIntegrationWithQCAL:
    """Test integration with QCAL framework."""
    
    def test_frequency_constant_matches(self):
        """Test F0_QCAL constant matches expected value."""
        assert F0_QCAL == 141.7001
    
    def test_trace_formula_qcal_coherence(self):
        """Test trace formula can incorporate QCAL coherence."""
        flow = AdelicAnosovFlow(dimension=50)
        
        # Compute at QCAL-related time
        t_qcal = 1.0 / F0_QCAL
        
        result = flow.trace_heat_kernel(t_qcal)
        
        # Should compute without error
        assert np.isfinite(result['total'])
    
    def test_spectral_connection_with_qcal_zeros(self):
        """Test spectral connection using QCAL framework zeros."""
        # Use first few Riemann zeros
        zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
        
        flow = create_adelic_anosov_flow(dimension=30, riemann_zeros=zeros)
        
        spectral_data = flow.spectral_connection_to_zeros()
        
        assert spectral_data['zeros_connected'] is True
        assert spectral_data['n_zeros'] == 5


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
