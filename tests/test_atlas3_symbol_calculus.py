#!/usr/bin/env python3
"""
Tests for Atlas³ Pseudodifferential Symbol Calculus

This module tests the symbol calculus framework that derives:
    1. Weyl's law from phase space volume
    2. Trace formula from Hamiltonian flow fixed points
    3. Coupling constant κ from symbol expansion

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import sys
import os
import pytest
import numpy as np
from typing import Dict, Any

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from atlas3_symbol_calculus import (
    PseudodifferentialSymbol,
    WeylLawCalculator,
    HamiltonianFlow,
    TraceFormulaCalculator,
    KappaDerivation,
    validate_weyl_law_derivation,
    KAPPA_PI
)


class TestPseudodifferentialSymbol:
    """Tests for pseudodifferential symbol class."""
    
    def test_symbol_initialization(self):
        """Test symbol initialization with default parameters."""
        symbol = PseudodifferentialSymbol()
        
        assert symbol.V_amp == 12650.0
        assert symbol.beta_0 == 0.0
        assert symbol.use_principal == False
    
    def test_potential_function(self):
        """Test quasiperiodic potential V_Atlas(t)."""
        symbol = PseudodifferentialSymbol(V_amp=100.0)
        
        t = np.array([0.0, np.pi/4, np.pi/2])
        V = symbol.V_atlas(t)
        
        # Check periodicity and amplitude
        assert np.abs(V[0] - 100.0) < 1e-10
        assert np.max(np.abs(V)) <= 100.0
        assert np.min(V) >= -100.0
    
    def test_beta_function(self):
        """Test PT-breaking function β(t)."""
        symbol = PseudodifferentialSymbol(beta_0=2.0)
        
        t = np.array([0.0, np.pi, 2*np.pi])
        beta = symbol.beta_function(t)
        
        # Check parity
        assert np.abs(beta[0] - 2.0) < 1e-10
        assert np.abs(beta[1] + 2.0) < 1e-10
        assert np.abs(beta[2] - 2.0) < 1e-10
    
    def test_total_symbol_hermitian(self):
        """Test total symbol is real when β₀ = 0."""
        symbol = PseudodifferentialSymbol(V_amp=100.0, beta_0=0.0)
        
        t, p = 2.0, 3.0
        sigma = symbol.total_symbol(t, p)
        
        # Should be real
        assert np.abs(sigma.imag) < 1e-10
        
        # Check value: p² + V_Atlas(t)
        expected = p**2 + symbol.V_atlas(t)
        assert np.abs(sigma.real - expected) < 1e-10
    
    def test_total_symbol_pt_breaking(self):
        """Test total symbol has imaginary part when β₀ ≠ 0."""
        symbol = PseudodifferentialSymbol(V_amp=100.0, beta_0=2.0)
        
        t, p = 0.0, 3.0  # t=0 gives β(t)=2.0
        sigma = symbol.total_symbol(t, p)
        
        # Should have imaginary part
        assert np.abs(sigma.imag) > 1e-6
        
        # Check imaginary part: β(t)·p
        expected_imag = 2.0 * 3.0
        assert np.abs(sigma.imag - expected_imag) < 1e-10
    
    def test_principal_symbol(self):
        """Test principal symbol σ₀(t,p) = t·p."""
        symbol = PseudodifferentialSymbol()
        
        t, p = 2.5, 3.7
        sigma0 = symbol.principal_symbol(t, p)
        
        expected = t * p
        assert np.abs(sigma0 - expected) < 1e-10
    
    def test_symbol_selection(self):
        """Test symbol selection based on use_principal flag."""
        # Total symbol
        symbol_total = PseudodifferentialSymbol(use_principal=False)
        sig_total = symbol_total.symbol(2.0, 3.0)
        
        # Principal symbol
        symbol_principal = PseudodifferentialSymbol(use_principal=True)
        sig_principal = symbol_principal.symbol(2.0, 3.0)
        
        # They should be different (unless β₀=0 and V=0)
        assert sig_principal == 6.0
        assert sig_total != sig_principal


class TestWeylLawCalculator:
    """Tests for Weyl law derivation from symbol."""
    
    def test_phase_space_volume_positive(self):
        """Test phase space volume is non-negative."""
        symbol = PseudodifferentialSymbol(use_principal=True)
        weyl = WeylLawCalculator(symbol)
        
        T_values = [1.0, 5.0, 10.0, 50.0, 100.0]
        
        for T in T_values:
            vol = weyl.phase_space_volume(T)
            assert vol >= 0.0
    
    def test_phase_space_volume_monotonic(self):
        """Test phase space volume increases with T."""
        symbol = PseudodifferentialSymbol(use_principal=True)
        weyl = WeylLawCalculator(symbol)
        
        T_values = np.linspace(2.0, 100.0, 20)
        volumes = [weyl.phase_space_volume(T) for T in T_values]
        
        # Should be monotonically increasing
        for i in range(len(volumes) - 1):
            assert volumes[i+1] >= volumes[i]
    
    def test_counting_function_normalization(self):
        """Test counting function N(T) = Vol/(2π)."""
        symbol = PseudodifferentialSymbol(use_principal=True)
        weyl = WeylLawCalculator(symbol)
        
        T = 50.0
        vol = weyl.phase_space_volume(T)
        N = weyl.counting_function(T)
        
        expected = vol / (2.0 * np.pi)
        assert np.abs(N - expected) < 1e-10
    
    def test_weyl_asymptotic_large_T(self):
        """Test asymptotic behavior N(T) ~ (T/π)ln(T) for large T."""
        symbol = PseudodifferentialSymbol(use_principal=True)
        weyl = WeylLawCalculator(symbol)
        
        # For large T, the ratio N(T) / ((T/π)ln(T)) should approach 1
        T_large = 1000.0
        N_exact = weyl.counting_function(T_large)
        N_asymp = weyl.weyl_asymptotic(T_large)
        
        # Relative error should be small for large T
        relative_error = np.abs(N_exact - N_asymp) / N_asymp
        assert relative_error < 0.6  # Allow 60% error for this range
    
    def test_riemann_von_mangoldt_zeros(self):
        """Test Riemann-von Mangoldt formula for known T values."""
        symbol = PseudodifferentialSymbol(use_principal=True)
        weyl = WeylLawCalculator(symbol)
        
        # For T = 50, there are approximately 10 zeros
        T = 50.0
        N = weyl.riemann_von_mangoldt(T)
        
        # Should be positive and reasonable
        assert N > 0
        assert N < 100  # Sanity check
    
    def test_weyl_law_validation(self):
        """Test complete Weyl law validation."""
        result = validate_weyl_law_derivation(T_max=50.0, num_points=10)
        
        # Check result structure
        assert 'T_values' in result
        assert 'N_exact' in result
        assert 'N_asymptotic' in result
        assert 'mean_error_asymptotic' in result
        assert 'convergence_confirmed' in result
        
        # All N values should be non-negative
        assert np.all(result['N_exact'] >= 0)
        assert np.all(result['N_asymptotic'] >= 0)


class TestHamiltonianFlow:
    """Tests for Hamiltonian flow and fixed points."""
    
    def test_flow_preserves_product(self):
        """Test flow preserves t·p (symplectic structure)."""
        flow = HamiltonianFlow()
        
        t0, p0 = 2.0, 3.0
        product_initial = t0 * p0
        
        tau_values = [0.1, 0.5, 1.0, 2.0, 5.0]
        
        for tau in tau_values:
            t_tau, p_tau = flow.flow(t0, p0, tau)
            product_final = t_tau * p_tau
            
            # Product should be preserved
            assert np.abs(product_final - product_initial) < 1e-10
    
    def test_flow_dilation_property(self):
        """Test flow has correct dilation form."""
        flow = HamiltonianFlow()
        
        t0, p0 = 1.5, 2.5
        tau = 1.3
        
        t_tau, p_tau = flow.flow(t0, p0, tau)
        
        # Check explicit form
        expected_t = t0 * np.exp(tau)
        expected_p = p0 * np.exp(-tau)
        
        assert np.abs(t_tau - expected_t) < 1e-10
        assert np.abs(p_tau - expected_p) < 1e-10
    
    def test_flow_identity_at_zero(self):
        """Test flow is identity at τ=0."""
        flow = HamiltonianFlow()
        
        t0, p0 = 2.7, 3.9
        t_tau, p_tau = flow.flow(t0, p0, 0.0)
        
        assert np.abs(t_tau - t0) < 1e-10
        assert np.abs(p_tau - p0) < 1e-10
    
    def test_fixed_point_condition(self):
        """Test fixed point condition e^τ = q."""
        flow = HamiltonianFlow()
        
        tau_values = [0.0, 1.0, np.log(2), np.log(3), np.log(5)]
        
        for tau in tau_values:
            exp_tau = flow.fixed_point_condition(tau)
            assert np.abs(exp_tau - np.exp(tau)) < 1e-10
    
    def test_prime_orbit_times(self):
        """Test prime orbit times τ = k·ln(p)."""
        flow = HamiltonianFlow()
        
        p_prime = 5
        k_max = 5
        
        orbit_times = flow.prime_orbit_times(p_prime, k_max)
        
        # Check length
        assert len(orbit_times) == k_max
        
        # Check values
        for k, tau in enumerate(orbit_times, start=1):
            expected = k * np.log(p_prime)
            assert np.abs(tau - expected) < 1e-10


class TestTraceFormulaCalculator:
    """Tests for trace formula from fixed points."""
    
    def test_van_vleck_determinant_positive(self):
        """Test Van-Vleck determinant is positive."""
        trace_calc = TraceFormulaCalculator()
        
        t, p = 2.0, 3.0
        tau_values = [0.5, 1.0, 2.0, 5.0]
        
        for tau in tau_values:
            det = trace_calc.van_vleck_determinant(t, p, tau)
            assert det > 0
    
    def test_van_vleck_determinant_scaling(self):
        """Test Van-Vleck determinant scales as 1/√(e^τ)."""
        trace_calc = TraceFormulaCalculator()
        
        t, p = 1.0, 1.0
        tau = 2.0
        
        det = trace_calc.van_vleck_determinant(t, p, tau)
        expected = 1.0 / np.sqrt(np.exp(tau))
        
        assert np.abs(det - expected) < 1e-10
    
    def test_prime_orbit_contribution_decay(self):
        """Test prime orbit contributions decay with k."""
        trace_calc = TraceFormulaCalculator()
        
        p_prime = 3
        tau = 1.0
        
        # Contributions should decrease with k
        contrib_k1 = trace_calc.prime_orbit_contribution(p_prime, 1, tau)
        contrib_k2 = trace_calc.prime_orbit_contribution(p_prime, 2, tau)
        contrib_k3 = trace_calc.prime_orbit_contribution(p_prime, 3, tau)
        
        assert np.abs(contrib_k1) > np.abs(contrib_k2)
        assert np.abs(contrib_k2) > np.abs(contrib_k3)
    
    def test_trace_approximation_convergence(self):
        """Test trace approximation converges with more primes."""
        trace_calc = TraceFormulaCalculator()
        
        tau = 0.5
        
        # Trace with few primes
        trace_small = trace_calc.trace_approximation(tau, primes=[2, 3], k_max=5)
        
        # Trace with more primes
        trace_large = trace_calc.trace_approximation(tau, primes=[2, 3, 5, 7, 11], k_max=5)
        
        # Magnitude should increase
        assert np.abs(trace_large) > np.abs(trace_small)
    
    def test_trace_real_positive(self):
        """Test trace is approximately real and positive."""
        trace_calc = TraceFormulaCalculator()
        
        tau = 1.0
        trace = trace_calc.trace_approximation(tau, primes=[2, 3, 5, 7], k_max=10)
        
        # Should be primarily real
        assert np.abs(trace.imag) < np.abs(trace.real) * 0.01
        
        # Should be positive
        assert trace.real > 0


class TestKappaDerivation:
    """Tests for κ derivation from symbol expansion."""
    
    def test_hermiticity_condition_returns_kappa_pi(self):
        """Test hermiticity condition returns κ_Π."""
        symbol = PseudodifferentialSymbol()
        kappa_calc = KappaDerivation(symbol)
        
        kappa = kappa_calc.hermiticity_condition(2.0)
        
        assert np.abs(kappa - KAPPA_PI) < 1e-6
    
    def test_maslov_index_correction(self):
        """Test Maslov index gives 1/4 correction."""
        symbol = PseudodifferentialSymbol()
        kappa_calc = KappaDerivation(symbol)
        
        maslov = kappa_calc.maslov_index_correction()
        
        assert np.abs(maslov - 0.25) < 1e-10
    
    def test_pt_compensation_scaling(self):
        """Test PT compensation parameter scales with √V_amp."""
        symbol = PseudodifferentialSymbol()
        kappa_calc = KappaDerivation(symbol)
        
        # Reference value
        V_ref = 12650.0
        kappa_ref = kappa_calc.pt_compensation_parameter(V_ref)
        assert np.abs(kappa_ref - KAPPA_PI) < 1e-6
        
        # Double the potential
        V_double = 2 * V_ref
        kappa_double = kappa_calc.pt_compensation_parameter(V_double)
        
        # Should scale as √2
        expected_ratio = np.sqrt(2)
        actual_ratio = kappa_double / kappa_ref
        
        assert np.abs(actual_ratio - expected_ratio) < 1e-6
    
    def test_kappa_positive(self):
        """Test all κ derivations are positive."""
        symbol = PseudodifferentialSymbol(V_amp=12650.0, beta_0=2.0)
        kappa_calc = KappaDerivation(symbol)
        
        kappa_hermit = kappa_calc.hermiticity_condition(2.0)
        kappa_maslov = kappa_calc.maslov_index_correction()
        kappa_pt = kappa_calc.pt_compensation_parameter(12650.0)
        
        assert kappa_hermit > 0
        assert kappa_maslov > 0
        assert kappa_pt > 0


class TestIntegration:
    """Integration tests for complete symbol calculus framework."""
    
    def test_symbol_to_weyl_law_pipeline(self):
        """Test complete pipeline from symbol to Weyl law."""
        # Create symbol
        symbol = PseudodifferentialSymbol(use_principal=True)
        
        # Create Weyl calculator
        weyl = WeylLawCalculator(symbol)
        
        # Compute counting function
        T = 100.0
        N = weyl.counting_function(T)
        
        # Should be positive and reasonable
        assert N > 0
        assert N < 1000
    
    def test_flow_to_trace_pipeline(self):
        """Test pipeline from Hamiltonian flow to trace formula."""
        # Create flow
        flow = HamiltonianFlow()
        
        # Get prime orbit times
        primes = [2, 3, 5, 7]
        orbit_times_dict = {}
        
        for p in primes:
            orbit_times_dict[p] = flow.prime_orbit_times(p, k_max=5)
        
        # Create trace calculator
        trace_calc = TraceFormulaCalculator()
        
        # Compute trace
        tau = 0.5
        trace = trace_calc.trace_approximation(tau, primes=primes, k_max=5)
        
        # Trace should be finite
        assert np.isfinite(trace)
        assert np.abs(trace) < 1000
    
    def test_symbol_consistency(self):
        """Test consistency between total and principal symbols."""
        # For β₀ = 0 and V = 0, total symbol should reduce to p²
        symbol = PseudodifferentialSymbol(V_amp=0.0, beta_0=0.0)
        
        t, p = 2.0, 3.0
        sigma_total = symbol.total_symbol(t, p)
        
        # Should equal p²
        assert np.abs(sigma_total - p**2) < 1e-10
    
    def test_framework_numerical_stability(self):
        """Test framework is numerically stable."""
        # Test with various parameter combinations
        test_configs = [
            {'V_amp': 100.0, 'beta_0': 0.0},
            {'V_amp': 12650.0, 'beta_0': 1.0},
            {'V_amp': 12650.0, 'beta_0': 2.57},
            {'V_amp': 50000.0, 'beta_0': 0.5},
        ]
        
        for config in test_configs:
            symbol = PseudodifferentialSymbol(**config)
            weyl = WeylLawCalculator(symbol)
            kappa_calc = KappaDerivation(symbol)
            
            # All computations should be finite
            N = weyl.counting_function(50.0)
            kappa = kappa_calc.pt_compensation_parameter(config['V_amp'])
            
            assert np.isfinite(N)
            assert np.isfinite(kappa)
            assert N >= 0
            assert kappa > 0


def test_demonstration_runs():
    """Test that the demonstration function runs without errors."""
    from atlas3_symbol_calculus import demonstrate_symbol_calculus
    
    # Should run without raising exceptions
    demonstrate_symbol_calculus()


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
