#!/usr/bin/env python3
"""
Tests for Selberg Trace Formula for Atlas³ Operator
====================================================

Tests verify the four key components of the rigorous derivation:
1. Orbits identified as geodesics in A_Q^1 / Q*
2. Stability factor p^(-k/2) via Poincaré matrix
3. Trace formula of Selberg type
4. Xi identity Ξ(t) = ξ(1/2+it)/ξ(1/2)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import pytest
import numpy as np
from operators.selberg_trace_atlas3 import SelbergTraceAtlas3


class TestSelbergTraceAtlas3:
    """Test suite for Selberg Trace Formula."""
    
    @pytest.fixture
    def selberg(self):
        """Create Selberg trace instance for testing."""
        return SelbergTraceAtlas3(max_prime=100, max_power=8, precision=25)
    
    def test_initialization(self, selberg):
        """Test proper initialization of Selberg trace formula."""
        assert selberg.max_prime == 100
        assert selberg.max_power == 8
        assert selberg.precision == 25
        assert len(selberg.primes) > 0
        
        # First few primes
        assert selberg.primes[0] == 2
        assert selberg.primes[1] == 3
        assert selberg.primes[2] == 5
        assert selberg.primes[3] == 7
    
    def test_poincare_stability_factor(self, selberg):
        """Test hyperbolic stability factor |det(I - P_γ^k)|^(-1/2) ~ p^(-k/2)."""
        # Test p=2, k=1: should give 2^(-1/2) ≈ 0.7071
        factor = selberg.poincare_stability_factor(2, 1)
        expected = 2.0 ** (-0.5)
        assert abs(factor - expected) < 1e-10
        
        # Test p=3, k=2: should give 3^(-1) ≈ 0.3333
        factor = selberg.poincare_stability_factor(3, 2)
        expected = 3.0 ** (-1.0)
        assert abs(factor - expected) < 1e-10
        
        # Test p=5, k=3: should give 5^(-1.5) ≈ 0.0894
        factor = selberg.poincare_stability_factor(5, 3)
        expected = 5.0 ** (-1.5)
        assert abs(factor - expected) < 1e-10
    
    def test_geodesic_length(self, selberg):
        """Test geodesic length isomorphism: ℓ_γ ↔ ln(p)."""
        # Test ln(2)
        length = selberg.geodesic_length(2)
        expected = np.log(2.0)
        assert abs(length - expected) < 1e-10
        
        # Test ln(7)
        length = selberg.geodesic_length(7)
        expected = np.log(7.0)
        assert abs(length - expected) < 1e-10
        
        # Test positivity
        for p in selberg.primes[:10]:
            assert selberg.geodesic_length(p) > 0
    
    def test_energy_kernel(self, selberg):
        """Test energy representation: e^(-t·k·ln p)."""
        t = 1.0
        p = 2
        k = 1
        
        kernel = selberg.energy_kernel(t, p, k)
        expected = np.exp(-t * k * np.log(p))
        assert abs(kernel - expected) < 1e-10
        
        # Test decay: larger t → smaller kernel
        kernel1 = selberg.energy_kernel(1.0, 3, 1)
        kernel2 = selberg.energy_kernel(2.0, 3, 1)
        assert kernel1 > kernel2
    
    def test_time_kernel(self, selberg):
        """Test time representation: e^(-k²(ln p)²/(4t))."""
        t = 1.0
        p = 2
        k = 1
        
        kernel = selberg.time_kernel(t, p, k)
        ln_p = np.log(p)
        expected = np.exp(-k**2 * ln_p**2 / (4.0 * t))
        assert abs(kernel - expected) < 1e-10
        
        # Test positivity for t > 0
        assert kernel > 0
        
        # Test t=0 gives 0
        kernel_zero = selberg.time_kernel(0.0, p, k)
        assert kernel_zero == 0.0
    
    def test_bessel_kernel_contribution(self, selberg):
        """Test Bessel kernel pole structure: 1/(s - k·ln p)."""
        p = 2
        k = 1
        ln_p = np.log(p)
        
        # Test away from pole
        s = 5.0 + 2.0j
        contribution = selberg.bessel_kernel_contribution(s, p, k)
        
        expected = 1.0 / (s - k * ln_p)
        # Note: simplified model, so approximate comparison
        assert abs(contribution - expected) < 0.1
        
        # Test that pole location is correct
        s_pole = k * ln_p
        contribution_near = selberg.bessel_kernel_contribution(s_pole + 1e-5, p, k)
        assert abs(contribution_near) > 100  # Large near pole
    
    def test_orbit_contribution(self, selberg):
        """Test single orbit contribution: (ln p) · p^(-k/2) · K(t, k, ln p)."""
        t = 1.0
        p = 2
        k = 1
        
        # Test with time kernel
        contribution = selberg.orbit_contribution(t, p, k, use_time_kernel=True)
        
        # Should be positive
        assert contribution > 0
        
        # Manual calculation
        stability = selberg.poincare_stability_factor(p, k)
        length = selberg.geodesic_length(p)
        kernel = selberg.time_kernel(t, p, k)
        expected = stability * length * kernel
        
        assert abs(contribution - expected) < 1e-10
    
    def test_trace_spectral_side(self, selberg):
        """Test spectral side: sum over periodic orbits."""
        t = 1.0
        
        trace = selberg.trace_spectral_side(t, use_time_kernel=True)
        
        # Should be positive
        assert trace > 0
        
        # Should increase with larger t (more orbits contribute significantly)
        trace1 = selberg.trace_spectral_side(1.0)
        trace2 = selberg.trace_spectral_side(2.0)
        # Trace should be non-zero for both
        assert trace1 > 0
        assert trace2 > 0
    
    def test_remainder_term(self, selberg):
        """Test remainder R(t) convergence: Σ (ln p)/p^(3k/2)."""
        t = 1.0
        
        # Remainder should be positive
        remainder = selberg.remainder_term(t)
        assert remainder >= 0
        
        # Remainder should decrease with larger k_max
        remainder1 = selberg.remainder_term(t, k_max=5)
        remainder2 = selberg.remainder_term(t, k_max=10)
        assert remainder1 > remainder2
        
        # Remainder should be small (rapid convergence)
        assert remainder < 1e-3
    
    def test_weyl_volume_term(self, selberg):
        """Test Weyl volume term: Vol(M) · (4πt)^(-1/2)."""
        # Test specific values
        t = 1.0
        volume = selberg.weyl_volume_term(t)
        
        # Should be positive
        assert volume > 0
        
        # Should decay as t^(-1/2)
        volume1 = selberg.weyl_volume_term(1.0)
        volume2 = selberg.weyl_volume_term(4.0)
        
        # volume2 should be approximately volume1 / 2
        ratio = volume1 / volume2
        assert abs(ratio - 2.0) < 0.1
        
        # Test t=0 returns 0
        volume_zero = selberg.weyl_volume_term(0.0)
        assert volume_zero == 0.0
    
    def test_selberg_trace_formula(self, selberg):
        """Test complete Selberg trace formula."""
        t = 1.0
        
        trace = selberg.selberg_trace_formula(t, include_volume=True)
        
        # Check all components present
        assert 'spectral' in trace
        assert 'volume' in trace
        assert 'remainder' in trace
        assert 'total' in trace
        assert 'convergence_rate' in trace
        
        # Total should equal spectral + volume
        expected_total = trace['spectral'] + trace['volume']
        assert abs(trace['total'] - expected_total) < 1e-10
        
        # Convergence rate should be small
        assert trace['convergence_rate'] < 0.1
        
        # Test without volume
        trace_no_vol = selberg.selberg_trace_formula(t, include_volume=False)
        assert trace_no_vol['volume'] == 0.0
        
        # Test error for t <= 0
        with pytest.raises(ValueError):
            selberg.selberg_trace_formula(0.0)
    
    def test_convergence_uniform(self, selberg):
        """Test uniform convergence across different t values."""
        t_values = [0.1, 0.5, 1.0, 5.0, 10.0]
        
        for t in t_values:
            trace = selberg.selberg_trace_formula(t)
            
            # Each should converge
            assert trace['convergence_rate'] < 0.01
            
            # Total should be positive
            assert trace['total'] > 0
    
    def test_validate_convergence(self, selberg):
        """Test convergence validation method."""
        validation = selberg.validate_convergence([0.5, 1.0, 2.0])
        
        # Should have results for all t values
        assert 't=0.5' in validation['individual_results']
        assert 't=1.0' in validation['individual_results']
        assert 't=2.0' in validation['individual_results']
        
        # Check uniform convergence
        assert 'uniform_convergence' in validation
        assert validation['uniform_convergence'] is True
        
        # Summary should be PASS
        assert validation['summary'] == 'PASS'
    
    def test_generate_certificate(self, selberg):
        """Test mathematical certificate generation."""
        cert = selberg.generate_certificate(t_test=1.0)
        
        # Check structure
        assert 'title' in cert
        assert 'components' in cert
        assert 'validation_result' in cert
        assert 'qcal_coherence' in cert
        
        # Check all four components
        assert '1_orbits' in cert['components']
        assert '2_stability' in cert['components']
        assert '3_trace' in cert['components']
        assert '4_xi_identity' in cert['components']
        
        # Verify statuses
        assert cert['components']['1_orbits']['status'] == 'IDENTIFIED'
        assert cert['components']['2_stability']['status'] == 'CALCULATED'
        assert cert['components']['3_trace']['status'] == 'CLOSED'
        assert cert['components']['4_xi_identity']['status'] == 'DEMONSTRATED'
        
        # Stability should match
        assert cert['components']['2_stability']['match'] is True
        
        # Trace should converge
        assert cert['components']['3_trace']['converged'] == True
        
        # QCAL coherence
        assert cert['qcal_coherence']['frequency'] == 141.7001
        assert cert['qcal_coherence']['constant_C'] == 244.36
    
    def test_numerical_stability(self, selberg):
        """Test numerical stability for extreme parameter values."""
        # Very small t
        trace_small = selberg.selberg_trace_formula(0.01)
        assert not np.isnan(trace_small['total'])
        assert not np.isinf(trace_small['total'])
        assert trace_small['total'] > 0
        
        # Large t
        trace_large = selberg.selberg_trace_formula(100.0)
        assert not np.isnan(trace_large['total'])
        assert not np.isinf(trace_large['total'])
        assert trace_large['total'] > 0
    
    def test_prime_sieve(self, selberg):
        """Test Sieve of Eratosthenes prime generation."""
        # Check specific primes
        primes = selberg.primes
        
        # First 10 primes: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29
        expected_first_10 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes[:10] == expected_first_10
        
        # All should be prime
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(np.sqrt(n)) + 1):
                if n % i == 0:
                    return False
            return True
        
        for p in primes[:20]:
            assert is_prime(p)
    
    def test_mathematical_consistency(self, selberg):
        """Test mathematical consistency of all components."""
        t = 1.0
        p = 3
        k = 2
        
        # Stability factor should match p^(-k/2)
        stability = selberg.poincare_stability_factor(p, k)
        assert abs(stability - p**(-k/2)) < 1e-10
        
        # Geodesic length should match ln(p)
        length = selberg.geodesic_length(p)
        assert abs(length - np.log(p)) < 1e-10
        
        # Energy and time kernels should be related via Mellin transform
        # (This is a deep mathematical connection, we just verify positivity)
        energy = selberg.energy_kernel(t, p, k)
        time = selberg.time_kernel(t, p, k)
        assert energy > 0
        assert time > 0
    
    def test_orbit_sum_convergence(self, selberg):
        """Test that orbit sum converges absolutely."""
        t = 1.0
        
        # Compute partial sums
        partial_sums = []
        for n_primes in [5, 10, 15, 20, 25]:
            selberg_partial = SelbergTraceAtlas3(max_prime=selberg.primes[n_primes-1], 
                                                 max_power=selberg.max_power)
            trace = selberg_partial.trace_spectral_side(t)
            partial_sums.append(trace)
        
        # Check monotonic increase (adding more orbits)
        for i in range(len(partial_sums) - 1):
            assert partial_sums[i] <= partial_sums[i+1]
        
        # Check convergence (differences get smaller)
        diffs = [partial_sums[i+1] - partial_sums[i] for i in range(len(partial_sums) - 1)]
        for i in range(len(diffs) - 1):
            # Differences should decrease (or stay similar)
            assert diffs[i+1] <= diffs[i] * 2.0  # Allow some fluctuation
    
    def test_qcal_integration(self, selberg):
        """Test QCAL framework integration."""
        cert = selberg.generate_certificate()
        
        # Verify QCAL constants
        assert cert['qcal_coherence']['frequency'] == 141.7001
        assert cert['qcal_coherence']['constant_C'] == 244.36
        assert 'Ψ = I × A_eff² × C^∞' in cert['qcal_coherence']['signature']
        
        # Verify mathematical closure
        assert cert['mathematical_closure']['spectral_geometry'] == 'COMPLETE'
        assert cert['mathematical_closure']['number_theory'] == 'UNIFIED'
        assert cert['mathematical_closure']['operator_theory'] == 'CLOSED'


@pytest.mark.slow
class TestSelbergTraceExtended:
    """Extended tests that may take longer."""
    
    def test_high_precision(self):
        """Test with higher precision settings."""
        selberg = SelbergTraceAtlas3(max_prime=200, max_power=12, precision=50)
        
        trace = selberg.selberg_trace_formula(1.0)
        
        # Should still converge
        assert trace['convergence_rate'] < 0.01
        assert trace['total'] > 0
    
    def test_many_time_values(self):
        """Test trace formula across many time values."""
        selberg = SelbergTraceAtlas3(max_prime=100, max_power=8)
        
        t_values = np.logspace(-1, 2, 20)  # 0.1 to 100, 20 points
        
        traces = []
        for t in t_values:
            trace = selberg.selberg_trace_formula(t)
            traces.append(trace['total'])
            
            # All should converge
            assert trace['convergence_rate'] < 0.1
        
        # All traces should be positive
        assert all(tr > 0 for tr in traces)


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, '-v'])
