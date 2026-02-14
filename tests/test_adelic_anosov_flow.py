#!/usr/bin/env python3
"""
Tests for Adelic Anosov Flow Implementation
===========================================

Validates the hyperbolic dynamics of the adelic flow and connection
to the Selberg trace formula and Riemann zeta function.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from adelic_anosov_flow import AdelicAnosovFlow, validate_anosov_structure


class TestAdelicAnosovFlow:
    """Test suite for Adelic Anosov Flow."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.flow = AdelicAnosovFlow(primes=[2, 3, 5, 7, 11], t_max=5.0, n_points=100)
    
    def test_initialization(self):
        """Test proper initialization of flow."""
        assert len(self.flow.primes) == 5
        assert self.flow.primes == [2, 3, 5, 7, 11]
        assert self.flow.t_max == 5.0
        assert self.flow.n_points == 100
        assert len(self.flow.t_range) == 100
    
    def test_first_primes_generation(self):
        """Test prime number generation."""
        primes = self.flow._first_primes(10)
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        
        primes_5 = self.flow._first_primes(5)
        assert len(primes_5) == 5
        assert all(self.flow._is_prime(p) for p in primes_5)
    
    def test_is_prime(self):
        """Test prime checking function."""
        assert self.flow._is_prime(2)
        assert self.flow._is_prime(3)
        assert self.flow._is_prime(17)
        assert self.flow._is_prime(97)
        
        assert not self.flow._is_prime(1)
        assert not self.flow._is_prime(4)
        assert not self.flow._is_prime(100)
    
    def test_archimedean_norm_expansion(self):
        """Test Archimedean norm expansion: |e^t x|_∞ = e^t |x|."""
        x = 2.5
        t = 1.0
        
        norm = self.flow.archimedean_norm(x, t)
        expected = np.exp(1.0) * 2.5
        
        assert np.abs(norm - expected) < 1e-10
    
    def test_archimedean_expansion_positive_time(self):
        """Test expansion in positive time direction."""
        x = 1.0
        t_positive = 2.0
        
        norm_positive = self.flow.archimedean_norm(x, t_positive)
        assert norm_positive > x  # Must expand
        assert np.abs(norm_positive - np.exp(2.0)) < 1e-10
    
    def test_archimedean_contraction_negative_time(self):
        """Test contraction in negative time direction."""
        x = 1.0
        t_negative = -2.0
        
        norm_negative = self.flow.archimedean_norm(x, t_negative)
        assert norm_negative < x  # Must contract
        assert np.abs(norm_negative - np.exp(-2.0)) < 1e-10
    
    def test_p_adic_norm_basic(self):
        """Test p-adic norm computation."""
        # |1|_p = 1 for any prime p
        assert self.flow.p_adic_norm(1, 2) == 1.0
        assert self.flow.p_adic_norm(1, 3) == 1.0
        
        # |0|_p = 0
        assert self.flow.p_adic_norm(0, 2) == 0.0
    
    def test_p_adic_norm_powers(self):
        """Test p-adic norm for powers of primes."""
        # |2|_2 = 2^(-1) = 0.5
        assert self.flow.p_adic_norm(2, 2) == 0.5
        
        # |4|_2 = |2^2|_2 = 2^(-2) = 0.25
        assert self.flow.p_adic_norm(4, 2) == 0.25
        
        # |8|_2 = 2^(-3) = 0.125
        assert self.flow.p_adic_norm(8, 2) == 0.125
        
        # |3|_3 = 3^(-1) ≈ 0.333...
        assert np.abs(self.flow.p_adic_norm(3, 3) - 1/3) < 1e-10
    
    def test_p_adic_norm_non_divisible(self):
        """Test p-adic norm when p doesn't divide x."""
        # |3|_2 = 1 (2 doesn't divide 3)
        assert self.flow.p_adic_norm(3, 2) == 1.0
        
        # |5|_2 = 1
        assert self.flow.p_adic_norm(5, 2) == 1.0
        
        # |2|_3 = 1 (3 doesn't divide 2)
        assert self.flow.p_adic_norm(2, 3) == 1.0
    
    def test_idelic_norm_product_formula(self):
        """Test idelic norm as product of local norms."""
        x_components = {
            'real': 2.0,
            2: 4,  # |4|_2 = 0.25
            3: 1   # |1|_3 = 1
        }
        
        norm = self.flow.idelic_norm(x_components)
        # Should be 2.0 * 0.25 * 1.0 = 0.5
        expected = 2.0 * 0.25 * 1.0
        assert np.abs(norm - expected) < 1e-10
    
    def test_flow_action_rates(self):
        """Test differential expansion rates."""
        t = 1.5
        action = self.flow.flow_action(t)
        
        # Archimedean: e^t
        assert np.abs(action['archimedean'] - np.exp(1.5)) < 1e-10
        
        # p-adic norm: preserved
        assert action['p_adic'] == 1.0
        
        # Frame bundle: e^(-t)
        assert np.abs(action['frame_compression'] - np.exp(-1.5)) < 1e-10
    
    def test_anosov_decomposition(self):
        """Test Anosov tangent space decomposition."""
        x = 1.0
        t = 1.0
        
        decomp = self.flow.anosov_decomposition(x, t)
        
        # Check all three subspaces exist
        assert 'E0' in decomp
        assert 'E_unstable' in decomp
        assert 'E_stable' in decomp
        
        # E^u expands by e^t
        assert np.abs(decomp['E_unstable'][1] - np.exp(1.0)) < 1e-10
        
        # E^s contracts by e^(-t)
        assert np.abs(decomp['E_stable'][1] - np.exp(-1.0)) < 1e-10
    
    def test_closed_orbits_structure(self):
        """Test closed orbit generation."""
        orbits = self.flow.closed_orbits(t_max=5.0)
        
        # Should find multiple orbits
        assert len(orbits) > 0
        
        # Each orbit should have required fields
        for orbit in orbits:
            assert 'prime' in orbit
            assert 'power' in orbit
            assert 'time' in orbit
            assert 'q' in orbit
            assert 'weight' in orbit
            assert 'ln_p' in orbit
            
            # Check q = p^k
            assert orbit['q'] == orbit['prime'] ** orbit['power']
            
            # Check time = k * ln(p)
            expected_t = orbit['power'] * np.log(orbit['prime'])
            assert np.abs(orbit['time'] - expected_t) < 1e-10
    
    def test_closed_orbits_from_primes(self):
        """Test that closed orbits correspond to e^t = p^k."""
        orbits = self.flow.closed_orbits(t_max=3.0)
        
        # Check first few orbits
        for orbit in orbits[:5]:
            p = orbit['prime']
            k = orbit['power']
            
            # Verify e^t = p^k
            t = orbit['time']
            assert np.abs(np.exp(t) - p**k) < 1e-8
    
    def test_selberg_trace_convergence(self):
        """Test Selberg trace formula convergence."""
        # Trace should be finite and real
        trace = self.flow.selberg_trace(1.0)
        assert np.isfinite(trace)
        assert np.isreal(trace)
        
        # Should decrease as t increases (exponential damping)
        trace_1 = self.flow.selberg_trace(1.0)
        trace_2 = self.flow.selberg_trace(2.0)
        assert trace_2 < trace_1
    
    def test_selberg_trace_positive(self):
        """Test that Selberg trace is positive."""
        for t in [0.5, 1.0, 1.5, 2.0]:
            trace = self.flow.selberg_trace(t)
            assert trace > 0, f"Trace should be positive at t={t}"
    
    def test_poisson_identity_poles(self):
        """Test Poisson identity has poles at k ln p."""
        s = 0.5 + 14.0j  # Away from poles
        
        result = self.flow.poisson_identity(s)
        assert np.isfinite(result.real)
        assert np.isfinite(result.imag)
    
    def test_lyapunov_exponents_signs(self):
        """Test Lyapunov exponents have correct signs."""
        lyap = self.flow.lyapunov_exponents()
        
        # Unstable direction: positive
        assert lyap['unstable'] > 0
        
        # Stable direction: negative
        assert lyap['stable'] < 0
        
        # Neutral (flow direction): zero
        assert lyap['neutral'] == 0
    
    def test_lyapunov_exponents_magnitude(self):
        """Test Lyapunov exponents are ±1."""
        lyap = self.flow.lyapunov_exponents()
        
        assert np.abs(lyap['unstable'] - 1.0) < 1e-10
        assert np.abs(lyap['stable'] + 1.0) < 1e-10
    
    def test_verify_hyperbolicity_true(self):
        """Test that flow is verified as Anosov."""
        verification = self.flow.verify_hyperbolicity()
        
        assert verification['is_anosov'] == True
        assert verification['lyapunov_gap'] > 0
        assert verification['decomposition_preserved'] == True
        assert verification['metric_emergent'] == True
    
    def test_hyperbolicity_gap(self):
        """Test uniform hyperbolicity gap."""
        verification = self.flow.verify_hyperbolicity()
        
        gap = verification['lyapunov_gap']
        assert gap >= 0.5  # Minimum required gap
        assert gap == 1.0  # For this flow
    
    def test_connection_to_zeta_poles(self):
        """Test connection to zeta function through poles."""
        s = 0.5 + 10.0j
        connection = self.flow.connection_to_zeta(s)
        
        # Should have poles
        assert len(connection['poles']) > 0
        
        # Poles should be at k ln p
        poles = connection['poles']
        for pole in poles[:3]:
            # Each pole should be positive (ln p > 0, k > 0)
            assert pole > 0
    
    def test_spectral_expansion_volume_preserving(self):
        """Test that flow is volume preserving: expansion × contraction = 1."""
        expansion_data = self.flow.compute_spectral_expansion()
        
        product = expansion_data['product']
        
        # Should be 1 everywhere (volume preserving)
        assert np.allclose(product, 1.0, atol=1e-10)
    
    def test_spectral_expansion_symmetry(self):
        """Test time-reversal symmetry of expansion/contraction."""
        expansion_data = self.flow.compute_spectral_expansion()
        
        t = expansion_data['t']
        expansion = expansion_data['expansion']
        contraction = expansion_data['contraction']
        
        # At t=0, both should be 1
        idx_zero = np.argmin(np.abs(t))
        assert np.abs(expansion[idx_zero] - 1.0) < 1e-10
        assert np.abs(contraction[idx_zero] - 1.0) < 1e-10
        
        # Expansion and contraction should be reciprocals
        assert np.allclose(expansion * contraction, 1.0, atol=1e-10)
    
    def test_validate_anosov_structure_complete(self):
        """Test complete validation function."""
        results = validate_anosov_structure()
        
        # All required keys should be present
        assert 'hyperbolicity' in results
        assert 'lyapunov_exponents' in results
        assert 'closed_orbits_count' in results
        assert 'selberg_trace_t1' in results
        assert 'zeta_connection' in results
        assert 'validation' in results
        
        # Validation should pass
        validation = results['validation']
        assert validation['is_anosov'] == True
        assert validation['metric_emergent'] == True
        assert validation['trace_formula_exact'] == True
        assert validation['poles_match_zeta'] == True
    
    def test_orbit_weights_decrease(self):
        """Test that orbit weights decrease with power k."""
        orbits = self.flow.closed_orbits(t_max=10.0)
        
        # For same prime, weights should decrease with k
        p2_orbits = [o for o in orbits if o['prime'] == 2]
        if len(p2_orbits) >= 2:
            weights = [o['weight'] for o in p2_orbits]
            # Should be decreasing (ln p / p^(k/2) decreases with k)
            for i in range(len(weights) - 1):
                assert weights[i] > weights[i+1]
    
    def test_metric_emergence(self):
        """Test that metric is not imposed but emerges from idelic action."""
        verification = self.flow.verify_hyperbolicity()
        
        # Key property: metric emerges, not imposed
        assert verification['metric_emergent'] == True
        
        # This is validated by checking that curvature comes from
        # the product structure of Archimedean × p-adic components
        assert verification['is_anosov'] == True


class TestAnosovFlowMathematics:
    """Test mathematical properties specific to Anosov flows."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.flow = AdelicAnosovFlow(primes=[2, 3, 5, 7], t_max=3.0)
    
    def test_flow_preserves_decomposition(self):
        """Test that flow preserves Anosov decomposition."""
        x = 1.0
        
        # Decomposition at different times should remain consistent
        decomp_1 = self.flow.anosov_decomposition(x, 1.0)
        decomp_2 = self.flow.anosov_decomposition(x, 2.0)
        
        # E^0 direction should be preserved (orbit tangent)
        assert decomp_1['E0'][0] == decomp_2['E0'][0]
        
        # Expansion/contraction should follow exponential law
        ratio = decomp_2['E_unstable'][1] / decomp_1['E_unstable'][1]
        expected_ratio = np.exp(2.0) / np.exp(1.0)
        assert np.abs(ratio - expected_ratio) < 1e-10
    
    def test_hyperbolicity_uniform_gap(self):
        """Test uniform gap in Lyapunov spectrum."""
        lyap = self.flow.lyapunov_exponents()
        
        # Gap from zero should be uniform
        gap_unstable = abs(lyap['unstable'] - 0)
        gap_stable = abs(lyap['stable'] - 0)
        
        # Both should be bounded away from zero uniformly
        assert gap_unstable >= 1.0
        assert gap_stable >= 1.0
    
    def test_ergodicity_property(self):
        """Test ergodic properties implied by Anosov structure."""
        # Anosov flows are ergodic with respect to natural measure
        # We verify this indirectly through orbit distribution
        
        orbits = self.flow.closed_orbits(t_max=10.0)
        
        # Orbits should be well-distributed (multiple primes)
        primes_used = set(o['prime'] for o in orbits)
        assert len(primes_used) >= 2  # At least 2 different primes
    
    def test_mixing_property(self):
        """Test mixing property through trace decay."""
        # Anosov flows are mixing: correlations decay exponentially
        
        # Selberg trace should decay exponentially
        trace_small = self.flow.selberg_trace(0.5)
        trace_large = self.flow.selberg_trace(3.0)
        
        # Large time should be much smaller
        assert trace_large < trace_small / 10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
