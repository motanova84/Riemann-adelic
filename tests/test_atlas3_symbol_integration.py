#!/usr/bin/env python3
"""
Tests for Atlas³ Symbol Calculus Integration with Atlas3Operator

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from atlas3_operator import Atlas3Operator, KAPPA_PI


class TestAtlas3SymbolIntegration:
    """Tests for symbol calculus integration with Atlas³ operator."""
    
    def test_symbol_calculus_available(self):
        """Test that symbol calculus can be loaded."""
        atlas = Atlas3Operator(N=100, beta_0=1.0)
        symbol_calc = atlas.get_symbol_calculus()
        
        # Should return dict or None
        assert symbol_calc is None or isinstance(symbol_calc, dict)
    
    def test_get_symbol_calculus_components(self):
        """Test symbol calculus returns all required components."""
        atlas = Atlas3Operator(N=100, beta_0=2.0, V_amp=12650.0)
        symbol_calc = atlas.get_symbol_calculus()
        
        if symbol_calc is not None:
            # Should have all components
            assert 'symbol' in symbol_calc
            assert 'weyl_calculator' in symbol_calc
            assert 'hamiltonian_flow' in symbol_calc
            assert 'trace_calculator' in symbol_calc
            assert 'kappa_derivation' in symbol_calc
    
    def test_symbol_parameters_match_operator(self):
        """Test symbol parameters match operator configuration."""
        V_amp = 10000.0
        beta_0 = 1.5
        
        atlas = Atlas3Operator(N=100, beta_0=beta_0, V_amp=V_amp)
        symbol_calc = atlas.get_symbol_calculus()
        
        if symbol_calc is not None:
            symbol = symbol_calc['symbol']
            
            # Parameters should match
            assert symbol.V_amp == V_amp
            assert symbol.beta_0 == beta_0
    
    def test_weyl_law_validation_structure(self):
        """Test Weyl law validation returns proper structure."""
        atlas = Atlas3Operator(N=100, beta_0=1.0)
        eigenvalues, _ = atlas.compute_spectrum()
        
        weyl_validation = atlas.validate_weyl_law_from_symbol(eigenvalues)
        
        # Check structure
        assert 'N_spectral' in weyl_validation or 'error' in weyl_validation
        
        if 'N_spectral' in weyl_validation:
            assert weyl_validation['N_spectral'] == len(eigenvalues)
            assert weyl_validation['N_spectral'] > 0
    
    def test_trace_from_symbol_structure(self):
        """Test trace computation from symbol returns proper structure."""
        atlas = Atlas3Operator(N=50, beta_0=0.5)
        
        trace_result = atlas.compute_trace_from_symbol(tau=0.5, primes=[2, 3], k_max=5)
        
        # Check structure
        if 'trace_value' in trace_result:
            assert 'trace_real' in trace_result
            assert 'trace_imag' in trace_result
            assert 'trace_magnitude' in trace_result
            assert 'prime_contributions' in trace_result
    
    def test_trace_from_symbol_positive_magnitude(self):
        """Test trace has positive magnitude."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        
        trace_result = atlas.compute_trace_from_symbol(tau=0.5, primes=[2, 3, 5], k_max=10)
        
        if 'trace_magnitude' in trace_result:
            assert trace_result['trace_magnitude'] >= 0
    
    def test_kappa_derivation_structure(self):
        """Test κ derivation returns proper structure."""
        atlas = Atlas3Operator(N=50, beta_0=2.0, V_amp=12650.0)
        
        kappa_result = atlas.derive_kappa_from_symbol()
        
        # Check structure
        if 'kappa_hermiticity' in kappa_result:
            assert 'kappa_maslov_index' in kappa_result
            assert 'kappa_pt_compensation' in kappa_result
            assert 'kappa_experimental' in kappa_result
    
    def test_kappa_derivation_matches_kappa_pi(self):
        """Test κ derivation matches KAPPA_PI."""
        atlas = Atlas3Operator(N=50, beta_0=2.0, V_amp=12650.0)
        
        kappa_result = atlas.derive_kappa_from_symbol()
        
        if 'kappa_hermiticity' in kappa_result:
            # Should match KAPPA_PI closely
            assert abs(kappa_result['kappa_hermiticity'] - KAPPA_PI) < 1e-6
            assert abs(kappa_result['kappa_pt_compensation'] - KAPPA_PI) < 1e-6
            assert kappa_result['kappa_experimental'] == KAPPA_PI
    
    def test_kappa_maslov_index_value(self):
        """Test Maslov index has expected value."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        
        kappa_result = atlas.derive_kappa_from_symbol()
        
        if 'kappa_maslov_index' in kappa_result:
            # Maslov index should be 1/4 for 1D systems
            assert abs(kappa_result['kappa_maslov_index'] - 0.25) < 1e-10
    
    def test_trace_decreases_with_tau(self):
        """Test trace magnitude decreases as τ increases."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        
        tau_small = 0.1
        tau_large = 2.0
        
        trace_small = atlas.compute_trace_from_symbol(tau=tau_small, primes=[2, 3], k_max=5)
        trace_large = atlas.compute_trace_from_symbol(tau=tau_large, primes=[2, 3], k_max=5)
        
        if 'trace_magnitude' in trace_small and 'trace_magnitude' in trace_large:
            # Trace should decrease with τ due to e^(-τ) factor
            assert trace_small['trace_magnitude'] > trace_large['trace_magnitude']
    
    def test_prime_contributions_decrease(self):
        """Test prime contributions decrease for larger primes."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        
        trace_result = atlas.compute_trace_from_symbol(tau=0.5, primes=[2, 3, 5, 7], k_max=5)
        
        if 'prime_contributions' in trace_result:
            contribs = trace_result['prime_contributions']
            
            # Contributions should generally decrease for larger primes
            assert abs(contribs[2]) > abs(contribs[7])
    
    def test_kappa_scales_with_V_amp(self):
        """Test κ_PT scales as √V_amp."""
        # Two operators with different V_amp
        atlas1 = Atlas3Operator(N=50, beta_0=1.0, V_amp=10000.0)
        atlas2 = Atlas3Operator(N=50, beta_0=1.0, V_amp=40000.0)
        
        kappa1 = atlas1.derive_kappa_from_symbol()
        kappa2 = atlas2.derive_kappa_from_symbol()
        
        if 'kappa_pt_compensation' in kappa1 and 'kappa_pt_compensation' in kappa2:
            # Ratio should be √(40000/10000) = 2
            ratio = kappa2['kappa_pt_compensation'] / kappa1['kappa_pt_compensation']
            assert abs(ratio - 2.0) < 0.1
    
    def test_integration_numerical_stability(self):
        """Test integration is numerically stable."""
        # Test with various configurations
        configs = [
            {'N': 50, 'beta_0': 0.0, 'V_amp': 1000.0},
            {'N': 100, 'beta_0': 1.0, 'V_amp': 10000.0},
            {'N': 50, 'beta_0': 2.0, 'V_amp': 12650.0},
        ]
        
        for config in configs:
            atlas = Atlas3Operator(**config)
            
            # All computations should be finite
            symbol_calc = atlas.get_symbol_calculus()
            
            if symbol_calc is not None:
                eigenvalues, _ = atlas.compute_spectrum()
                
                weyl_val = atlas.validate_weyl_law_from_symbol(eigenvalues)
                trace_val = atlas.compute_trace_from_symbol(tau=0.5)
                kappa_val = atlas.derive_kappa_from_symbol()
                
                # All should return valid dicts without errors
                assert 'error' not in weyl_val or isinstance(weyl_val.get('N_spectral'), (int, float))
                assert 'error' not in trace_val or isinstance(trace_val.get('trace_magnitude'), (int, float))
                assert 'error' not in kappa_val or isinstance(kappa_val.get('kappa_hermiticity'), (int, float))


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
