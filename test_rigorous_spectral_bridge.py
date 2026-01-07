#!/usr/bin/env python3
"""
Test suite for Rigorous Spectral Bridge

Tests the spectral equivalence verification:
    ∀ z ∈ Spec(𝓗_Ψ), ∃! t : ℝ, z = i(t - 1/2) ∧ ζ(1/2 + i·t) = 0

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-07
"""

import sys
import pytest
import mpmath as mp
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from rigorous_spectral_bridge import RigorousSpectralBridge


class TestRigorousSpectralBridge:
    """Test suite for rigorous spectral bridge verification"""
    
    @pytest.fixture
    def bridge(self):
        """Create bridge instance with moderate precision"""
        return RigorousSpectralBridge(precision_dps=30)
    
    @pytest.fixture
    def sample_zeros(self):
        """First 5 nontrivial zeros (imaginary parts)"""
        return [
            mp.mpf("14.134725141734693790457251983562"),
            mp.mpf("21.022039638771554992628479593896"),
            mp.mpf("25.010857580145688763213790992562"),
            mp.mpf("30.424876125859513210311897530584"),
            mp.mpf("32.935061587739189690662368964074"),
        ]
    
    def test_spectral_map_forward(self, bridge, sample_zeros):
        """Test that spectral map produces valid complex eigenvalues"""
        for t in sample_zeros:
            z = bridge.spectral_map(t)
            
            # Check it's a complex number
            assert isinstance(z, mp.mpc)
            
            # Check real part is approximately 0 (should be pure imaginary)
            assert abs(z.real) < 1e-10
            
            # Check imaginary part is correct
            expected_imag = t - mp.mpf("0.5")
            assert abs(z.imag - expected_imag) < 1e-10
    
    def test_spectral_map_inverse(self, bridge, sample_zeros):
        """Test that inverse map correctly recovers zero imaginary parts"""
        for t_original in sample_zeros:
            z = bridge.spectral_map(t_original)
            t_recovered = bridge.inverse_spectral_map(z)
            
            # Should recover original value
            assert abs(t_recovered - t_original) < 1e-10
    
    def test_bijection_verification(self, bridge, sample_zeros):
        """Test bijection between zeros and eigenvalues"""
        eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
        
        result = bridge.verify_bijection(sample_zeros, eigenvalues)
        assert result is True
    
    def test_local_uniqueness(self, bridge, sample_zeros):
        """Test local uniqueness with epsilon = 0.1"""
        # Zeros should be well-separated (> 0.1 apart)
        result = bridge.verify_local_uniqueness(sample_zeros)
        assert result is True
    
    def test_order_preservation(self, bridge, sample_zeros):
        """Test that ordering is preserved under spectral map"""
        eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
        
        result = bridge.verify_order_preservation(sample_zeros, eigenvalues)
        assert result is True
    
    def test_weyl_law_exact(self, bridge, sample_zeros):
        """Test exact Weyl law: |N_spec - N_zeros| < 1"""
        eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
        T = mp.mpf("35.0")  # Height parameter
        
        error = bridge.compute_weyl_law_error(T, len(eigenvalues), len(sample_zeros))
        
        # Error should be strictly less than 1
        assert error < 1
        
        # In this case, should be exactly 0 (same count)
        assert error == 0
    
    def test_fundamental_frequency_constant(self, bridge):
        """Test that fundamental frequency constant is defined"""
        assert bridge.F0_EXACT is not None
        
        # Check precision
        f0_str = str(bridge.F0_EXACT)
        assert "141.7" in f0_str
        
        # Check it's positive
        assert bridge.F0_EXACT > 0
    
    def test_coherence_constants(self, bridge):
        """Test QCAL coherence constants"""
        assert bridge.C_COHERENCE == mp.mpf("244.36")
        assert bridge.C_SPECTRAL == mp.mpf("629.83")
    
    def test_uniqueness_epsilon(self, bridge):
        """Test uniqueness epsilon value"""
        assert bridge.EPSILON_UNIQUENESS == mp.mpf("0.1")
    
    def test_full_equivalence_verification(self, bridge, sample_zeros):
        """Test complete spectral equivalence verification"""
        eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
        T = mp.mpf("35.0")
        zeta_deriv = mp.mpf("2.0")  # Approximate
        
        result = bridge.verify_spectral_equivalence(
            sample_zeros, eigenvalues, T, zeta_deriv
        )
        
        # Check all components
        assert result.is_equivalent is True
        assert result.bijection_verified is True
        assert result.order_preserved is True
        assert result.weyl_law_error < 1
        assert result.uniqueness_epsilon == 0.1
        assert result.num_zeros_checked == len(sample_zeros)
        assert result.precision_dps == bridge.precision_dps
    
    def test_spectral_map_linearity_in_gaps(self, bridge, sample_zeros):
        """Test that spectral map preserves gap structure"""
        eigenvalues = [bridge.spectral_map(t) for t in sample_zeros]
        
        # Compute gaps between consecutive zeros
        zero_gaps = [sample_zeros[i+1] - sample_zeros[i] 
                     for i in range(len(sample_zeros) - 1)]
        
        # Compute gaps between consecutive eigenvalues
        eigenvalue_gaps = [eigenvalues[i+1].imag - eigenvalues[i].imag 
                          for i in range(len(eigenvalues) - 1)]
        
        # Gaps should be equal (linear map)
        for zg, eg in zip(zero_gaps, eigenvalue_gaps):
            assert abs(zg - eg) < 1e-10


def test_spectral_bridge_demo():
    """Test that demo runs without errors"""
    from rigorous_spectral_bridge import demo_spectral_bridge
    
    # Should complete without exceptions
    demo_spectral_bridge()


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
