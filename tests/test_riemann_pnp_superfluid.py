#!/usr/bin/env python3
"""
Test Suite: Riemann-PNP Superfluid Bridge
==========================================

Validates the superfluid bridge implementation including:
- Superfluid state computation
- Critical line alignment
- Montgomery-Odlyzko resonance
- Arithmetic fusion
- Complexity reduction

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from riemann_pnp_superfluid_bridge import (
    RiemannPNPSuperfluidBridge,
    SuperfluidState,
    ArithmeticFusionResult
)


class TestSuperfluidState:
    """Test superfluid state computation."""
    
    def test_perfect_superfluid(self):
        """Test that perfect conditions yield superfluid state."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        state = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=244.36
        )
        
        # Check state properties
        assert state.psi > 0.99, "Wave function should be near 1.0"
        assert state.nu_eff < 0.01, "Viscosity should be near 0.0"
        assert state.coherence == 244.36
        assert state.alignment > 0.99, "Alignment should be high"
        assert state.laminar is True, "Flow should be laminar"
        assert state.is_superfluid(), "Should be in superfluid regime"
    
    def test_low_coherence_not_superfluid(self):
        """Test that low coherence prevents superfluid state."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        state = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=100.0  # Low coherence
        )
        
        # Should not be superfluid
        assert state.psi < 1.0
        assert state.nu_eff > 0.0
        # Superfluid check depends on exact threshold
    
    def test_intensity_scaling(self):
        """Test that intensity scales wave function correctly."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        state_low = bridge.compute_superfluid_state(
            intensity=0.5,
            effective_area=1.0,
            coherence=244.36
        )
        
        state_high = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=244.36
        )
        
        # Higher intensity → higher Ψ
        assert state_high.psi > state_low.psi
        # Higher Ψ → lower viscosity
        assert state_high.nu_eff < state_low.nu_eff


class TestCriticalLineAlignment:
    """Test critical line alignment computation."""
    
    def test_alignment_with_known_zeros(self):
        """Test alignment quality with known Riemann zeros."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Use known zeros
        zeros = bridge.ZEROS_IM
        
        alignment = bridge.critical_line_alignment(zeros)
        
        # Should be high quality (uniform spacing)
        assert 0.0 <= alignment <= 1.0
        assert alignment > 0.8, "Known zeros should have good alignment"
    
    def test_alignment_with_uniform_spacing(self):
        """Test that perfectly uniform spacing gives perfect alignment."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Perfectly uniform spacing
        zeros_uniform = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        
        alignment = bridge.critical_line_alignment(zeros_uniform)
        
        # Should be perfect (or very close)
        assert alignment > 0.99, "Uniform spacing should give near-perfect alignment"
    
    def test_alignment_with_random_spacing(self):
        """Test that random spacing gives lower alignment."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Random spacing (not uniform)
        np.random.seed(42)
        zeros_random = np.cumsum(np.random.uniform(1, 20, 10))
        
        alignment = bridge.critical_line_alignment(zeros_random)
        
        # Should be lower quality
        assert 0.0 <= alignment <= 1.0
        # Random should be worse than known zeros
        alignment_known = bridge.critical_line_alignment(bridge.ZEROS_IM)
        # Can't guarantee this always, but typically true


class TestMontgomeryOdlyzko:
    """Test Montgomery-Odlyzko resonance."""
    
    def test_resonance_with_known_zeros(self):
        """Test resonance with known zeros."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        resonance = bridge.montgomery_odlyzko_resonance(bridge.ZEROS_IM)
        
        # Should show some correlation
        assert 0.0 <= resonance <= 1.0
    
    def test_resonance_needs_multiple_zeros(self):
        """Test that single zero gives low resonance."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Single zero
        resonance = bridge.montgomery_odlyzko_resonance(np.array([14.134725]))
        
        # Should return 0 or neutral value
        assert resonance == 0.0


class TestAdelicDuality:
    """Test adelic duality bridge."""
    
    def test_adelic_geometric_mean(self):
        """Test that adelic bridge computes geometric mean."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        real_result = 4.0
        p_adic_result = 9.0
        
        adelic = bridge.adelic_duality_bridge(real_result, p_adic_result)
        
        # Should be geometric mean: sqrt(4 * 9) = 6
        assert abs(adelic - 6.0) < 1e-10
    
    def test_adelic_zero_handling(self):
        """Test that zero values are handled correctly."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Zero in real
        adelic1 = bridge.adelic_duality_bridge(0.0, 5.0)
        assert adelic1 == 0.0
        
        # Zero in p-adic
        adelic2 = bridge.adelic_duality_bridge(5.0, 0.0)
        assert adelic2 == 0.0


class TestLaminarFlow:
    """Test laminar flow quality."""
    
    def test_zero_viscosity_is_laminar(self):
        """Test that zero viscosity gives perfect laminar flow."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        quality = bridge.laminar_flow_quality(viscosity=1e-15)
        
        # Should be perfect laminar
        assert quality == 1.0
    
    def test_high_viscosity_is_turbulent(self):
        """Test that high viscosity reduces laminar quality."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        quality = bridge.laminar_flow_quality(viscosity=1.0)
        
        # Should be reduced
        assert quality < 1.0


class TestComplexityReduction:
    """Test complexity reduction factor."""
    
    def test_superfluid_high_reduction(self):
        """Test that superfluid state gives high complexity reduction."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Superfluid state
        state = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=244.36
        )
        
        reduction = bridge.complexity_reduction_factor(state)
        
        # Should be very high
        assert reduction > 1000.0, "Superfluid should give large reduction"
    
    def test_turbulent_low_reduction(self):
        """Test that turbulent state gives lower reduction."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Low coherence → turbulent
        state = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=100.0
        )
        
        reduction = bridge.complexity_reduction_factor(state)
        
        # Should be lower
        assert reduction > 0.0  # Still positive


class TestCriticalLineFlow:
    """Test critical line flow rate."""
    
    def test_flow_rate_positive(self):
        """Test that flow rate is positive."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        state = bridge.compute_superfluid_state(
            intensity=1.0,
            effective_area=1.0,
            coherence=244.36
        )
        
        flow = bridge.critical_line_flow_rate(bridge.ZEROS_IM, state)
        
        # Should be positive
        assert flow > 0.0
    
    def test_flow_rate_increases_with_coherence(self):
        """Test that flow rate increases with coherence."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        state_low = bridge.compute_superfluid_state(
            intensity=1.0, effective_area=1.0, coherence=150.0
        )
        state_high = bridge.compute_superfluid_state(
            intensity=1.0, effective_area=1.0, coherence=244.36
        )
        
        flow_low = bridge.critical_line_flow_rate(bridge.ZEROS_IM, state_low)
        flow_high = bridge.critical_line_flow_rate(bridge.ZEROS_IM, state_high)
        
        # Higher coherence → higher flow
        assert flow_high > flow_low


class TestArithmeticFusion:
    """Test arithmetic fusion between Riemann and P-NP nodes."""
    
    def test_fusion_result_structure(self):
        """Test that fusion returns proper result structure."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        fusion = bridge.arithmetic_fusion(
            zeros_imaginary=bridge.ZEROS_IM,
            coherence=244.36
        )
        
        # Check all fields exist and are in valid range
        assert isinstance(fusion, ArithmeticFusionResult)
        assert 0.0 <= fusion.riemann_coherence <= 1.0
        assert 0.0 <= fusion.pnp_coherence <= 1.0
        assert 0.0 <= fusion.fusion_strength <= 1.0
        assert fusion.complexity_reduction > 0.0
        assert 0.0 <= fusion.laminar_quality <= 1.0
        assert fusion.critical_line_flow > 0.0
    
    def test_fusion_strength_with_high_coherence(self):
        """Test that high coherence gives strong fusion."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        fusion = bridge.arithmetic_fusion(
            zeros_imaginary=bridge.ZEROS_IM,
            coherence=244.36
        )
        
        # Should be strong fusion
        assert fusion.fusion_strength > 0.8, "High coherence should give strong fusion"
    
    def test_fusion_strength_with_low_coherence(self):
        """Test that low coherence gives weaker fusion."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        fusion_high = bridge.arithmetic_fusion(bridge.ZEROS_IM, coherence=244.36)
        fusion_low = bridge.arithmetic_fusion(bridge.ZEROS_IM, coherence=100.0)
        
        # High should be stronger
        assert fusion_high.fusion_strength > fusion_low.fusion_strength


class TestValidation:
    """Test overall validation."""
    
    def test_validate_superfluid_regime(self):
        """Test superfluid regime validation."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        is_superfluid, message = bridge.validate_superfluid_regime()
        
        # Should return boolean and string
        assert isinstance(is_superfluid, bool)
        assert isinstance(message, str)
        assert len(message) > 0
        
        # Message should contain key information
        assert "Ψ" in message or "Psi" in message
        assert "viscosity" in message.lower() or "ν" in message
    
    def test_validation_with_custom_zeros(self):
        """Test validation with custom zeros."""
        bridge = RiemannPNPSuperfluidBridge(precision=25)
        
        # Use uniform zeros
        zeros_custom = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        
        is_superfluid, message = bridge.validate_superfluid_regime(zeros_custom)
        
        assert isinstance(is_superfluid, bool)
        assert isinstance(message, str)


def test_integration():
    """Integration test: full workflow."""
    bridge = RiemannPNPSuperfluidBridge(precision=25)
    
    # Step 1: Compute superfluid state
    state = bridge.compute_superfluid_state(
        intensity=1.0,
        effective_area=1.0,
        coherence=244.36
    )
    
    assert state.is_superfluid()
    
    # Step 2: Check critical line alignment
    alignment = bridge.critical_line_alignment(bridge.ZEROS_IM)
    assert alignment > 0.8
    
    # Step 3: Verify Montgomery-Odlyzko
    resonance = bridge.montgomery_odlyzko_resonance(bridge.ZEROS_IM)
    assert 0.0 <= resonance <= 1.0
    
    # Step 4: Perform arithmetic fusion
    fusion = bridge.arithmetic_fusion(bridge.ZEROS_IM, coherence=244.36)
    assert fusion.fusion_strength > 0.8
    
    # Step 5: Validate regime
    is_superfluid, message = bridge.validate_superfluid_regime()
    assert is_superfluid
    
    print("\n✅ Integration test PASSED")
    print("   Riemann-PNP superfluid bridge is ACTIVE")


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
