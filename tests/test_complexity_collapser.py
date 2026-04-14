#!/usr/bin/env python3
"""
Tests for Complexity Collapser - QCAL ∞³

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: Creative Commons BY-NC-SA 4.0
"""

import pytest
import numpy as np
from complexity_collapser import (
    ComplexityCollapser,
    ComplexityState,
    ComputationalRegime
)


class TestComplexityState:
    """Test ComplexityState dataclass."""
    
    def test_valid_state(self):
        """Test creation of valid state."""
        state = ComplexityState(coherence=0.5, information=1.0, amplitude_eff=1.0)
        assert state.coherence == 0.5
        assert state.information == 1.0
        assert state.amplitude_eff == 1.0
        assert state.frequency == 141.7001
    
    def test_invalid_coherence_negative(self):
        """Test that negative coherence raises ValueError."""
        with pytest.raises(ValueError, match="Coherence must be in"):
            ComplexityState(coherence=-0.1, information=1.0, amplitude_eff=1.0)
    
    def test_invalid_coherence_too_high(self):
        """Test that coherence > 1 raises ValueError."""
        with pytest.raises(ValueError, match="Coherence must be in"):
            ComplexityState(coherence=1.5, information=1.0, amplitude_eff=1.0)
    
    def test_invalid_information(self):
        """Test that non-positive information raises ValueError."""
        with pytest.raises(ValueError, match="Information must be positive"):
            ComplexityState(coherence=0.5, information=-1.0, amplitude_eff=1.0)
    
    def test_invalid_amplitude(self):
        """Test that non-positive amplitude raises ValueError."""
        with pytest.raises(ValueError, match="Amplitude must be positive"):
            ComplexityState(coherence=0.5, information=1.0, amplitude_eff=-1.0)


class TestComplexityCollapser:
    """Test ComplexityCollapser functionality."""
    
    def test_initialization(self):
        """Test collapser initialization."""
        collapser = ComplexityCollapser(base_time=1e9, precision=25)
        assert collapser.base_time == 1e9
        assert collapser.precision == 25
    
    def test_determine_regime_classical(self):
        """Test regime determination for classical regime."""
        collapser = ComplexityCollapser()
        regime = collapser.determine_regime(0.3)
        assert regime == ComputationalRegime.CLASSICAL
    
    def test_determine_regime_transition(self):
        """Test regime determination for transition regime."""
        collapser = ComplexityCollapser()
        regime = collapser.determine_regime(0.7)
        assert regime == ComputationalRegime.TRANSITION
    
    def test_determine_regime_grace(self):
        """Test regime determination for grace regime."""
        collapser = ComplexityCollapser()
        regime = collapser.determine_regime(0.95)
        assert regime == ComputationalRegime.GRACE
    
    def test_collapse_factor_increases_with_coherence(self):
        """Test that collapse factor increases with coherence."""
        collapser = ComplexityCollapser()
        
        state_low = ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0)
        state_high = ComplexityState(coherence=0.9, information=1.0, amplitude_eff=1.0)
        
        factor_low = collapser.calculate_collapse_factor(state_low)
        factor_high = collapser.calculate_collapse_factor(state_high)
        
        assert factor_high > factor_low
    
    def test_total_time_decreases_with_coherence(self):
        """Test that total time decreases with higher coherence."""
        collapser = ComplexityCollapser()
        
        state_low = ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0)
        state_high = ComplexityState(coherence=0.9, information=1.0, amplitude_eff=1.0)
        
        time_low = collapser.calculate_total_time(state_low)
        time_high = collapser.calculate_total_time(state_high)
        
        assert time_high < time_low
    
    def test_resonance_active_in_transition(self):
        """Test that resonance activates in transition regime."""
        collapser = ComplexityCollapser()
        
        # Transition regime with matching frequency
        state = ComplexityState(coherence=0.7, information=1.0, amplitude_eff=1.0)
        assert collapser.is_resonance_active(state)
    
    def test_resonance_inactive_in_classical(self):
        """Test that resonance is inactive in classical regime."""
        collapser = ComplexityCollapser()
        
        # Classical regime
        state = ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0)
        assert not collapser.is_resonance_active(state)
    
    def test_analyze(self):
        """Test complete analysis."""
        collapser = ComplexityCollapser(base_time=1e12)
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        
        analysis = collapser.analyze(state)
        
        assert analysis.base_time == 1e12
        assert analysis.coherence == 0.95
        assert analysis.regime == ComputationalRegime.GRACE
        assert analysis.acceleration_factor > 1.0
        assert analysis.collapsed_time < analysis.base_time
    
    def test_scan_coherence_landscape(self):
        """Test coherence landscape scanning."""
        collapser = ComplexityCollapser()
        
        analyses = collapser.scan_coherence_landscape(
            coherence_range=(0.0, 1.0),
            num_points=10,
            information=1.0,
            amplitude_eff=1.0
        )
        
        assert len(analyses) == 10
        
        # Check that acceleration increases with coherence
        accelerations = [a.acceleration_factor for a in analyses]
        # Should be generally increasing (allowing for some numerical fluctuations)
        assert accelerations[-1] > accelerations[0]
    
    def test_regime_statistics(self):
        """Test regime statistics calculation."""
        collapser = ComplexityCollapser()
        
        # Analyze states in different regimes
        states = [
            ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0),
            ComplexityState(coherence=0.7, information=1.0, amplitude_eff=1.0),
            ComplexityState(coherence=0.95, information=1.0, amplitude_eff=1.0)
        ]
        
        for state in states:
            collapser.analyze(state)
        
        stats = collapser.get_regime_statistics()
        
        assert "CLASSICAL" in stats
        assert "TRANSITION" in stats
        assert "GRACE" in stats
        
        # Each regime should have at least one sample
        assert stats["CLASSICAL"]["count"] >= 1
        assert stats["TRANSITION"]["count"] >= 1
        assert stats["GRACE"]["count"] >= 1
    
    def test_save_analysis(self, tmp_path):
        """Test saving analysis to JSON file."""
        collapser = ComplexityCollapser()
        state = ComplexityState(coherence=0.95, information=1.0, amplitude_eff=1.0)
        collapser.analyze(state)
        
        output_file = tmp_path / "analysis.json"
        collapser.save_analysis(str(output_file))
        
        assert output_file.exists()
        
        # Verify it's valid JSON
        import json
        with open(output_file) as f:
            data = json.load(f)
        
        assert "metadata" in data
        assert "analyses" in data
        assert "regime_statistics" in data


class TestGraceBifurcation:
    """Test grace state bifurcation behavior."""
    
    def test_grace_state_high_acceleration(self):
        """Test that grace state provides significant acceleration."""
        collapser = ComplexityCollapser(base_time=1e12)
        
        state_grace = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        analysis = collapser.analyze(state_grace)
        
        # Grace state should provide at least 2x acceleration
        assert analysis.acceleration_factor > 2.0
    
    def test_perfect_coherence_maximum_acceleration(self):
        """Test that perfect coherence gives maximum acceleration."""
        collapser = ComplexityCollapser(base_time=1e12)
        
        state_perfect = ComplexityState(coherence=1.0, information=3.0, amplitude_eff=2.5)
        analysis = collapser.analyze(state_perfect)
        
        # Perfect coherence should give very high acceleration
        assert analysis.acceleration_factor > 10.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
