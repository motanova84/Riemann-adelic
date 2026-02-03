#!/usr/bin/env python3
"""
Tests for PNP_BRIDGE module
"""

import sys
import os

# Add path to .github/agents/riemann
repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
pnp_bridge_path = os.path.join(repo_root, '.github', 'agents', 'riemann')
sys.path.insert(0, pnp_bridge_path)

import pytest
import numpy as np
from dataclasses import asdict

from pnp_bridge import PNPSpectralBridge, ComplexityTransition


class TestComplexityTransition:
    """Test ComplexityTransition dataclass"""
    
    def test_speedup_calculation(self):
        """Test speedup property"""
        trans = ComplexityTransition(
            classical_complexity=1000.0,
            coherent_complexity=10.0,
            acceleration_factor=100.0,
            coherence_level=0.999,
            p_equivalent=True
        )
        assert trans.speedup == 100.0
    
    def test_speedup_infinity(self):
        """Test speedup with zero coherent complexity"""
        trans = ComplexityTransition(
            classical_complexity=1000.0,
            coherent_complexity=0.0,
            acceleration_factor=float('inf'),
            coherence_level=0.999999,
            p_equivalent=True
        )
        assert trans.speedup == float('inf')


class TestPNPSpectralBridge:
    """Test PNPSpectralBridge class"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.bridge = PNPSpectralBridge()
    
    def test_initialization(self):
        """Test bridge initialization"""
        assert self.bridge.base_frequency == 141.7001
        assert self.bridge.critical_coherence == 0.888
    
    def test_classical_zero_search(self):
        """Test classical zero search"""
        t_range = (14.0, 100.0)
        result = self.bridge.classical_zero_search(t_range)
        
        assert result["search_type"] == "CLASSICAL_EXHAUSTIVE"
        assert result["points_to_check"] == 1000
        assert result["total_complexity"] > 0
        assert result["expected_zeros"] > 0
        assert result["complexity_per_zero"] > 0
    
    def test_coherent_zero_search_low_coherence(self):
        """Test coherent search with low coherence falls back to classical"""
        t_range = (14.0, 100.0)
        result = self.bridge.coherent_zero_search(t_range, coherence_level=0.5)
        
        # Should fall back to classical search
        assert result["search_type"] == "CLASSICAL_EXHAUSTIVE"
    
    def test_coherent_zero_search_high_coherence(self):
        """Test coherent search with high coherence"""
        t_range = (14.0, 100.0)
        result = self.bridge.coherent_zero_search(t_range, coherence_level=0.999)
        
        assert result["search_type"] == "COHERENT_RESONANT"
        assert result["coherence_level"] == 0.999
        assert result["points_to_check"] < 1000  # Should be reduced
        assert "resonance_advantage" in result
        assert result["resonance_advantage"] > 1
    
    def test_resonance_advantage_levels(self):
        """Test resonance advantage calculation at different coherence levels"""
        assert self.bridge._calculate_resonance_advantage(0.5) == 1
        assert self.bridge._calculate_resonance_advantage(0.888) == 10
        assert self.bridge._calculate_resonance_advantage(0.95) == 1e2
        assert self.bridge._calculate_resonance_advantage(0.99) == 1e4
        assert self.bridge._calculate_resonance_advantage(0.999) == 1e6
        assert self.bridge._calculate_resonance_advantage(0.999999) == float('inf')
    
    def test_analyze_complexity_transition(self):
        """Test complexity transition analysis"""
        t_range = (14.0, 100.0)
        coherence_levels = [0.5, 0.888, 0.99, 0.999]
        
        transitions = self.bridge.analyze_complexity_transition(t_range, coherence_levels)
        
        assert len(transitions) == 4
        assert all(isinstance(t, ComplexityTransition) for t in transitions)
        
        # Check that acceleration increases with coherence
        for i in range(len(transitions) - 1):
            if transitions[i].coherence_level >= 0.888:
                assert transitions[i+1].acceleration_factor >= transitions[i].acceleration_factor
    
    def test_simulate_zero_detection_experiment(self):
        """Test zero detection experiment simulation"""
        np.random.seed(42)  # For reproducibility
        
        experiment = self.bridge.simulate_zero_detection_experiment(
            num_zeros=10,
            coherence_level=0.999
        )
        
        assert experiment["experiment_type"] == "ZERO_DETECTION_COMPARISON"
        assert experiment["coherence_level"] == 0.999
        assert "classical" in experiment
        assert "coherent" in experiment
        assert "improvement" in experiment
        
        # Check metrics
        assert 0 <= experiment["classical"]["recall"] <= 1
        assert 0 <= experiment["classical"]["precision"] <= 1
        assert 0 <= experiment["coherent"]["recall"] <= 1
        assert 0 <= experiment["coherent"]["precision"] <= 1
    
    def test_p_equivalence_threshold(self):
        """Test P-equivalence determination"""
        t_range = (14.0, 100.0)
        
        # High coherence should be P-equivalent
        high_coherence_result = self.bridge.coherent_zero_search(t_range, coherence_level=0.999)
        p_threshold = np.log(t_range[1]) ** 3
        
        assert high_coherence_result["complexity_per_zero"] < p_threshold


class TestMainFunctionality:
    """Test main function scenarios"""
    
    def test_bridge_conceptual_demo(self, capsys):
        """Test that bridge can run without arguments"""
        from pnp_bridge import main
        import sys
        
        # Mock argv
        original_argv = sys.argv
        try:
            sys.argv = ['pnp_bridge.py']
            main()
            captured = capsys.readouterr()
            
            assert "EL GRAN PUENTE P-NP" in captured.out
            assert "PROBLEMA ORIGINAL" in captured.out
            assert "SOLUCIÓN POR COHERENCIA" in captured.out
        finally:
            sys.argv = original_argv


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
