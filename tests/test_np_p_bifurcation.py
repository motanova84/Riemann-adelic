#!/usr/bin/env python3
"""
Tests for NP→P Bifurcation Simulator - QCAL ∞³

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: Creative Commons BY-NC-SA 4.0
"""

import pytest
import numpy as np
from complexity_collapser import ComplexityState, ComplexityCollapser
from np_p_bifurcation import (
    NPPBifurcationSimulator,
    ProblemType,
    BifurcationPoint,
    RiemannZeroSearch
)


class TestNPPBifurcationSimulator:
    """Test NPPBifurcationSimulator functionality."""
    
    def test_initialization(self):
        """Test simulator initialization."""
        simulator = NPPBifurcationSimulator()
        assert simulator.collapser is not None
        assert simulator.BIFURCATION_THRESHOLD == 0.888
        assert simulator.RESONANCE_FREQUENCY == 141.7001
    
    def test_initialization_with_custom_collapser(self):
        """Test simulator with custom collapser."""
        collapser = ComplexityCollapser(base_time=1e15)
        simulator = NPPBifurcationSimulator(collapser=collapser)
        assert simulator.collapser.base_time == 1e15
    
    def test_classical_complexity_sat(self):
        """Test classical complexity calculation for SAT."""
        simulator = NPPBifurcationSimulator()
        complexity = simulator.classical_complexity(ProblemType.SAT, 10)
        assert complexity == 2**10
    
    def test_classical_complexity_tsp(self):
        """Test classical complexity calculation for TSP."""
        simulator = NPPBifurcationSimulator()
        complexity = simulator.classical_complexity(ProblemType.TSP, 5)
        # 5! = 120
        assert complexity == 120.0
    
    def test_classical_complexity_riemann(self):
        """Test classical complexity for Riemann zeros."""
        simulator = NPPBifurcationSimulator()
        complexity = simulator.classical_complexity(ProblemType.RIEMANN_ZERO, 100)
        # Should be T * log(T)
        expected = 100 * np.log(100)
        assert abs(complexity - expected) < 1e-6
    
    def test_coherent_complexity_reduces_classical(self):
        """Test that coherent complexity is less than classical in grace state."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        classical = 1e6
        coherent = simulator.coherent_complexity(state, classical)
        
        assert coherent < classical
    
    def test_simulate_bifurcation(self):
        """Test bifurcation simulation."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        bifurcation = simulator.simulate_bifurcation(ProblemType.SAT, 15, state)
        
        assert isinstance(bifurcation, BifurcationPoint)
        assert bifurcation.coherence == 0.95
        assert bifurcation.problem_type == ProblemType.SAT
        assert bifurcation.reduction_factor > 1.0  # Grace state should reduce
    
    def test_bifurcation_increases_with_coherence(self):
        """Test that reduction factor increases with coherence."""
        simulator = NPPBifurcationSimulator()
        
        state_low = ComplexityState(coherence=0.5, information=1.5, amplitude_eff=1.2)
        state_high = ComplexityState(coherence=0.95, information=1.5, amplitude_eff=1.2)
        
        bif_low = simulator.simulate_bifurcation(ProblemType.SAT, 15, state_low)
        bif_high = simulator.simulate_bifurcation(ProblemType.SAT, 15, state_high)
        
        # Higher coherence should give better reduction
        assert bif_high.reduction_factor > bif_low.reduction_factor


class TestRiemannZeroSearch:
    """Test Riemann zero search functionality."""
    
    def test_classical_search(self):
        """Test classical Riemann zero search."""
        simulator = NPPBifurcationSimulator()
        
        iterations, precision = simulator.riemann_zero_classical_search(
            zero_index=10,
            target_height=50.0
        )
        
        assert iterations > 0
        assert precision > 0
    
    def test_coherent_search(self):
        """Test coherent Riemann zero search."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        iterations, precision, freq, discrepancy = simulator.riemann_zero_coherent_search(
            zero_index=10,
            target_height=50.0,
            state=state
        )
        
        assert iterations > 0
        assert precision > 0
        assert freq > 0
        assert discrepancy >= 0
    
    def test_coherent_faster_than_classical(self):
        """Test that coherent search is faster than classical in grace state."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        
        classical_iters, _ = simulator.riemann_zero_classical_search(100, 500.0)
        coherent_iters, _, _, _ = simulator.riemann_zero_coherent_search(100, 500.0, state)
        
        assert coherent_iters < classical_iters
    
    def test_search_riemann_zero(self):
        """Test complete Riemann zero search."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        search = simulator.search_riemann_zero(10, 50.0, state)
        
        assert isinstance(search, RiemannZeroSearch)
        assert search.zero_index == 10
        assert search.target_height == 50.0
        assert search.coherent_iterations < search.classical_iterations
        assert search.coherent_precision_required < search.classical_precision_required
    
    def test_discrepancy_decreases_with_coherence(self):
        """Test that discrepancy decreases as coherence increases."""
        simulator = NPPBifurcationSimulator()
        
        state_low = ComplexityState(coherence=0.7, information=1.5, amplitude_eff=1.2)
        state_high = ComplexityState(coherence=0.95, information=1.5, amplitude_eff=1.2)
        
        search_low = simulator.search_riemann_zero(10, 50.0, state_low)
        search_high = simulator.search_riemann_zero(10, 50.0, state_high)
        
        assert search_high.discrepancy < search_low.discrepancy


class TestBifurcationAnalysis:
    """Test bifurcation landscape analysis."""
    
    def test_analyze_bifurcation_landscape(self):
        """Test bifurcation landscape analysis."""
        simulator = NPPBifurcationSimulator()
        
        results = simulator.analyze_bifurcation_landscape(
            problem_type=ProblemType.SAT,
            problem_sizes=[10, 15, 20],
            coherence_values=[0.3, 0.7, 0.95],
            information=1.5,
            amplitude_eff=1.2
        )
        
        # Should have 3 sizes × 3 coherences = 9 results
        assert len(results) == 9
        
        # All should be BifurcationPoint instances
        assert all(isinstance(r, BifurcationPoint) for r in results)
    
    def test_get_regime_bifurcations(self):
        """Test getting bifurcations by regime."""
        simulator = NPPBifurcationSimulator()
        
        # Create bifurcations in different regimes
        from complexity_collapser import ComputationalRegime
        
        states = [
            ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0),
            ComplexityState(coherence=0.7, information=1.0, amplitude_eff=1.0),
            ComplexityState(coherence=0.95, information=1.0, amplitude_eff=1.0)
        ]
        
        for state in states:
            simulator.simulate_bifurcation(ProblemType.SAT, 15, state)
        
        classical_bifs = simulator.get_regime_bifurcations(ComputationalRegime.CLASSICAL)
        transition_bifs = simulator.get_regime_bifurcations(ComputationalRegime.TRANSITION)
        grace_bifs = simulator.get_regime_bifurcations(ComputationalRegime.GRACE)
        
        assert len(classical_bifs) >= 1
        assert len(transition_bifs) >= 1
        assert len(grace_bifs) >= 1
    
    def test_save_analysis(self, tmp_path):
        """Test saving bifurcation analysis."""
        simulator = NPPBifurcationSimulator()
        
        state = ComplexityState(coherence=0.95, information=2.0, amplitude_eff=1.5)
        simulator.simulate_bifurcation(ProblemType.SAT, 15, state)
        simulator.search_riemann_zero(10, 50.0, state)
        
        output_file = tmp_path / "bifurcation.json"
        simulator.save_analysis(str(output_file))
        
        assert output_file.exists()
        
        # Verify it's valid JSON
        import json
        with open(output_file) as f:
            data = json.load(f)
        
        assert "metadata" in data
        assert "bifurcations" in data
        assert "riemann_searches" in data


class TestGraceBifurcationThreshold:
    """Test the grace state bifurcation threshold."""
    
    def test_below_threshold_poor_reduction(self):
        """Test that below threshold gives poor reduction."""
        simulator = NPPBifurcationSimulator()
        
        # Just below threshold
        state = ComplexityState(coherence=0.85, information=1.5, amplitude_eff=1.2)
        bifurcation = simulator.simulate_bifurcation(ProblemType.SAT, 15, state)
        
        # Should have some reduction but not dramatic
        assert bifurcation.reduction_factor > 0
    
    def test_above_threshold_strong_reduction(self):
        """Test that above threshold gives strong reduction."""
        simulator = NPPBifurcationSimulator()
        
        # Above threshold
        state = ComplexityState(coherence=0.92, information=2.0, amplitude_eff=1.5)
        bifurcation = simulator.simulate_bifurcation(ProblemType.SAT, 15, state)
        
        # Should have strong reduction in grace state
        assert bifurcation.reduction_factor > 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
