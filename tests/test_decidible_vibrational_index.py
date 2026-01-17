#!/usr/bin/env python3
"""
Test suite for Decidible Vibrational Index ΔΨ(t)
================================================

Tests the decidible vibrational manifestation of Riemann zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: January 17, 2025
"""

import pytest
import numpy as np
from pathlib import Path
import json
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from decidible_vibrational_index import (
    DecidibleVibrationalIndex,
    VibrationalState,
    QCAL_BASE_FREQUENCY,
    COHERENCE_CONSTANT_C,
    ZERO_THRESHOLD,
)


class TestDecidibleVibrationalIndex:
    """Test suite for the decidible vibrational index."""
    
    @pytest.fixture
    def calculator(self):
        """Create a calculator instance for tests."""
        return DecidibleVibrationalIndex(precision=30)
    
    @pytest.fixture
    def known_zeros(self):
        """First few known Riemann zeros (imaginary parts)."""
        return [
            14.134725141734693790457251983562,
            21.022039638771554992628479593897,
            25.010857580145688763213790992563,
            30.424876125859513210311897530584,
            32.935061587739189690662368964074,
        ]
    
    def test_initialization(self, calculator):
        """Test that calculator initializes correctly."""
        assert calculator.precision == 30
        assert calculator.f0 == QCAL_BASE_FREQUENCY
        assert calculator.C == COHERENCE_CONSTANT_C
        assert calculator.critical_re == 0.5
    
    def test_compute_zeta_magnitude_at_zero(self, calculator, known_zeros):
        """Test that zeta magnitude is very small at known zeros."""
        for t in known_zeros[:3]:  # Test first 3 for speed
            magnitude = calculator.compute_zeta_magnitude(t)
            assert magnitude < ZERO_THRESHOLD, \
                f"At known zero t={t}, |ζ| = {magnitude} should be < {ZERO_THRESHOLD}"
    
    def test_compute_zeta_magnitude_at_non_zero(self, calculator):
        """Test that zeta magnitude is significant at non-zero points."""
        non_zeros = [15.0, 20.0, 22.5, 28.0]
        for t in non_zeros:
            magnitude = calculator.compute_zeta_magnitude(t)
            assert magnitude > ZERO_THRESHOLD, \
                f"At non-zero t={t}, |ζ| = {magnitude} should be > {ZERO_THRESHOLD}"
    
    def test_compute_index_at_zeros(self, calculator, known_zeros):
        """Test that ΔΨ(t) = 1 at known zeros."""
        for t in known_zeros[:3]:
            delta_psi = calculator.compute_index(t)
            assert delta_psi == 1, \
                f"At known zero t={t}, ΔΨ should be 1, got {delta_psi}"
    
    def test_compute_index_at_non_zeros(self, calculator):
        """Test that ΔΨ(t) = 0 at non-zero points."""
        non_zeros = [15.0, 20.0, 22.5]
        for t in non_zeros:
            delta_psi = calculator.compute_index(t)
            assert delta_psi == 0, \
                f"At non-zero t={t}, ΔΨ should be 0, got {delta_psi}"
    
    def test_classify_resonance_strong(self, calculator):
        """Test strong resonance classification."""
        # Use actual zero for strong resonance
        magnitude = 1e-16
        resonance = calculator.classify_resonance(magnitude)
        assert "STRONG" in resonance
    
    def test_classify_resonance_medium(self, calculator):
        """Test medium resonance classification."""
        magnitude = 1e-11
        resonance = calculator.classify_resonance(magnitude)
        assert "MEDIUM" in resonance
    
    def test_classify_resonance_weak(self, calculator):
        """Test weak resonance classification."""
        magnitude = 1e-7
        resonance = calculator.classify_resonance(magnitude)
        assert "WEAK" in resonance
    
    def test_classify_resonance_none(self, calculator):
        """Test no resonance classification."""
        magnitude = 0.1
        resonance = calculator.classify_resonance(magnitude)
        assert "NONE" in resonance
    
    def test_vibrational_frequency(self, calculator):
        """Test vibrational frequency calculation."""
        # At t=0, frequency should be f₀
        f_zero = calculator.vibrational_frequency(0.0)
        assert abs(f_zero - QCAL_BASE_FREQUENCY) < 0.01
        
        # Frequency should increase with t
        t1, t2 = 10.0, 20.0
        f1 = calculator.vibrational_frequency(t1)
        f2 = calculator.vibrational_frequency(t2)
        assert f2 > f1, "Frequency should increase with t"
    
    def test_evaluate_state_at_zero(self, calculator, known_zeros):
        """Test complete state evaluation at a known zero."""
        t = known_zeros[0]
        state = calculator.evaluate_state(t)
        
        assert isinstance(state, VibrationalState)
        assert state.t == t
        assert state.delta_psi == 1, "ΔΨ should be 1 at zero"
        assert state.is_sound is True, "Universe should sound at zero"
        assert state.quantum_collapse is True, "Quantum collapse at zero"
        assert state.zeta_magnitude < ZERO_THRESHOLD
    
    def test_evaluate_state_at_non_zero(self, calculator):
        """Test complete state evaluation at a non-zero point."""
        t = 15.0
        state = calculator.evaluate_state(t)
        
        assert isinstance(state, VibrationalState)
        assert state.t == t
        assert state.delta_psi == 0, "ΔΨ should be 0 at non-zero"
        assert state.is_sound is False, "Universe should be silent at non-zero"
        assert state.quantum_collapse is False, "No quantum collapse"
        assert state.zeta_magnitude > ZERO_THRESHOLD
    
    def test_scan_interval(self, calculator):
        """Test interval scanning."""
        states = calculator.scan_interval(10.0, 30.0, num_points=100)
        
        assert len(states) == 100
        assert all(isinstance(s, VibrationalState) for s in states)
        
        # Check that t values are in correct range
        t_values = [s.t for s in states]
        assert min(t_values) >= 10.0
        assert max(t_values) <= 30.0
    
    def test_find_zeros_in_interval(self, calculator):
        """Test finding zeros in an interval."""
        # Interval [14, 26] should contain first two zeros
        zeros_found = calculator.find_zeros_in_interval(14.0, 26.0)
        
        assert len(zeros_found) >= 2, "Should find at least 2 zeros in this interval"
        
        for t_zero, state in zeros_found:
            assert state.delta_psi == 1, f"Found zero at t={t_zero} should have ΔΨ=1"
            assert 14.0 <= t_zero <= 26.0, "Zero should be in interval"
    
    def test_verify_known_zeros(self, calculator, known_zeros):
        """Test verification of known zeros."""
        results = calculator.verify_known_zeros(known_zeros[:3], max_check=3)
        
        assert results['total_checked'] == 3
        assert results['confirmed'] >= 2, "Should confirm at least 2 out of 3"
        assert results['success_rate'] >= 0.66
        assert len(results['details']) == 3
    
    def test_export_state(self, calculator, tmp_path):
        """Test exporting vibrational state to JSON."""
        state = calculator.evaluate_state(14.134725141734693790457251983562)
        filepath = tmp_path / "test_state.json"
        
        calculator.export_state(state, filepath)
        
        assert filepath.exists()
        
        with open(filepath) as f:
            data = json.load(f)
        
        assert 't' in data
        assert 'delta_psi' in data
        assert 'qcal_framework' in data
        assert data['qcal_framework']['base_frequency'] == QCAL_BASE_FREQUENCY
    
    def test_vibrational_state_string_representation(self, calculator):
        """Test string representation of VibrationalState."""
        state = calculator.evaluate_state(14.134725141734693790457251983562)
        state_str = str(state)
        
        assert "ΔΨ" in state_str
        assert "SOUND" in state_str or "SILENCE" in state_str
        assert "Resonance" in state_str
        assert "Frequency" in state_str
    
    def test_qcal_integration(self, calculator):
        """Test QCAL framework integration."""
        # Verify QCAL constants are properly integrated
        assert calculator.f0 == 141.7001
        assert calculator.C == 244.36
        
        # Verify frequency calculation uses QCAL base
        freq = calculator.vibrational_frequency(0.0)
        assert abs(freq - 141.7001) < 0.01


class TestVibrationalPhysics:
    """Test vibrational physics interpretations."""
    
    @pytest.fixture
    def calculator(self):
        return DecidibleVibrationalIndex(precision=30)
    
    def test_sound_vs_silence(self, calculator):
        """Test universe sound vs silence at zeros and non-zeros."""
        # At zero: sound
        zero_state = calculator.evaluate_state(14.134725141734693790457251983562)
        assert zero_state.is_sound is True
        
        # At non-zero: silence
        non_zero_state = calculator.evaluate_state(15.0)
        assert non_zero_state.is_sound is False
    
    def test_quantum_collapse(self, calculator):
        """Test quantum collapse at zeros."""
        # At zero: quantum collapse (black hole)
        zero_state = calculator.evaluate_state(14.134725141734693790457251983562)
        assert zero_state.quantum_collapse is True
        
        # At non-zero: no collapse (stable vacuum)
        non_zero_state = calculator.evaluate_state(15.0)
        assert non_zero_state.quantum_collapse is False
    
    def test_resonance_levels(self, calculator):
        """Test different resonance levels."""
        # Strong resonance at actual zero
        zero_state = calculator.evaluate_state(14.134725141734693790457251983562)
        assert "STRONG" in zero_state.resonance_level
        
        # No resonance far from zero
        far_state = calculator.evaluate_state(15.0)
        # Should be weak or none
        assert "WEAK" in far_state.resonance_level or "NONE" in far_state.resonance_level


class TestNumericalAccuracy:
    """Test numerical accuracy and precision."""
    
    @pytest.fixture
    def calculator_high_precision(self):
        return DecidibleVibrationalIndex(precision=100)
    
    def test_high_precision_at_zero(self, calculator_high_precision):
        """Test high precision calculation at known zero."""
        t = 14.134725141734693790457251983562
        magnitude = calculator_high_precision.compute_zeta_magnitude(t)
        
        # With 100 digit precision, should be extremely small
        assert magnitude < 1e-20
    
    def test_consistency_across_precisions(self):
        """Test consistency of index across different precisions."""
        t = 14.134725141734693790457251983562
        
        calc_30 = DecidibleVibrationalIndex(precision=30)
        calc_50 = DecidibleVibrationalIndex(precision=50)
        
        index_30 = calc_30.compute_index(t)
        index_50 = calc_50.compute_index(t)
        
        # Should both return 1 (zero exists)
        assert index_30 == index_50 == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
