#!/usr/bin/env python3
"""
Test Suite for Quantum Phase Shift δζ

This test suite validates the implementation of the quantum phase shift
δζ ≈ 0.2787437 Hz and its role in transforming the Euclidean diagonal
into the cosmic string.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
from quantum_phase_shift import QuantumPhaseShift


class TestQuantumPhaseShift:
    """Test cases for QuantumPhaseShift class."""
    
    @pytest.fixture
    def qps(self):
        """Create a QuantumPhaseShift instance with high precision."""
        return QuantumPhaseShift(precision_dps=30)
    
    def test_fundamental_constants(self, qps):
        """Test that fundamental constants are correctly defined."""
        assert abs(qps.QCAL_BASE_FREQUENCY - 141.7001) < 1e-10
        assert abs(qps.EUCLIDEAN_BASE - 100.0) < 1e-10
        assert qps.COHERENCE_C == 244.36
    
    def test_euclidean_diagonal_computation(self, qps):
        """Test that 100√2 is computed correctly."""
        expected_diagonal = 141.4213562373095
        computed_diagonal = float(qps.euclidean_diagonal)
        
        assert abs(computed_diagonal - expected_diagonal) < 1e-10
    
    def test_delta_zeta_computation(self, qps):
        """Test that δζ is computed correctly from f₀ - 100√2."""
        expected_delta_zeta = 0.2787437627
        computed_delta_zeta = float(qps.delta_zeta)
        
        assert abs(computed_delta_zeta - expected_delta_zeta) < 1e-8
    
    def test_fundamental_relationship(self, qps):
        """Test the fundamental relationship: f₀ = 100√2 + δζ"""
        validation = qps.validate_frequency_relationship()
        
        assert validation['validation_passed'] == True
        assert validation['relative_error'] < 1e-10
        assert validation['phase_coherence'] > 0.999999999
        
        # Verify individual components
        euclidean = validation['euclidean_diagonal_hz']
        delta = validation['delta_zeta_hz']
        computed_f0 = validation['computed_f0_hz']
        expected_f0 = validation['expected_f0_hz']
        
        assert abs((euclidean + delta) - expected_f0) < 1e-10
    
    def test_euclidean_to_cosmic_without_shift(self, qps):
        """Test Euclidean to cosmic transformation without phase shift."""
        freq = 100.0
        result = qps.euclidean_to_cosmic_transform(freq, apply_phase_shift=False)
        
        assert result['input_frequency_hz'] == freq
        assert result['euclidean_component_hz'] == freq
        assert result['cosmic_frequency_hz'] == freq
        assert result['delta_zeta_applied_hz'] == 0.0
    
    def test_euclidean_to_cosmic_with_shift(self, qps):
        """Test Euclidean to cosmic transformation with phase shift."""
        freq = 100.0
        result = qps.euclidean_to_cosmic_transform(freq, apply_phase_shift=True)
        
        expected_cosmic = freq + float(qps.delta_zeta)
        
        assert result['input_frequency_hz'] == freq
        assert abs(result['cosmic_frequency_hz'] - expected_cosmic) < 1e-8
        assert abs(result['delta_zeta_applied_hz'] - float(qps.delta_zeta)) < 1e-8
    
    def test_euclidean_diagonal_perfect_transform(self, qps):
        """Test that Euclidean diagonal transforms to f₀ perfectly."""
        euclidean_diagonal = float(qps.euclidean_diagonal)
        result = qps.euclidean_to_cosmic_transform(euclidean_diagonal)
        
        # Should transform to exactly f₀
        expected_f0 = float(qps.f0)
        computed_cosmic = result['cosmic_frequency_hz']
        
        assert abs(computed_cosmic - expected_f0) < 1e-8
        assert result['is_resonant'] == True
        assert result['coherence_with_f0'] > 0.999999
    
    def test_riemann_zero_phases(self, qps):
        """Test computation of quantum phases for Riemann zeros."""
        # Use first few known Riemann zeros
        riemann_zeros = np.array([
            14.134725141734693,
            21.022039638771555,
            25.010857580145688,
            30.424876125859513,
            32.935061587739189
        ])
        
        result = qps.compute_riemann_zero_phases(riemann_zeros)
        
        assert result['n_zeros'] == len(riemann_zeros)
        assert len(result['quantum_phases']) == len(riemann_zeros)
        assert len(result['coherences']) == len(riemann_zeros)
        
        # All coherences should be positive
        assert all(c > 0 for c in result['coherences'])
        
        # Mean coherence should be reasonable
        assert 0 < result['mean_coherence'] < 1
    
    def test_cosmic_string_tension(self, qps):
        """Test cosmic string tension computation."""
        tension = qps.cosmic_string_tension()
        
        # Tension ratio should be small (δζ/f₀)²
        expected_ratio = (float(qps.delta_zeta) / float(qps.f0)) ** 2
        assert abs(tension['tension_ratio'] - expected_ratio) < 1e-10
        
        # Energy scale should be δζ·f₀
        expected_energy = float(qps.delta_zeta) * float(qps.f0)
        assert abs(tension['energy_scale_hz2'] - expected_energy) < 1e-6
        
        # Coherence length should be 1/δζ
        expected_length = 1.0 / float(qps.delta_zeta)
        assert abs(tension['coherence_length'] - expected_length) < 1e-6
    
    def test_certificate_generation(self, qps):
        """Test mathematical certificate generation."""
        cert = qps.generate_certificate()
        
        # Check required fields
        assert 'title' in cert
        assert 'fundamental_relationship' in cert
        assert 'constants' in cert
        assert 'validation' in cert
        assert 'cosmic_string' in cert
        
        # Check fundamental relationship
        assert cert['fundamental_relationship'] == 'f₀ = 100√2 + δζ'
        
        # Check constants
        constants = cert['constants']
        assert 'f0_hz' in constants
        assert 'euclidean_diagonal_hz' in constants
        assert 'delta_zeta_hz' in constants
        
        # Check validation passed
        assert cert['validation']['validation_passed'] == True
        
        # Check author and signature
        assert 'José Manuel Mota Burruezo' in cert['author']
        assert 'QCAL' in cert['signature']
    
    def test_precision_consistency(self):
        """Test that different precisions give consistent results."""
        qps_low = QuantumPhaseShift(precision_dps=15)
        qps_high = QuantumPhaseShift(precision_dps=50)
        
        val_low = qps_low.validate_frequency_relationship()
        val_high = qps_high.validate_frequency_relationship()
        
        # Both should pass validation
        assert val_low['validation_passed'] == True
        assert val_high['validation_passed'] == True
        
        # Results should agree to low precision
        delta_diff = abs(val_low['delta_zeta_hz'] - val_high['delta_zeta_hz'])
        assert delta_diff < 1e-10
    
    def test_coherence_at_f0(self, qps):
        """Test that coherence is maximum at f₀."""
        f0 = float(qps.f0)
        
        # Transform f₀ without shift
        result_f0 = qps.euclidean_to_cosmic_transform(f0, apply_phase_shift=False)
        
        # Transform nearby frequencies
        result_lower = qps.euclidean_to_cosmic_transform(f0 - 1.0, apply_phase_shift=False)
        result_higher = qps.euclidean_to_cosmic_transform(f0 + 1.0, apply_phase_shift=False)
        
        # f₀ should have highest coherence
        coh_f0 = result_f0['coherence_with_f0']
        coh_lower = result_lower['coherence_with_f0']
        coh_higher = result_higher['coherence_with_f0']
        
        assert coh_f0 > coh_lower
        assert coh_f0 > coh_higher
        assert abs(coh_f0 - 1.0) < 1e-10
    
    def test_phase_shift_sign(self, qps):
        """Test that δζ has the correct sign (positive)."""
        delta_zeta = float(qps.delta_zeta)
        
        # δζ should be positive
        assert delta_zeta > 0
        
        # It should be the difference f₀ - 100√2
        expected = qps.QCAL_BASE_FREQUENCY - 100.0 * np.sqrt(2)
        assert abs(delta_zeta - expected) < 1e-8


class TestDeltaZetaIntegration:
    """Integration tests for δζ with QCAL framework."""
    
    def test_qcal_beacon_consistency(self):
        """Test consistency with .qcal_beacon values."""
        qps = QuantumPhaseShift(precision_dps=25)
        
        # These values should match .qcal_beacon
        assert abs(float(qps.f0) - 141.7001) < 1e-10
        assert abs(float(qps.delta_zeta) - 0.2787437627) < 1e-6
        assert abs(float(qps.euclidean_diagonal) - 141.4213562373) < 1e-8
    
    def test_frequency_transformation_reversibility(self):
        """Test that Euclidean → Cosmic transformation is reversible."""
        qps = QuantumPhaseShift(precision_dps=25)
        
        # Start with Euclidean diagonal
        euclidean = float(qps.euclidean_diagonal)
        
        # Transform to cosmic (should give f₀)
        result_forward = qps.euclidean_to_cosmic_transform(euclidean, apply_phase_shift=True)
        cosmic = result_forward['cosmic_frequency_hz']
        
        # Reverse transform (subtract δζ)
        reverse_euclidean = cosmic - float(qps.delta_zeta)
        
        # Should recover original Euclidean frequency
        assert abs(reverse_euclidean - euclidean) < 1e-8


def test_module_import():
    """Test that the module can be imported without errors."""
    from quantum_phase_shift import QuantumPhaseShift
    assert QuantumPhaseShift is not None


def test_demo_execution():
    """Test that the demo function runs without errors."""
    from quantum_phase_shift import demo_quantum_phase_shift
    
    # Should run without raising exceptions
    try:
        demo_quantum_phase_shift()
        success = True
    except Exception as e:
        success = False
        print(f"Demo failed: {e}")
    
    assert success


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
