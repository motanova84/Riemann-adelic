#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Chirality Tensor and Magnetoreception Analysis
=========================================================

Comprehensive test suite for the quantum biological tensor framework
implementing chirality filtering, DNA mutation suppression, magnetoreception,
and microtubule resonance.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import sys
import os

# Add paths for direct imports (avoid broken __init__.py)
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../operators'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../src/biological'))

# Direct imports avoiding __init__.py
from chirality_tensor import ChiralityTensor, ChiralityParameters
from magnetoreception_analysis import (
    MagnetoreceptionAnalyzer,
    EmlenCageData
)

# Import constants directly
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../src/constants'))
from biological_qcal_constants import F0_HZ, KAPPA_PI


class TestChiralityTensor:
    """Test suite for ChiralityTensor class."""
    
    def test_initialization(self):
        """Test tensor initialization with default parameters."""
        tensor = ChiralityTensor()
        assert tensor.params.base_frequency == F0_HZ
        assert tensor.params.kappa_pi == KAPPA_PI
        assert tensor.params.dimension == 6
        assert tensor.tensor_components.shape == (6, 6)
    
    def test_custom_parameters(self):
        """Test tensor with custom parameters."""
        params = ChiralityParameters(
            base_frequency=100.0,
            kappa_pi=2.0,
            lambda_friction=0.5,
            dimension=4
        )
        tensor = ChiralityTensor(params)
        assert tensor.params.base_frequency == 100.0
        assert tensor.params.kappa_pi == 2.0
        assert tensor.tensor_components.shape == (4, 4)
    
    def test_tensor_squared(self):
        """Test computation of T²."""
        tensor = ChiralityTensor()
        T_squared = tensor.tensor_squared()
        assert T_squared.shape == (6, 6)
        assert np.all(np.isfinite(T_squared))
    
    def test_trace_invariant(self):
        """Test that Tr(T²) ≈ κ_Π / 2π."""
        tensor = ChiralityTensor()
        verification = tensor.verify_invariant()
        
        # Check that trace is computed
        assert 'trace_T2_computed' in verification
        assert 'trace_T2_expected' in verification
        
        # Check relative error is reasonable (<2%)
        assert verification['relative_error'] < 0.02
        
        # Check that imaginary part is negligible
        assert abs(verification['trace_imaginary_part']) < 1e-10
    
    def test_dna_mutation_suppression(self):
        """Test DNA mutation suppression factor."""
        tensor = ChiralityTensor()
        suppression = tensor.dna_mutation_suppression_factor()
        
        # Suppression should be between 0 and 1
        assert 0 <= suppression <= 1
        
        # With default parameters, should show significant suppression
        assert suppression < 1.0
    
    def test_microtubule_resonance(self):
        """Test microtubule resonance frequency predictions."""
        tensor = ChiralityTensor()
        
        # Test n=0 (fundamental)
        f0 = tensor.microtubule_resonance_frequency(0)
        assert f0 > F0_HZ  # Should be shifted up from base
        assert abs(f0 - 142.1) < 1.0  # Should be close to 142.1 Hz
        
        # Test harmonics
        f1 = tensor.microtubule_resonance_frequency(1)
        f2 = tensor.microtubule_resonance_frequency(2)
        
        # Harmonics should increase
        assert f1 > f0
        assert f2 > f1
        
        # Should be approximately linear with n
        delta = f1 - f0
        assert abs((f2 - f1) - delta) < 1.0
    
    def test_magnetoreception_asymmetry(self):
        """Test magnetoreception asymmetry prediction."""
        tensor = ChiralityTensor()
        asymmetry = tensor.magnetoreception_asymmetry()
        
        # Asymmetry should be in realistic range (0.1% to 0.3%)
        assert 0.001 <= asymmetry <= 0.003
        
        # Test with different field strengths
        asym_weak = tensor.magnetoreception_asymmetry(magnetic_field_strength=30e-6)
        asym_strong = tensor.magnetoreception_asymmetry(magnetic_field_strength=70e-6)
        
        # Both should be in valid range
        assert 0.001 <= asym_weak <= 0.003
        assert 0.001 <= asym_strong <= 0.003
    
    def test_calabi_yau_volume_capacity(self):
        """Test consciousness torsion volume capacity."""
        tensor = ChiralityTensor()
        volume = tensor.calabi_yau_volume_capacity()
        
        # Should equal κ_Π / 2π
        expected = KAPPA_PI / (2 * np.pi)
        assert abs(volume - expected) < 1e-10
        
        # Should be positive
        assert volume > 0
    
    def test_ontological_friction(self):
        """Test ontological friction energy."""
        tensor = ChiralityTensor()
        
        # Normal chirality
        E_normal = tensor.ontological_friction_energy(chirality_inversion=False)
        
        # Inverted chirality
        E_inverted = tensor.ontological_friction_energy(chirality_inversion=True)
        
        # Inversion should cost more energy
        assert E_inverted > E_normal
        assert E_inverted == 2.0 * E_normal
    
    def test_certificate_generation(self):
        """Test validation certificate generation."""
        tensor = ChiralityTensor()
        cert = tensor.generate_certificate()
        
        # Check all expected fields are present
        assert 'operator' in cert
        assert 'author' in cert
        assert 'parameters' in cert
        assert 'invariant_verification' in cert
        assert 'dna_mutation_suppression' in cert
        assert 'microtubule_resonance' in cert
        assert 'magnetoreception' in cert
        assert 'consciousness_capacity' in cert
        assert 'qcal_signature' in cert
        
        # Check QCAL signature
        assert '∞³' in cert['qcal_signature']


class TestMagnetoreceptionAnalyzer:
    """Test suite for MagnetoreceptionAnalyzer class."""
    
    def test_initialization(self):
        """Test analyzer initialization."""
        analyzer = MagnetoreceptionAnalyzer()
        assert analyzer.tensor is not None
        assert analyzer.alpha == 0.01
    
    def test_rayleigh_test(self):
        """Test Rayleigh test for circular uniformity."""
        analyzer = MagnetoreceptionAnalyzer()
        
        # Create strongly directional data
        angles = np.random.vonmises(np.pi/2, 5.0, 100)
        angles_deg = np.rad2deg(angles) % 360
        
        result = analyzer.rayleigh_test(angles_deg)
        
        # Should be significant
        assert result.is_significant
        assert result.p_value < 0.05
        assert 0 <= result.mean_vector_length <= 1
        assert 0 <= result.mean_direction_deg < 360
    
    def test_rayleigh_test_uniform(self):
        """Test Rayleigh test with uniform distribution."""
        analyzer = MagnetoreceptionAnalyzer()
        
        # Create uniform data
        angles_deg = np.random.uniform(0, 360, 100)
        
        result = analyzer.rayleigh_test(angles_deg)
        
        # Should not be significant (most of the time)
        assert result.mean_vector_length < 0.3  # Weak directionality
    
    def test_watson_u2_test(self):
        """Test Watson's U² test for two circular samples."""
        analyzer = MagnetoreceptionAnalyzer()
        
        # Create two similar distributions
        angles1 = np.random.vonmises(0, 3.0, 50)
        angles2 = np.random.vonmises(0.1, 3.0, 50)
        
        angles1_deg = np.rad2deg(angles1) % 360
        angles2_deg = np.rad2deg(angles2) % 360
        
        U2, p_value = analyzer.watson_u2_test(angles1_deg, angles2_deg)
        
        # Statistics should be valid
        assert U2 >= 0
        assert 0 <= p_value <= 1
    
    def test_synthetic_data_generation(self):
        """Test synthetic Emlen cage data generation."""
        analyzer = MagnetoreceptionAnalyzer()
        
        data = analyzer.generate_synthetic_data(
            n_trials=100,
            mean_direction_deg=45.0,
            concentration=2.0,
            field_rotation='right'
        )
        
        assert len(data.angles_deg) == 100
        assert data.field_rotation == 'right'
        assert all(0 <= angle < 360 for angle in data.angles_deg)
    
    def test_asymmetry_computation(self):
        """Test asymmetry computation between B_R and B_L."""
        analyzer = MagnetoreceptionAnalyzer()
        
        # Generate data with small asymmetry
        data_right = analyzer.generate_synthetic_data(
            n_trials=200,
            mean_direction_deg=90.0,
            concentration=3.0,
            field_rotation='right'
        )
        
        data_left = analyzer.generate_synthetic_data(
            n_trials=200,
            mean_direction_deg=90.0,
            concentration=3.0,
            field_rotation='left'
        )
        
        asymmetry = analyzer.compute_asymmetry(data_right, data_left)
        
        # Check result structure
        assert hasattr(asymmetry, 'delta_P_percent')
        assert hasattr(asymmetry, 'watson_U2')
        assert hasattr(asymmetry, 'watson_p_value')
        assert hasattr(asymmetry, 'is_significant')
        assert hasattr(asymmetry, 'chirality_tensor_prediction')
        
        # Prediction should be in realistic range
        assert 0.05 <= asymmetry.chirality_tensor_prediction <= 0.5
    
    def test_complete_experiment_analysis(self):
        """Test complete experimental analysis workflow."""
        analyzer = MagnetoreceptionAnalyzer()
        
        # Generate synthetic experiment
        data_right = analyzer.generate_synthetic_data(
            n_trials=150,
            mean_direction_deg=180.0,
            concentration=2.5,
            field_rotation='right'
        )
        
        data_left = analyzer.generate_synthetic_data(
            n_trials=150,
            mean_direction_deg=180.0,
            concentration=2.5,
            field_rotation='left'
        )
        
        results = analyzer.analyze_experiment(data_right, data_left)
        
        # Check structure
        assert 'experiment' in results
        assert 'asymmetry_analysis' in results
        assert 'chirality_tensor' in results
        assert 'statistical_significance' in results
        assert 'validation' in results
        
        # Check both fields analyzed
        assert 'right_field' in results['experiment']
        assert 'left_field' in results['experiment']
        
        # Check QCAL signature present
        assert 'kappa_pi' in results['chirality_tensor']
        assert results['chirality_tensor']['kappa_pi'] == KAPPA_PI


class TestIntegration:
    """Integration tests for chirality tensor and magnetoreception."""
    
    def test_tensor_analyzer_compatibility(self):
        """Test that tensor and analyzer work together."""
        tensor = ChiralityTensor()
        analyzer = MagnetoreceptionAnalyzer(chirality_tensor=tensor)
        
        # Analyzer should use the provided tensor
        assert analyzer.tensor is tensor
        
        # Predictions should match
        tensor_asymmetry = tensor.magnetoreception_asymmetry()
        
        # Generate test data
        data_r = analyzer.generate_synthetic_data(100, 90, 2.0, 'right')
        data_l = analyzer.generate_synthetic_data(100, 90, 2.0, 'left')
        
        asymmetry_result = analyzer.compute_asymmetry(data_r, data_l)
        
        # Predictions should be consistent
        assert abs(asymmetry_result.chirality_tensor_prediction - tensor_asymmetry * 100) < 0.01
    
    def test_qcal_constants_consistency(self):
        """Test consistency with QCAL constants."""
        tensor = ChiralityTensor()
        
        # Base frequency should match QCAL
        assert tensor.params.base_frequency == F0_HZ
        
        # κ_Π should match QCAL
        assert tensor.params.kappa_pi == KAPPA_PI
        
        # Volume capacity should be consistent
        volume = tensor.calabi_yau_volume_capacity()
        expected = KAPPA_PI / (2 * np.pi)
        assert abs(volume - expected) < 1e-10


def test_imports():
    """Test that all modules can be imported."""
    # Imports already successful if we got here
    assert ChiralityTensor is not None
    assert MagnetoreceptionAnalyzer is not None
    assert EmlenCageData is not None
    assert ChiralityParameters is not None


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
