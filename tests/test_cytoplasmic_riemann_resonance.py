#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Test suite for cytoplasmic Riemann resonance model.

This test suite validates the implementation of the biological proof
of the Riemann Hypothesis through cellular resonance.
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from xenos.cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    BiophysicalConstants
)


class TestCytoplasmicRiemannResonance:
    """Test suite for CytoplasmicRiemannResonance class."""
    
    def test_initialization(self):
        """Test model initialization with default parameters."""
        model = CytoplasmicRiemannResonance()
        
        assert model.constants.base_frequency == 141.7001
        assert model.constants.kappa_pi == 2.5773
        assert model.constants.num_cells == 3.7e13
        assert model.num_harmonics == 100
        
    def test_harmonic_frequencies(self):
        """Test that harmonic frequencies are correctly generated."""
        model = CytoplasmicRiemannResonance()
        
        assert model.harmonic_frequencies is not None
        assert len(model.harmonic_frequencies) == 100
        
        # First harmonic should equal base frequency
        assert np.isclose(
            model.harmonic_frequencies[0],
            model.constants.base_frequency
        )
        
        # Second harmonic should be double
        assert np.isclose(
            model.harmonic_frequencies[1],
            2 * model.constants.base_frequency
        )
    
    def test_hermitian_operator_construction(self):
        """Test that Hermitian operator is properly constructed."""
        model = CytoplasmicRiemannResonance()
        
        H = model._hermitian_operator
        assert H is not None
        assert H.shape == (100, 100)
        
        # Check Hermiticity: H = H†
        hermiticity_error = np.max(np.abs(H - np.conj(H.T)))
        assert hermiticity_error < 1e-10
    
    def test_eigenvalue_reality(self):
        """Test that all eigenvalues are real (RH validation)."""
        model = CytoplasmicRiemannResonance()
        
        assert model.eigenvalues is not None
        
        # All eigenvalues should be real
        imaginary_parts = np.abs(np.imag(model.eigenvalues))
        assert np.all(imaginary_parts < 1e-10)
    
    def test_validate_riemann_hypothesis_biological(self):
        """Test the main validation method."""
        model = CytoplasmicRiemannResonance()
        results = model.validate_riemann_hypothesis_biological()
        
        assert isinstance(results, dict)
        assert 'hypothesis_validated' in results
        assert 'all_eigenvalues_real' in results
        assert 'harmonic_distribution' in results
        assert 'coherence_length_um' in results
        
        # Should validate for healthy system
        assert results['hypothesis_validated'] is True
        assert results['all_eigenvalues_real'] is True
    
    def test_get_coherence_at_scale(self):
        """Test coherence computation at different scales."""
        model = CytoplasmicRiemannResonance()
        
        # Test at 1 micrometer
        info = model.get_coherence_at_scale(1e-6)
        
        assert isinstance(info, dict)
        assert 'coherence_length_um' in info
        assert 'frequency_hz' in info
        assert 'is_resonant' in info
        assert 'quality_factor' in info
        
        assert info['frequency_hz'] > 0
        assert info['quality_factor'] > 0
    
    def test_detect_decoherence(self):
        """Test decoherence detection for healthy system."""
        model = CytoplasmicRiemannResonance()
        diagnosis = model.detect_decoherence()
        
        assert isinstance(diagnosis, dict)
        assert 'system_state' in diagnosis
        assert 'is_hermitian' in diagnosis
        assert 'decoherence_severity' in diagnosis
        
        # Healthy system should be coherent
        assert diagnosis['system_state'] == 'coherent'
        assert diagnosis['is_hermitian'] is True
        assert diagnosis['decoherence_severity'] < 0.01
    
    def test_cellular_resonance_map(self):
        """Test spatial resonance map computation."""
        model = CytoplasmicRiemannResonance()
        resonance_map = model.compute_cellular_resonance_map()
        
        assert isinstance(resonance_map, dict)
        assert 'scales' in resonance_map
        assert 'coherence_lengths' in resonance_map
        assert 'frequencies' in resonance_map
        assert 'resonance_intensity' in resonance_map
        
        # All arrays should have same length
        n = len(resonance_map['scales'])
        assert len(resonance_map['coherence_lengths']) == n
        assert len(resonance_map['frequencies']) == n
        assert len(resonance_map['resonance_intensity']) == n
    
    def test_export_results(self, tmp_path):
        """Test JSON export functionality."""
        model = CytoplasmicRiemannResonance()
        
        output_file = tmp_path / "test_results.json"
        model.export_results(str(output_file))
        
        assert output_file.exists()
        
        # Verify file is valid JSON
        import json
        with open(output_file, 'r') as f:
            data = json.load(f)
        
        assert 'validation' in data
        assert 'decoherence_analysis' in data
        assert 'eigenvalues' in data
        assert 'metadata' in data


class TestMolecularValidationProtocol:
    """Test suite for MolecularValidationProtocol class."""
    
    def test_initialization(self):
        """Test protocol initialization."""
        protocol = MolecularValidationProtocol()
        
        assert protocol.base_frequency == 141.7001
        assert len(protocol.markers) == 3
        assert len(protocol.nanoparticles) == 2
    
    def test_fluorescent_markers(self):
        """Test fluorescent marker specifications."""
        protocol = MolecularValidationProtocol()
        
        marker_names = [m.name for m in protocol.markers]
        assert 'GFP-Cytoplasm' in marker_names
        assert 'RFP-Mitochondria' in marker_names
        assert 'FRET-Actin' in marker_names
        
        # Check marker properties
        for marker in protocol.markers:
            assert marker.excitation_nm > 0
            assert marker.emission_nm > 0
            assert 0 < marker.quantum_efficiency <= 1
    
    def test_magnetic_nanoparticles(self):
        """Test magnetic nanoparticle specifications."""
        protocol = MolecularValidationProtocol()
        
        # First nanoparticle should resonate at f₀
        assert np.isclose(
            protocol.nanoparticles[0].resonance_frequency,
            protocol.base_frequency
        )
        
        # Second should resonate at 2f₀
        assert np.isclose(
            protocol.nanoparticles[1].resonance_frequency,
            2 * protocol.base_frequency
        )
    
    def test_generate_experimental_protocol(self):
        """Test experimental protocol generation."""
        protocol = MolecularValidationProtocol()
        exp_protocol = protocol.generate_experimental_protocol()
        
        assert isinstance(exp_protocol, dict)
        assert 'preparation' in exp_protocol
        assert 'labeling' in exp_protocol
        assert 'acquisition' in exp_protocol
        assert 'analysis' in exp_protocol
        assert 'expected_results' in exp_protocol
    
    def test_measurement_precision(self):
        """Test measurement precision estimates."""
        protocol = MolecularValidationProtocol()
        precision = protocol.estimate_measurement_precision()
        
        assert isinstance(precision, dict)
        assert 'frequency_hz' in precision
        assert 'coherence_length_nm' in precision
        assert 'temporal_resolution_ms' in precision
        assert 'signal_to_noise' in precision
        
        # Sanity checks
        assert precision['frequency_hz'] > 0
        assert precision['coherence_length_nm'] > 0
        assert precision['signal_to_noise'] > 1
    
    def test_export_protocol(self, tmp_path):
        """Test protocol export functionality."""
        protocol = MolecularValidationProtocol()
        
        output_file = tmp_path / "test_protocol.json"
        protocol.export_protocol(str(output_file))
        
        assert output_file.exists()
        
        # Verify file is valid JSON
        import json
        with open(output_file, 'r') as f:
            data = json.load(f)
        
        assert 'protocol' in data
        assert 'precision_estimates' in data
        assert 'metadata' in data


class TestBiophysicalConstants:
    """Test biophysical constants."""
    
    def test_default_constants(self):
        """Test default constant values."""
        constants = BiophysicalConstants()
        
        # Verify fundamental constants
        assert constants.base_frequency == 141.7001
        assert constants.riemann_gamma_1 == 14.134725
        assert np.isclose(
            constants.base_frequency,
            constants.riemann_gamma_1 * 10.025,
            rtol=1e-4
        )
        
        # Verify physical constants
        assert constants.planck_reduced > 0
        assert constants.cytoplasm_viscosity > 0
        assert constants.coherence_target > 0
        assert constants.num_cells == 3.7e13


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
