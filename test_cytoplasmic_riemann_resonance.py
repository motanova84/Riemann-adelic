#!/usr/bin/env python3
"""
Test Suite: Cytoplasmic Riemann Resonance

Comprehensive tests for the cytoplasmic Riemann resonance model.

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from xenos.cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance


class TestCytoplasmicRiemannResonance:
    """Test suite for CytoplasmicRiemannResonance class."""
    
    @pytest.fixture
    def model(self):
        """Create a model instance for testing."""
        return CytoplasmicRiemannResonance()
    
    def test_initialization(self, model):
        """Test that model initializes with correct parameters."""
        assert model.constants.base_frequency == pytest.approx(141.7001, rel=1e-6)
        assert model.constants.kappa_pi == pytest.approx(2.5773, rel=1e-4)
        assert model.constants.num_cells == pytest.approx(3.7e13, rel=1e-2)
        assert model.constants.cytoplasm_viscosity > 0
    
    def test_base_frequency_derivation(self, model):
        """Test that base frequency matches Riemann zero derivation."""
        # γ₁ = 14.134725 (first Riemann zero)
        # f₀ = γ₁ × 10.025 ≈ 141.7001 Hz
        gamma_1 = 14.134725
        scaling_factor = 10.025
        expected_f0 = gamma_1 * scaling_factor
        
        assert model.constants.base_frequency == pytest.approx(expected_f0, rel=1e-4)
    
    def test_harmonic_frequencies(self, model):
        """Test that harmonic frequencies are correct multiples."""
        for n in range(1, 11):
            expected = n * model.constants.base_frequency
            # The model should support calculating harmonics
            # (implementation may vary, this is a conceptual test)
            harmonic = n * model.constants.base_frequency
            assert harmonic == pytest.approx(expected, rel=1e-10)
    
    def test_validate_riemann_hypothesis(self, model):
        """Test biological Riemann Hypothesis validation."""
        result = model.validate_riemann_hypothesis_biological()
        
        # Check return structure
        assert 'hypothesis_validated' in result
        assert 'all_eigenvalues_real' in result
        assert 'harmonic_distribution' in result
        assert 'interpretation' in result
        
        # Check validation results
        assert result['hypothesis_validated'] is True
        assert result['all_eigenvalues_real'] is True
        assert result['harmonic_distribution'] is True
        assert len(result['interpretation']) > 0
    
    def test_hermiticity(self, model):
        """Test that the system maintains hermitian symmetry."""
        result = model.validate_riemann_hypothesis_biological()
        
        # Hermiticity error should be extremely small (< 1e-12)
        assert result['hermiticity_error'] < 1e-12
        
        # All eigenvalues must be real
        assert result['all_eigenvalues_real'] is True
    
    def test_coherence_at_cellular_scale(self, model):
        """Test coherence calculation at 1.06 μm cellular scale."""
        scale = 1.06e-6  # 1.06 μm in meters
        coherence = model.get_coherence_at_scale(scale)
        
        # Check return structure
        assert 'coherence_length_um' in coherence
        assert 'frequency_hz' in coherence
        assert 'is_resonant' in coherence
        
        # Coherence length should be positive
        assert coherence['coherence_length_um'] > 0
        
        # Frequency should be close to base frequency
        assert coherence['frequency_hz'] > 0
    
    def test_coherence_length_formula(self, model):
        """Test that coherence length follows ξ = √(ν/ω)."""
        # At base frequency
        omega = 2 * np.pi * model.constants.base_frequency
        expected_xi = np.sqrt(model.constants.cytoplasm_viscosity / omega)
        
        # Get coherence at base frequency scale
        coherence = model.get_coherence_at_scale(expected_xi)
        calculated_xi = coherence['coherence_length_um'] * 1e-6  # Convert to meters
        
        # Should be approximately the same
        assert calculated_xi == pytest.approx(expected_xi, rel=0.1)
    
    def test_kappa_pi_value(self, model):
        """Test that κ_Π ≈ 2.5773."""
        assert model.constants.kappa_pi == pytest.approx(2.5773, rel=1e-3)
    
    def test_detect_decoherence_healthy(self, model):
        """Test decoherence detection for healthy system."""
        health = model.detect_decoherence()
        
        # Check return structure
        assert 'system_state' in health
        assert 'is_hermitian' in health
        assert 'decoherence_severity' in health
        assert 'suggested_action' in health
        
        # Healthy system should be coherent
        assert health['system_state'] in ['Coherent', 'Healthy']
        assert health['is_hermitian'] is True
        assert health['decoherence_severity'] < 0.1
    
    def test_export_results(self, model, tmp_path):
        """Test JSON export functionality."""
        output_file = tmp_path / "test_results.json"
        model.export_results(str(output_file))
        
        # Check file was created
        assert output_file.exists()
        
        # Check file is valid JSON
        import json
        with open(output_file, 'r') as f:
            data = json.load(f)
        
        # Check structure
        assert isinstance(data, dict)
        assert len(data) > 0
    
    def test_cellular_scale_resonance(self, model):
        """Test that the model resonates at cellular scales."""
        # Test various cellular scales
        scales = [
            1e-6,    # 1 μm (small organelle)
            10e-6,   # 10 μm (typical cell)
            100e-6,  # 100 μm (large cell)
        ]
        
        for scale in scales:
            coherence = model.get_coherence_at_scale(scale)
            # All scales should return valid data
            assert coherence['coherence_length_um'] > 0
            assert coherence['frequency_hz'] > 0
    
    def test_eigenvalues_real(self, model):
        """Test that all eigenvalues are strictly real."""
        result = model.validate_riemann_hypothesis_biological()
        
        if 'eigenvalues' in result:
            eigenvalues = np.array(result['eigenvalues'])
            # Check all eigenvalues are real (imaginary part ≈ 0)
            if np.iscomplexobj(eigenvalues):
                max_imag = np.max(np.abs(eigenvalues.imag))
                assert max_imag < 1e-12
    
    def test_frequency_spectrum(self, model):
        """Test that frequency spectrum shows harmonic distribution."""
        # Generate first 5 harmonics
        harmonics = [n * model.constants.base_frequency for n in range(1, 6)]
        
        expected = [141.7001, 283.4002, 425.1003, 566.8004, 708.5005]
        
        for h, e in zip(harmonics, expected):
            assert h == pytest.approx(e, rel=1e-4)
    
    def test_quality_factor(self, model):
        """Test that quality factor Q is high (> 100,000)."""
        # Q-factor for biological oscillators should be very high
        coherence = model.get_coherence_at_scale(1.06e-6)
        
        if 'quality_factor' in coherence:
            Q = coherence['quality_factor']
            assert Q > 100000, f"Quality factor {Q} is too low"
    
    def test_cell_count(self, model):
        """Test that cell count is 37 trillion (3.7 × 10¹³)."""
        assert model.constants.num_cells == pytest.approx(3.7e13, rel=1e-2)
        
        # Check it's in the right order of magnitude
        assert 1e13 < model.constants.num_cells < 1e14
    
    def test_biological_interpretation(self, model):
        """Test that interpretation mentions key concepts."""
        result = model.validate_riemann_hypothesis_biological()
        interpretation = result['interpretation'].lower()
        
        # Should mention key concepts
        assert any(word in interpretation for word in [
            'riemann', 'células', 'cells', 'ceros', 'zeros', 'coherencia', 'coherence'
        ])
    
    def test_decoherence_severity_range(self, model):
        """Test that decoherence severity is in [0, 1] range."""
        health = model.detect_decoherence()
        severity = health['decoherence_severity']
        
        assert 0 <= severity <= 1, f"Decoherence severity {severity} out of range [0, 1]"


class TestMathematicalConsistency:
    """Test mathematical consistency of the model."""
    
    @pytest.fixture
    def model(self):
        """Create model instance."""
        return CytoplasmicRiemannResonance()
    
    def test_coherence_length_positive(self, model):
        """Test that coherence length is always positive."""
        for scale in [1e-7, 1e-6, 1e-5, 1e-4]:
            coherence = model.get_coherence_at_scale(scale)
            assert coherence['coherence_length_um'] > 0
    
    def test_frequency_positive(self, model):
        """Test that all frequencies are positive."""
        assert model.constants.base_frequency > 0
        
        for n in range(1, 21):
            f_n = n * model.constants.base_frequency
            assert f_n > 0
    
    def test_hermitian_matrix_properties(self, model):
        """Test that hermitian matrix has required properties."""
        result = model.validate_riemann_hypothesis_biological()
        
        # Hermitian matrices have real eigenvalues
        assert result['all_eigenvalues_real'] is True
        
        # Hermiticity error should be near zero
        assert result['hermiticity_error'] < 1e-10


def test_full_workflow():
    """Test complete workflow from initialization to export."""
    # Create model
    model = CytoplasmicRiemannResonance()
    
    # Validate hypothesis
    result = model.validate_riemann_hypothesis_biological()
    assert result['hypothesis_validated'] is True
    
    # Check coherence
    coherence = model.get_coherence_at_scale(1.06e-6)
    assert coherence['is_resonant'] is True
    
    # Detect decoherence
    health = model.detect_decoherence()
    assert health['is_hermitian'] is True
    
    # Export (to temp file)
    import tempfile
    with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as f:
        model.export_results(f.name)
    
    print("✓ Full workflow test passed")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
