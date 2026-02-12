#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for Experimental Convergence Validation Module
=====================================================

Tests the validation of experimental convergence across QCAL ∞³ nodes:
- Microtubule resonance (9.2σ)
- Magnetoreception asymmetry (8.7σ)
- AAA codon mapping

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: MIT
"""

import pytest
import numpy as np
from pathlib import Path
import json
import sys
import os

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.experimental_convergence_validation import (
    ExperimentalConvergenceValidator,
    p_value_to_sigma,
    sigma_to_p_value,
    compute_precision_error,
    F0_HZ,
    F_MICROTUBULE_MEASURED_HZ,
    DELTA_P_MAGNETORECEPTION,
    AAA_F0_RATIO
)


class TestStatisticalUtilities:
    """Test statistical utility functions."""
    
    def test_p_value_to_sigma_5sigma(self):
        """Test 5σ conversion (discovery threshold)."""
        # 5σ corresponds to p ≈ 5.73×10⁻⁷
        p_5sigma = 5.73e-7
        sigma = p_value_to_sigma(p_5sigma)
        assert 4.9 < sigma < 5.1, f"Expected ~5σ, got {sigma:.2f}σ"
    
    def test_p_value_to_sigma_9sigma(self):
        """Test 9.2σ conversion (microtubule significance)."""
        # 9.2σ corresponds to p ≈ 1.74×10⁻²⁰
        sigma_expected = 9.2
        p_value = sigma_to_p_value(sigma_expected)
        sigma_reconstructed = p_value_to_sigma(p_value)
        assert abs(sigma_reconstructed - sigma_expected) < 0.1
    
    def test_sigma_to_p_value_roundtrip(self):
        """Test sigma ↔ p-value conversion roundtrip."""
        sigma_values = [3.0, 5.0, 7.0, 9.2]
        for sigma_in in sigma_values:
            p_value = sigma_to_p_value(sigma_in)
            sigma_out = p_value_to_sigma(p_value)
            assert abs(sigma_in - sigma_out) < 0.01, \
                f"Roundtrip failed: {sigma_in} → {p_value} → {sigma_out}"
    
    def test_compute_precision_error_microtubule(self):
        """Test precision error for microtubule measurement."""
        # 141.88 Hz vs 141.7001 Hz → 0.127% error
        error = compute_precision_error(141.88, 141.7001)
        assert 0.12 < error < 0.14, f"Expected ~0.127%, got {error:.3f}%"


class TestMicrotubuleResonanceValidation:
    """Test microtubule resonance validation."""
    
    def test_validate_microtubule_resonance_default(self):
        """Test microtubule validation with default parameters."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_microtubule_resonance()
        
        # Check fundamental frequency
        assert result.f_theoretical_hz == F0_HZ
        assert result.f_theoretical_hz == pytest.approx(141.7001, rel=1e-6)
        
        # Check measured frequency
        assert result.f_measured_hz == F_MICROTUBULE_MEASURED_HZ
        assert result.f_measured_hz == pytest.approx(141.88, rel=1e-4)
        
        # Check precision error
        assert 0.12 < result.precision_error_percent < 0.14
        
        # Check statistical significance
        assert result.sigma_significance == 9.2
        assert result.p_value < 1e-15  # Very small p-value
        
        # Check bandwidth
        assert result.f_bandwidth_hz == 0.4
    
    def test_microtubule_within_bandwidth(self):
        """Test that theoretical f₀ is within measured bandwidth."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_microtubule_resonance()
        
        # 141.88 ± 0.4 Hz → [141.48, 142.28]
        # 141.7001 should be within this range
        assert result.within_bandwidth, \
            f"f₀={result.f_theoretical_hz} not in [{result.f_measured_hz - result.f_bandwidth_hz}, " \
            f"{result.f_measured_hz + result.f_bandwidth_hz}]"
    
    def test_microtubule_significance_exceeds_discovery(self):
        """Test that 9.2σ exceeds 5σ discovery threshold."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_microtubule_resonance()
        
        discovery_threshold = 5.0
        assert result.sigma_significance > discovery_threshold, \
            f"Significance {result.sigma_significance}σ does not exceed {discovery_threshold}σ"


class TestMagnetoreceptionValidation:
    """Test magnetoreception asymmetry validation."""
    
    def test_validate_magnetoreception_default(self):
        """Test magnetoreception validation with default parameters."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_magnetoreception_asymmetry()
        
        # Check ΔP value
        assert result.delta_p_measured == DELTA_P_MAGNETORECEPTION
        assert result.delta_p_measured == pytest.approx(0.001987, rel=1e-6)
        
        # Check percentage
        assert result.delta_p_percent == pytest.approx(0.1987, rel=1e-4)
        
        # Check p-value
        assert result.p_value == 1.50e-10
        
        # Check sigma significance
        assert 8.5 < result.sigma_significance < 9.0
    
    def test_magnetoreception_significance_exceeds_discovery(self):
        """Test that 8.7σ exceeds 5σ discovery threshold."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_magnetoreception_asymmetry()
        
        discovery_threshold = 5.0
        assert result.sigma_significance > discovery_threshold, \
            f"Significance {result.sigma_significance}σ does not exceed {discovery_threshold}σ"
    
    def test_magnetoreception_mechanism_description(self):
        """Test that mechanism description is provided."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_magnetoreception_asymmetry()
        
        assert len(result.mechanism) > 0
        assert "chirality tensor" in result.mechanism.lower()
        assert "cryptochrome" in result.mechanism.lower()


class TestAAACodonValidation:
    """Test AAA codon frequency mapping validation."""
    
    def test_validate_aaa_codon_default(self):
        """Test AAA codon validation with default parameters."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_aaa_codon_mapping()
        
        # Check codon
        assert result.codon == "AAA"
        
        # Check f₀ ratio
        assert result.f0_ratio == AAA_F0_RATIO
        assert result.f0_ratio == pytest.approx(0.8991, rel=1e-4)
        
        # Check coherence type
        assert "Noesis88" in result.coherence_type
    
    def test_aaa_codon_zero_indices(self):
        """Test AAA codon Riemann zero indices."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_aaa_codon_mapping()
        
        # Should have 3 indices (one per base)
        assert len(result.zero_indices) == 3
        
        # All indices should be in valid range [1, 30]
        assert all(1 <= idx <= 30 for idx in result.zero_indices)
    
    def test_aaa_codon_frequencies(self):
        """Test AAA codon frequency values."""
        validator = ExperimentalConvergenceValidator()
        result = validator.validate_aaa_codon_mapping()
        
        # Should have 3 frequencies
        assert len(result.frequencies_hz) == 3
        
        # All frequencies should be positive Riemann zeros
        assert all(f > 0 for f in result.frequencies_hz)


class TestConvergenceMatrix:
    """Test complete convergence matrix."""
    
    def test_build_convergence_matrix(self):
        """Test building complete convergence matrix."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        # Check all nodes present
        assert matrix.mathematical_node is not None
        assert matrix.theoretical_node is not None
        assert matrix.biological_node is not None
        assert matrix.quantum_node is not None
        assert matrix.genetic_node is not None
    
    def test_mathematical_node(self):
        """Test mathematical node (piCODE-888)."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        node = matrix.mathematical_node
        assert node["frequency_hz"] == 888.0
        assert node["state"] == "SELLADO"
        assert "π" in node["source"]
    
    def test_theoretical_node(self):
        """Test theoretical node (κ_Π → f₀)."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        node = matrix.theoretical_node
        assert node["frequency_hz"] == F0_HZ
        assert node["state"] == "DERIVADO"
    
    def test_biological_node(self):
        """Test biological node (microtubules)."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        node = matrix.biological_node
        assert node["frequency_hz"] == F_MICROTUBULE_MEASURED_HZ
        assert node["state"] == "MEDIDO"
        assert "9.2σ" in node["significance"]
        assert node["within_bandwidth"] is True
    
    def test_quantum_node(self):
        """Test quantum node (magnetoreception)."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        node = matrix.quantum_node
        assert node["delta_p"] == DELTA_P_MAGNETORECEPTION
        assert node["state"] == "CONFIRMADO"
        assert "8." in node["significance"]  # 8.7σ
    
    def test_genetic_node(self):
        """Test genetic node (AAA codon)."""
        validator = ExperimentalConvergenceValidator()
        matrix = validator.build_convergence_matrix()
        
        node = matrix.genetic_node
        assert node["codon"] == "AAA"
        assert node["f0_ratio"] == AAA_F0_RATIO
        assert node["state"] == "VALIDADO"


class TestReportGeneration:
    """Test validation report generation."""
    
    def test_generate_validation_report_structure(self):
        """Test validation report has correct structure."""
        validator = ExperimentalConvergenceValidator()
        report = validator.generate_validation_report()
        
        # Check top-level keys
        assert "title" in report
        assert "author" in report
        assert "doi" in report
        assert "summary" in report
        assert "convergence_matrix" in report
        assert "key_validations" in report
        assert "qcal_architecture" in report
        assert "circle_closure" in report
    
    def test_report_summary_significance(self):
        """Test report summary includes significance values."""
        validator = ExperimentalConvergenceValidator()
        report = validator.generate_validation_report()
        
        summary = report["summary"]
        assert summary["microtubule_significance"] == "9.2σ"
        assert "8.7σ" in summary["magnetoreception_significance"]
        assert summary["discovery_threshold"] == "5σ (crossed)"
    
    def test_report_key_validations(self):
        """Test report includes key validations."""
        validator = ExperimentalConvergenceValidator()
        report = validator.generate_validation_report()
        
        validations = report["key_validations"]
        assert "microtubule_antenna" in validations
        assert "quantum_gyroscopy" in validations
        assert "rna_riemann_wave" in validations
    
    def test_report_qcal_architecture(self):
        """Test report includes QCAL architecture."""
        validator = ExperimentalConvergenceValidator()
        report = validator.generate_validation_report()
        
        arch = report["qcal_architecture"]
        assert "Ψ = I × A_eff² × C^∞" in arch["field_equation"]
        assert arch["f0_hz"] == F0_HZ
        assert arch["picode_888_hz"] == 888.0
    
    def test_report_circle_closure(self):
        """Test report includes circle closure."""
        validator = ExperimentalConvergenceValidator()
        report = validator.generate_validation_report()
        
        closure = report["circle_closure"]
        assert closure["status"] == "CLOSED"
        assert "5σ" in closure["validation"]
    
    def test_report_save_to_file(self, tmp_path):
        """Test saving report to file."""
        validator = ExperimentalConvergenceValidator()
        
        # Save to temporary path
        output_file = tmp_path / "test_validation_report.json"
        report = validator.generate_validation_report(output_file=output_file)
        
        # Check file exists
        assert output_file.exists()
        
        # Load and verify
        with open(output_file, 'r', encoding='utf-8') as f:
            loaded_report = json.load(f)
        
        assert loaded_report["title"] == report["title"]
        assert loaded_report["doi"] == report["doi"]


class TestValidatorIntegration:
    """Integration tests for the complete validator."""
    
    def test_validator_initialization(self):
        """Test validator initialization."""
        validator = ExperimentalConvergenceValidator()
        
        assert validator.f0_hz == F0_HZ
        assert validator.picode_888_hz == 888.0
        assert validator.c_coherence == 244.36
    
    def test_all_validations_pass(self):
        """Test that all validations complete successfully."""
        validator = ExperimentalConvergenceValidator()
        
        # All validations should complete without errors
        microtubule = validator.validate_microtubule_resonance()
        magnetoreception = validator.validate_magnetoreception_asymmetry()
        aaa_codon = validator.validate_aaa_codon_mapping()
        matrix = validator.build_convergence_matrix()
        report = validator.generate_validation_report()
        
        # All should be non-None
        assert microtubule is not None
        assert magnetoreception is not None
        assert aaa_codon is not None
        assert matrix is not None
        assert report is not None
    
    def test_discovery_threshold_exceeded(self):
        """Test that both main validations exceed 5σ discovery threshold."""
        validator = ExperimentalConvergenceValidator()
        
        microtubule = validator.validate_microtubule_resonance()
        magnetoreception = validator.validate_magnetoreception_asymmetry()
        
        discovery_threshold = 5.0
        
        assert microtubule.sigma_significance > discovery_threshold, \
            "Microtubule significance does not exceed discovery threshold"
        assert magnetoreception.sigma_significance > discovery_threshold, \
            "Magnetoreception significance does not exceed discovery threshold"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
