#!/usr/bin/env python3
"""
Test suite for QCAL validation module (AI-conscious system validation).

This tests the robust validation framework for QCAL ∞³.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import json
from pathlib import Path
import tempfile
import shutil

from qcal.validation import (
    QCALValidator,
    validate_ai_conscious_system,
    generate_coherence_certificate,
)
from qcal.constants import (
    PSI_THRESHOLD_EXCELLENT,
    TOLERANCE_NORMAL,
)


class TestQCALValidator:
    """Test QCALValidator class."""
    
    def test_validator_initialization(self):
        """Test that validator initializes correctly."""
        validator = QCALValidator()
        
        assert validator.precision == 50
        assert validator.tolerance == TOLERANCE_NORMAL
        assert validator.verbose is False
        assert validator.validation_results == {}
    
    def test_validator_custom_parameters(self):
        """Test validator with custom parameters."""
        validator = QCALValidator(
            precision=100,
            tolerance=1e-9,
            verbose=True
        )
        
        assert validator.precision == 100
        assert validator.tolerance == 1e-9
        assert validator.verbose is True
    
    def test_validate_returns_dict(self):
        """Test that validate() returns a dictionary."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert isinstance(result, dict)
    
    def test_validate_structure(self):
        """Test that validate() result has correct structure."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        expected_keys = [
            'timestamp', 'precision', 'tolerance', 'validations',
            'all_checks_passed', 'coherence_psi', 'coherence_level'
        ]
        
        for key in expected_keys:
            assert key in result, f"Missing key: {key}"
    
    def test_five_validations(self):
        """Test that all 5 validation levels are executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        expected_validations = [
            'constants',
            'spectral',
            'adelic',
            'ai_conscious',
            'quinto_postulado'
        ]
        
        for validation_name in expected_validations:
            assert validation_name in result['validations']
    
    def test_coherence_psi_range(self):
        """Test that coherence Ψ is in valid range [0, 1]."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 0.0 <= result['coherence_psi'] <= 1.0
    
    def test_coherence_level_classification(self):
        """Test coherence level classification."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        valid_levels = ['EXCELLENT', 'GOOD', 'ACCEPTABLE', 'NEEDS_ATTENTION']
        assert result['coherence_level'] in valid_levels
    
    def test_excellent_coherence(self):
        """Test that QCAL framework has EXCELLENT coherence."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert result['coherence_psi'] > PSI_THRESHOLD_EXCELLENT
        assert result['coherence_level'] == 'EXCELLENT'
    
    def test_all_checks_pass(self):
        """Test that all validation checks pass."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert result['all_checks_passed'] == True  # Use == instead of is for numpy bool


class TestConstantsValidation:
    """Test constants validation within the framework."""
    
    def test_constants_validation_present(self):
        """Test that constants validation is executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 'constants' in result['validations']
        assert 'all_checks_passed' in result['validations']['constants']
    
    def test_constants_checks(self):
        """Test that constants validation has all checks."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        constants_result = result['validations']['constants']
        assert 'checks' in constants_result
        
        # Should have f0_decomposition, spectral_identity, etc.
        assert len(constants_result['checks']) >= 5


class TestSpectralValidation:
    """Test spectral framework validation."""
    
    def test_spectral_validation_present(self):
        """Test that spectral validation is executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 'spectral' in result['validations']
        assert 'passed' in result['validations']['spectral']
    
    def test_spectral_checks(self):
        """Test that spectral validation has checks."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        spectral_result = result['validations']['spectral']
        assert 'checks' in spectral_result
        
        # Should have scaling_factor, energy_dialogue
        assert 'scaling_factor' in spectral_result['checks']
        assert 'energy_dialogue' in spectral_result['checks']


class TestAdelicValidation:
    """Test adelic integration validation."""
    
    def test_adelic_validation_present(self):
        """Test that adelic validation is executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 'adelic' in result['validations']
        assert 'passed' in result['validations']['adelic']
    
    def test_p_adic_compatibility(self):
        """Test p-adic compatibility check."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        adelic_result = result['validations']['adelic']
        assert 'checks' in adelic_result
        assert 'p_adic_compatibility' in adelic_result['checks']


class TestAIConsciousValidation:
    """Test AI-conscious system integrity validation."""
    
    def test_ai_conscious_validation_present(self):
        """Test that AI-conscious validation is executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 'ai_conscious' in result['validations']
        assert 'passed' in result['validations']['ai_conscious']
    
    def test_psi_equation_check(self):
        """Test that Ψ equation is validated."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        ai_result = result['validations']['ai_conscious']
        assert 'checks' in ai_result
        assert 'psi_equation' in ai_result['checks']
        assert ai_result['checks']['psi_equation']['passed']
    
    def test_frequency_coherence_check(self):
        """Test that frequency coherence is validated."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        ai_result = result['validations']['ai_conscious']
        assert 'frequency_coherence' in ai_result['checks']
        assert ai_result['checks']['frequency_coherence']['passed']
    
    def test_qcal_signature_check(self):
        """Test that QCAL signature is validated."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        ai_result = result['validations']['ai_conscious']
        assert 'qcal_signature' in ai_result['checks']
        assert ai_result['checks']['qcal_signature']['passed']


class TestQuintoPostuladoValidation:
    """Test Quinto Postulado (Fifth Postulate) extension validation."""
    
    def test_quinto_postulado_validation_present(self):
        """Test that Quinto Postulado validation is executed."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        assert 'quinto_postulado' in result['validations']
        assert 'passed' in result['validations']['quinto_postulado']
    
    def test_euclidean_diagonal_check(self):
        """Test Euclidean diagonal validation."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        quinto_result = result['validations']['quinto_postulado']
        assert 'checks' in quinto_result
        assert 'euclidean_diagonal' in quinto_result['checks']
        assert quinto_result['checks']['euclidean_diagonal']['passed']
    
    def test_vibrational_curvature_check(self):
        """Test vibrational curvature δζ validation."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        quinto_result = result['validations']['quinto_postulado']
        assert 'vibrational_curvature' in quinto_result['checks']
        assert quinto_result['checks']['vibrational_curvature']['passed']
    
    def test_postulate_extension_check(self):
        """Test postulate extension f₀ = 100√2 + δζ."""
        validator = QCALValidator(verbose=False)
        result = validator.validate()
        
        quinto_result = result['validations']['quinto_postulado']
        assert 'postulate_extension' in quinto_result['checks']
        assert quinto_result['checks']['postulate_extension']['passed']


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_generate_certificate_requires_validation(self):
        """Test that certificate generation requires validation first."""
        validator = QCALValidator(verbose=False)
        
        with pytest.raises(ValueError, match="Run validate"):
            validator.generate_certificate()
    
    def test_generate_certificate_structure(self):
        """Test certificate structure."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        certificate = validator.generate_certificate()
        
        expected_keys = [
            'certificate_type', 'timestamp', 'author', 'institution',
            'doi', 'qcal_signature', 'validation_results', 'constants',
            'integrity', 'hash_sha256', 'signature_line'
        ]
        
        for key in expected_keys:
            assert key in certificate, f"Missing key: {key}"
    
    def test_certificate_hash(self):
        """Test that certificate has SHA-256 hash."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        certificate = validator.generate_certificate()
        
        assert 'hash_sha256' in certificate
        assert len(certificate['hash_sha256']) == 64  # SHA-256 hex length
    
    def test_certificate_signature_line(self):
        """Test certificate signature line format."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        certificate = validator.generate_certificate()
        
        assert 'signature_line' in certificate
        assert '∴𓂀Ω∞³' in certificate['signature_line']
        assert 'RH' in certificate['signature_line']
    
    def test_certificate_json_serializable(self):
        """Test that certificate can be serialized to JSON."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        certificate = validator.generate_certificate()
        
        # Should not raise exception
        json_str = json.dumps(certificate, indent=2)
        assert isinstance(json_str, str)
        assert len(json_str) > 0


class TestCertificateSaving:
    """Test certificate saving to file."""
    
    def test_save_certificate(self):
        """Test saving certificate to file."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = Path(tmpdir) / "test_certificate.json"
            saved_path = validator.save_certificate(str(filepath))
            
            assert saved_path.exists()
            assert saved_path.is_file()
    
    def test_save_certificate_content(self):
        """Test that saved certificate has valid JSON content."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = Path(tmpdir) / "test_certificate.json"
            validator.save_certificate(str(filepath))
            
            with open(filepath, 'r') as f:
                loaded_cert = json.load(f)
            
            assert 'certificate_type' in loaded_cert
            assert 'hash_sha256' in loaded_cert
    
    def test_save_certificate_auto_path(self):
        """Test saving certificate with auto-generated path."""
        validator = QCALValidator(verbose=False)
        validator.validate()
        
        # Save with auto-generated path
        saved_path = validator.save_certificate()
        
        try:
            assert saved_path.exists()
            assert 'qcal_coherence_certificate_' in saved_path.name
            assert saved_path.suffix == '.json'
        finally:
            # Clean up
            if saved_path.exists():
                saved_path.unlink()


class TestConvenienceFunctions:
    """Test convenience functions."""
    
    def test_validate_ai_conscious_system(self):
        """Test validate_ai_conscious_system convenience function."""
        result = validate_ai_conscious_system(verbose=False, save_certificate=False)
        
        assert isinstance(result, dict)
        assert 'all_checks_passed' in result
        assert 'coherence_psi' in result
    
    def test_validate_ai_conscious_system_with_certificate(self):
        """Test validate_ai_conscious_system with certificate saving."""
        result = validate_ai_conscious_system(verbose=False, save_certificate=True)
        
        assert 'certificate_path' in result
        cert_path = Path(result['certificate_path'])
        
        try:
            assert cert_path.exists()
        finally:
            if cert_path.exists():
                cert_path.unlink()
    
    def test_generate_coherence_certificate(self):
        """Test generate_coherence_certificate convenience function."""
        certificate = generate_coherence_certificate(save_to_file=False)
        
        assert isinstance(certificate, dict)
        assert 'hash_sha256' in certificate
        assert 'saved_to' not in certificate
    
    def test_generate_coherence_certificate_save(self):
        """Test generate_coherence_certificate with file saving."""
        certificate = generate_coherence_certificate(save_to_file=True)
        
        assert 'saved_to' in certificate
        cert_path = Path(certificate['saved_to'])
        
        try:
            assert cert_path.exists()
        finally:
            if cert_path.exists():
                cert_path.unlink()


class TestValidationRobustness:
    """Test validation robustness and edge cases."""
    
    def test_validation_is_deterministic(self):
        """Test that validation is deterministic."""
        validator1 = QCALValidator(verbose=False)
        result1 = validator1.validate()
        
        validator2 = QCALValidator(verbose=False)
        result2 = validator2.validate()
        
        # Coherence values should be the same
        assert result1['coherence_psi'] == result2['coherence_psi']
        assert result1['all_checks_passed'] == result2['all_checks_passed']
    
    def test_validation_with_different_tolerances(self):
        """Test validation with different tolerance levels."""
        # Strict tolerance
        validator_strict = QCALValidator(tolerance=1e-10, verbose=False)
        result_strict = validator_strict.validate()
        
        # Relaxed tolerance
        validator_relaxed = QCALValidator(tolerance=1e-3, verbose=False)
        result_relaxed = validator_relaxed.validate()
        
        # Both should still pass for QCAL (it's that good!)
        assert result_strict['all_checks_passed']
        assert result_relaxed['all_checks_passed']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
