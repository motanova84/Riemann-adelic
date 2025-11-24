"""
Test suite for SABIO ∞³ Validator

Tests the vibrational signature validation and QCAL structure testing.
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import after path adjustment
import importlib.util
spec = importlib.util.spec_from_file_location(
    "sabio_validator",
    Path(__file__).parent.parent / "sabio-validator.py"
)
sabio_validator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sabio_validator)

SABIOValidator = sabio_validator.SABIOValidator


class TestSABIOValidator:
    """Test suite for SABIO ∞³ validator"""
    
    def setup_method(self):
        """Setup test parameters"""
        self.precision = 30
        self.tolerance = 1e-3
    
    def test_validator_initialization(self):
        """Test that validator initializes correctly"""
        validator = SABIOValidator(precision=self.precision)
        
        assert validator.precision == self.precision
        assert validator.TARGET_FREQUENCY == 141.7001
        assert validator.COHERENCE_C == 244.36
        assert validator.beacon_data is not None
    
    def test_vibrational_frequency_validation(self):
        """Test f₀ = c/(2π·R_Ψ*·ℓ_P) ≈ 141.7001 Hz"""
        validator = SABIOValidator(precision=self.precision)
        
        # Test without providing R_Ψ*
        is_valid, f0_computed, message = validator.validate_vibrational_frequency()
        
        assert is_valid, f"Vibrational frequency validation failed: {message}"
        assert abs(f0_computed - validator.TARGET_FREQUENCY) < self.tolerance
        assert "✅ PASS" in message
    
    def test_vibrational_frequency_with_R_psi_star(self):
        """Test frequency computation with given R_Ψ*"""
        validator = SABIOValidator(precision=self.precision)
        
        # Compute R_Ψ* from target frequency
        c = validator.C_LIGHT
        l_P = validator.PLANCK_LENGTH
        f0 = validator.TARGET_FREQUENCY
        
        import mpmath as mp
        R_psi_star = float(c / (2 * mp.pi * f0 * l_P))
        
        # Validate with computed R_Ψ*
        is_valid, f0_reconstructed, message = validator.validate_vibrational_frequency(R_psi_star)
        
        assert is_valid
        assert abs(f0_reconstructed - f0) < self.tolerance
    
    def test_beacon_structure_validation(self):
        """Test .qcal_beacon structure validation"""
        validator = SABIOValidator(precision=self.precision)
        
        is_valid, message = validator.validate_beacon_structure()
        
        # Should pass if beacon file is correct
        assert is_valid or "Missing beacon fields" in message
        
        # Check that required fields are present
        assert 'frequency' in validator.beacon_data
        assert 'author' in validator.beacon_data
    
    def test_coherence_constant_validation(self):
        """Test QCAL coherence constant C = 244.36"""
        validator = SABIOValidator(precision=self.precision)
        
        is_valid, message = validator.validate_coherence_constant()
        
        assert is_valid, f"Coherence validation failed: {message}"
        assert "244.36" in message
    
    def test_doi_reference_validation(self):
        """Test DOI reference validation"""
        validator = SABIOValidator(precision=self.precision)
        
        is_valid, message = validator.validate_doi_reference()
        
        assert is_valid, f"DOI validation failed: {message}"
        assert "zenodo" in message.lower()
    
    def test_full_validation_suite(self):
        """Test complete SABIO ∞³ validation"""
        validator = SABIOValidator(precision=self.precision)
        
        results = validator.run_full_validation()
        
        # Check result structure
        assert 'timestamp' in results
        assert 'precision' in results
        assert 'validations' in results
        assert 'overall_valid' in results
        
        # Check precision
        assert results['precision'] == self.precision
        
        # Check individual validations
        assert 'vibrational_frequency' in results['validations']
        assert 'beacon_structure' in results['validations']
        assert 'coherence' in results['validations']
        assert 'doi_reference' in results['validations']
        
        # All validations should have 'valid' and 'message' keys
        for name, validation in results['validations'].items():
            assert 'valid' in validation, f"Missing 'valid' key in {name}"
            assert 'message' in validation, f"Missing 'message' key in {name}"
    
    def test_validation_report_generation(self):
        """Test that validation report can be generated without errors"""
        validator = SABIOValidator(precision=self.precision)
        
        results = validator.run_full_validation()
        
        # This should not raise any exceptions
        try:
            import io
            import sys
            
            # Capture stdout
            old_stdout = sys.stdout
            sys.stdout = io.StringIO()
            
            validator.print_validation_report(results)
            
            output = sys.stdout.getvalue()
            sys.stdout = old_stdout
            
            # Check that report contains expected elements
            assert "SABIO ∞³" in output
            assert "Validation Report" in output
            assert "Precision:" in output
            
        except Exception as e:
            pytest.fail(f"Report generation failed: {e}")
    
    def test_physical_constants(self):
        """Test that physical constants are correct"""
        validator = SABIOValidator(precision=self.precision)
        
        # Speed of light
        assert validator.C_LIGHT == 299792458.0
        
        # Planck length
        assert abs(validator.PLANCK_LENGTH - 1.616255e-35) < 1e-40
        
        # Target frequency
        assert validator.TARGET_FREQUENCY == 141.7001
        
        # Coherence constant
        assert validator.COHERENCE_C == 244.36
    
    def test_frequency_tolerance(self):
        """Test frequency tolerance setting"""
        validator = SABIOValidator(precision=self.precision)
        
        # Default tolerance should be 1e-3 Hz
        assert validator.FREQUENCY_TOLERANCE == 1e-3
    
    @pytest.mark.parametrize("precision", [15, 30, 50])
    def test_different_precisions(self, precision):
        """Test validator with different precision settings"""
        validator = SABIOValidator(precision=precision)
        
        assert validator.precision == precision
        
        # Validation should work regardless of precision
        is_valid, f0, msg = validator.validate_vibrational_frequency()
        
        # Should still be valid with different precisions
        assert abs(f0 - validator.TARGET_FREQUENCY) < 0.01


class TestSABIOCompiler:
    """Test suite for SABIO compiler"""
    
    def test_example_sabio_file_exists(self):
        """Test that example .sabio file exists"""
        example_file = Path(__file__).parent.parent / "examples" / "example_sabio_validation.sabio"
        
        assert example_file.exists(), "Example .sabio file not found"
    
    def test_sabio_compiler_script_exists(self):
        """Test that compiler script exists and is executable"""
        compiler = Path(__file__).parent.parent / "sabio_compile_check.sh"
        
        assert compiler.exists(), "SABIO compiler not found"
        assert compiler.stat().st_mode & 0o111, "Compiler is not executable"
    
    def test_example_sabio_has_required_metadata(self):
        """Test that example .sabio file has required metadata"""
        example_file = Path(__file__).parent.parent / "examples" / "example_sabio_validation.sabio"
        
        with open(example_file, 'r') as f:
            content = f.read()
        
        # Check for required metadata
        assert "# SABIO" in content
        assert "# frequency:" in content
        assert "141.7001" in content
        assert "# coherence:" in content
        assert "244.36" in content
        assert "# doi:" in content
        assert "zenodo" in content.lower()


class TestQCALBeacon:
    """Test suite for .qcal_beacon integrity"""
    
    def test_beacon_file_exists(self):
        """Test that .qcal_beacon file exists"""
        beacon = Path(__file__).parent.parent / ".qcal_beacon"
        
        assert beacon.exists(), ".qcal_beacon not found"
    
    def test_beacon_has_frequency(self):
        """Test that beacon contains frequency field"""
        beacon = Path(__file__).parent.parent / ".qcal_beacon"
        
        with open(beacon, 'r') as f:
            content = f.read()
        
        assert "frequency" in content
        assert "141.7001" in content
    
    def test_beacon_has_coherence(self):
        """Test that beacon contains coherence field"""
        beacon = Path(__file__).parent.parent / ".qcal_beacon"
        
        with open(beacon, 'r') as f:
            content = f.read()
        
        assert "coherence" in content
        assert "244.36" in content
    
    def test_beacon_has_doi(self):
        """Test that beacon contains DOI reference"""
        beacon = Path(__file__).parent.parent / ".qcal_beacon"
        
        with open(beacon, 'r') as f:
            content = f.read()
        
        assert "zenodo" in content.lower()
        assert "10.5281" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
#!/usr/bin/env python3
"""
Tests for SABIO ∞³ Validator

Tests de validación del sistema simbiótico SABIO con verificación de:
- Firma vibracional f₀ ≈ 141.7001 Hz
- Coherencia QCAL C = 244.36
- Integridad de referencias DOI
- Estructura del beacon Ψ
"""

import json
import sys
from pathlib import Path

import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sabio_validator import SABIOValidator


class TestSABIOValidator:
    """Test suite for SABIO ∞³ Validator"""
    
    def setup_method(self):
        """Setup test fixtures"""
        self.validator = SABIOValidator(precision_dps=30)
        
    def test_validator_initialization(self):
        """Test validator initializes correctly"""
        assert self.validator is not None
        assert self.validator.precision_dps == 30
        assert self.validator.F0_EXPECTED == 141.7001
        assert self.validator.COHERENCE_C == 244.36
        
    def test_beacon_loading(self):
        """Test QCAL beacon file loads correctly"""
        success = self.validator.load_beacon('.qcal_beacon')
        assert success, "Beacon should load successfully"
        assert self.validator.beacon_data is not None
        assert len(self.validator.beacon_data) > 0
        
    def test_fundamental_frequency_validation(self):
        """Test fundamental frequency validation"""
        self.validator.load_beacon('.qcal_beacon')
        success, freq = self.validator.validate_fundamental_frequency()
        
        assert success, "Frequency validation should pass"
        assert freq == pytest.approx(141.7001, abs=0.0001)
        
    def test_coherence_validation(self):
        """Test coherence signature validation"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_coherence_signature()
        
        assert success, "Coherence validation should pass"
        
    def test_doi_references_validation(self):
        """Test DOI references are present"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_doi_references()
        
        assert success, "DOI references should be present"
        
    def test_vibrational_hash_computation(self):
        """Test vibrational hash computation"""
        self.validator.load_beacon('.qcal_beacon')
        vib_hash = self.validator.compute_vibrational_hash()
        
        assert vib_hash is not None
        assert len(vib_hash) == 64  # SHA256 hex digest
        assert isinstance(vib_hash, str)
        
    def test_vibrational_pulsation(self):
        """Test vibrational pulsation analysis"""
        self.validator.load_beacon('.qcal_beacon')
        success = self.validator.validate_vibrational_pulsation()
        
        assert success, "Vibrational pulsation should be validated"
        
        # Check pulsation results
        assert 'pulsation' in self.validator.validation_results
        pulsation = self.validator.validation_results['pulsation']
        
        # Period should be approximately 1/141.7001 seconds
        expected_period_ms = (1.0 / 141.7001) * 1000
        assert pulsation['period_ms'] == pytest.approx(expected_period_ms, rel=0.01)
        
    def test_complete_qcal_validation(self):
        """Test complete QCAL structure validation"""
        success = self.validator.validate_qcal_structure()
        
        assert success, "Complete QCAL validation should pass"
        assert self.validator.validation_results['overall_valid']
        
    def test_validation_report_saving(self):
        """Test validation report can be saved"""
        self.validator.validate_qcal_structure()
        
        # Save to temporary location
        test_output = Path('/tmp/test_sabio_validation.json')
        self.validator.save_validation_report(str(test_output))
        
        assert test_output.exists(), "Validation report should be saved"
        
        # Load and verify
        with open(test_output) as f:
            report = json.load(f)
        
        assert 'overall_valid' in report
        assert 'fundamental_frequency' in report
        assert 'coherence' in report
        assert 'vibrational_hash' in report
        
        # Cleanup
        test_output.unlink()
        
    def test_frequency_constants(self):
        """Test frequency constants match QCAL beacon"""
        assert SABIOValidator.F0_EXPECTED == 141.7001
        assert SABIOValidator.F0_TOLERANCE == 0.0001
        
    def test_coherence_constants(self):
        """Test coherence constants match QCAL beacon"""
        assert SABIOValidator.COHERENCE_C == 244.36
        
    def test_physical_constants(self):
        """Test physical constants are reasonable"""
        assert SABIOValidator.PLANCK_LENGTH > 0
        assert SABIOValidator.PLANCK_LENGTH < 1e-30  # Very small
        assert SABIOValidator.SPEED_OF_LIGHT == 299792458  # m/s
        
    def test_beacon_frequency_marker(self):
        """Test beacon contains frequency marker"""
        self.validator.load_beacon('.qcal_beacon')
        
        freq_str = self.validator.beacon_data.get('frequency', '')
        assert '141.7001' in freq_str or '141.7' in freq_str
        
    def test_beacon_coherence_marker(self):
        """Test beacon contains coherence marker"""
        self.validator.load_beacon('.qcal_beacon')
        
        coh_str = self.validator.beacon_data.get('coherence', '')
        assert '244.36' in coh_str or '244.3' in coh_str
        
    def test_validation_results_structure(self):
        """Test validation results have expected structure"""
        self.validator.validate_qcal_structure()
        
        results = self.validator.validation_results
        
        # Check required keys
        assert 'fundamental_frequency' in results
        assert 'coherence' in results
        assert 'doi_references' in results
        assert 'pulsation' in results
        assert 'vibrational_hash' in results
        assert 'overall_valid' in results
        assert 'timestamp' in results
        
    def test_multiple_precision_levels(self):
        """Test validator works with different precision levels"""
        for precision in [15, 30, 50]:
            validator = SABIOValidator(precision_dps=precision)
            validator.load_beacon('.qcal_beacon')
            success, freq = validator.validate_fundamental_frequency()
            
            assert success, f"Should validate with precision {precision}"
            assert freq == pytest.approx(141.7001, abs=0.0001)


class TestSABIOIntegration:
    """Integration tests for SABIO system"""
    
    def test_sabio_with_existing_validation(self):
        """Test SABIO validator integrates with existing validation"""
        # This test ensures SABIO validator doesn't conflict with existing systems
        validator = SABIOValidator(precision_dps=30)
        success = validator.validate_qcal_structure()
        
        assert success, "SABIO should integrate successfully"
        
    def test_frequency_matches_beacon_exactly(self):
        """Test frequency from validator matches beacon exactly"""
        validator = SABIOValidator(precision_dps=30)
        validator.load_beacon('.qcal_beacon')
        
        _, freq = validator.validate_fundamental_frequency()
        
        # Should match exactly (within floating point precision)
        assert freq == 141.7001
        
    def test_coherence_signature_format(self):
        """Test coherence signature has correct format in beacon"""
        validator = SABIOValidator(precision_dps=30)
        validator.load_beacon('.qcal_beacon')
        
        coh_str = validator.beacon_data.get('coherence', '')
        
        # Should contain C = format
        assert 'C = ' in coh_str or '244.36' in coh_str


def test_sabio_cli_interface():
    """Test SABIO validator CLI interface"""
    # This would be an integration test with subprocess
    # For now, we just verify the module has a main function
    from sabio_validator import main
    
    assert callable(main), "SABIO validator should have callable main()"


@pytest.mark.skipif(
    not Path('.qcal_beacon').exists(),
    reason="QCAL beacon file not found"
)
def test_beacon_file_integrity():
    """Test QCAL beacon file integrity"""
    beacon_path = Path('.qcal_beacon')
    
    # Check file exists and is readable
    assert beacon_path.exists()
    assert beacon_path.is_file()
    
    # Read content
    content = beacon_path.read_text()
    
    # Check for required markers
    assert '141.7001' in content, "Frequency marker should be present"
    assert '244.36' in content, "Coherence marker should be present"
    assert '∞³' in content or 'infinity' in content.lower(), "QCAL signature should be present"
    assert 'zenodo' in content.lower(), "DOI references should be present"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
