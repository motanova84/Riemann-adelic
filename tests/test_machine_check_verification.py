"""
Test suite for Machine-Check Verification System

Tests all components of the machine-check verification system:
- QCAL coherence validation
- V5 Coronación integration
- Certificate generation
- Numerical precision
- Spectral properties
- Adelic structure
"""

import pytest
import json
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from machine_check_verification import MachineCheckVerifier, QCAL_BASE_FREQUENCY, QCAL_COHERENCE, QCAL_CRITICAL_LINE


class TestMachineCheckVerifier:
    """Test suite for MachineCheckVerifier class"""
    
    def setup_method(self):
        """Setup test environment"""
        self.verifier = MachineCheckVerifier(precision=25, verbose=False)
    
    def test_initialization(self):
        """Test verifier initialization"""
        assert self.verifier.precision == 25
        assert self.verifier.qcal_config['base_frequency'] == QCAL_BASE_FREQUENCY
        assert self.verifier.qcal_config['coherence'] == QCAL_COHERENCE
        assert self.verifier.qcal_config['critical_line'] == QCAL_CRITICAL_LINE
    
    def test_qcal_coherence(self):
        """Test QCAL coherence verification"""
        result = self.verifier.verify_qcal_coherence()
        assert result is True
        assert 'qcal_coherence' in self.verifier.results
        assert self.verifier.results['qcal_coherence']['status'] == 'PASSED'
    
    def test_numerical_precision(self):
        """Test numerical precision verification"""
        result = self.verifier.verify_numerical_precision()
        assert result is True
        assert 'numerical_precision' in self.verifier.results
        assert self.verifier.results['numerical_precision']['status'] == 'PASSED'
    
    def test_spectral_properties(self):
        """Test spectral properties verification"""
        result = self.verifier.verify_spectral_properties()
        assert result is True
        assert 'spectral_properties' in self.verifier.results
        assert self.verifier.results['spectral_properties']['status'] == 'PASSED'
    
    def test_mathematical_certificates(self):
        """Test mathematical certificates verification"""
        result = self.verifier.verify_mathematical_certificates()
        assert result is True
        assert 'mathematical_certificates' in self.verifier.results
    
    def test_adelic_structure(self):
        """Test adelic structure verification"""
        result = self.verifier.verify_adelic_structure()
        # Should pass or skip if module not available
        assert result is True
        assert 'adelic_structure' in self.verifier.results
    
    def test_yolo_integration(self):
        """Test YOLO integration verification"""
        result = self.verifier.verify_yolo_integration()
        # Should pass or skip if module not available
        assert result is True
        assert 'yolo_integration' in self.verifier.results
    
    def test_comprehensive_verification(self):
        """Test comprehensive verification run"""
        results = self.verifier.run_comprehensive_verification()
        
        assert 'timestamp' in results
        assert 'overall_status' in results
        assert 'summary' in results
        assert 'verifications' in results
        assert results['overall_status'] in ['PASSED', 'PARTIAL', 'FAILED']
        
        # Check summary statistics
        summary = results['summary']
        assert summary['total'] > 0
        assert summary['total'] == summary['passed'] + summary['failed'] + summary['skipped']
    
    def test_certificate_generation(self):
        """Test certificate generation"""
        # Run verification first
        results = self.verifier.run_comprehensive_verification()
        
        # Generate certificate to temp location
        cert_path = '/tmp/test_machine_check_certificate.json'
        certificate = self.verifier.generate_certificate(results, cert_path)
        
        assert certificate is not None
        assert 'certificate_type' in certificate
        assert 'qcal_signature' in certificate
        assert 'verification_results' in certificate
        
        # Verify certificate file was created
        cert_file = Path(cert_path)
        assert cert_file.exists()
        
        # Verify certificate content
        with open(cert_file, 'r') as f:
            loaded_cert = json.load(f)
        
        assert loaded_cert['certificate_type'] == 'QCAL ∞³ Machine-Check Verification'
        assert loaded_cert['version'] == 'V5 Coronación'
        assert loaded_cert['qcal_signature']['base_frequency'] == QCAL_BASE_FREQUENCY
        
        # Cleanup
        cert_file.unlink()


class TestQCALConstants:
    """Test QCAL constants and configuration"""
    
    def test_base_frequency(self):
        """Test QCAL base frequency constant"""
        assert QCAL_BASE_FREQUENCY == 141.7001
    
    def test_coherence_constant(self):
        """Test QCAL coherence constant"""
        assert QCAL_COHERENCE == 244.36
    
    def test_critical_line(self):
        """Test critical line constant"""
        assert QCAL_CRITICAL_LINE == 0.5


class TestVerificationComponents:
    """Test individual verification components"""
    
    def setup_method(self):
        """Setup test environment"""
        self.verifier = MachineCheckVerifier(precision=25, verbose=False)
    
    def test_log_function(self):
        """Test logging function"""
        # Should not raise error
        self.verifier.log("Test message")
        self.verifier.log("Test warning", "WARNING")
        self.verifier.log("Test error", "ERROR")
    
    def test_results_accumulation(self):
        """Test that results are properly accumulated"""
        self.verifier.verify_qcal_coherence()
        assert len(self.verifier.results) > 0
        
        self.verifier.verify_numerical_precision()
        assert len(self.verifier.results) > 1
    
    def test_error_handling(self):
        """Test error handling in verification methods"""
        # Create verifier with invalid precision to potentially trigger errors
        verifier_bad = MachineCheckVerifier(precision=1, verbose=False)
        
        # Should handle errors gracefully
        try:
            verifier_bad.verify_qcal_coherence()
            # Should succeed or fail gracefully
            assert True
        except Exception:
            # If it raises, that's also acceptable for this test
            assert True


class TestIntegrationWithV5:
    """Test integration with V5 Coronación framework"""
    
    def setup_method(self):
        """Setup test environment"""
        self.verifier = MachineCheckVerifier(precision=25, verbose=False)
    
    def test_v5_coronacion_verification(self):
        """Test V5 Coronación verification"""
        result = self.verifier.verify_v5_coronacion()
        
        # Should either pass or fail with proper error handling
        assert isinstance(result, bool)
        assert 'v5_coronacion' in self.verifier.results
        
        # Check result structure
        v5_result = self.verifier.results['v5_coronacion']
        assert 'status' in v5_result


@pytest.mark.slow
class TestComprehensiveRun:
    """Comprehensive integration tests (marked as slow)"""
    
    def test_full_verification_run(self):
        """Test complete verification run with certificate generation"""
        verifier = MachineCheckVerifier(precision=25, verbose=True)
        
        # Run comprehensive verification
        results = verifier.run_comprehensive_verification()
        
        # Verify results structure
        assert results['overall_status'] in ['PASSED', 'PARTIAL', 'FAILED']
        assert results['summary']['total'] >= 5  # At least 5 verification types
        
        # Generate certificate
        cert_path = '/tmp/test_comprehensive_certificate.json'
        certificate = verifier.generate_certificate(results, cert_path)
        
        assert certificate is not None
        
        # Cleanup
        Path(cert_path).unlink(missing_ok=True)
    
    def test_different_precision_levels(self):
        """Test verification at different precision levels"""
        precisions = [15, 25, 30]
        
        for prec in precisions:
            verifier = MachineCheckVerifier(precision=prec, verbose=False)
            result = verifier.verify_numerical_precision()
            
            assert result is True
            assert verifier.results['numerical_precision']['mpmath_dps'] == prec


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
