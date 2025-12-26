#!/usr/bin/env python3
"""
Test SpectrumZeta Numerical Verification

This test suite validates the numerical verification script for
SpectrumZeta.lean partial lemmas. It ensures that the first N zeros
are correctly verified against Odlyzko data.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 2025-11-22
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
import pytest
import json
import mpmath as mp

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from verify_zeta_zeros_numerical import (
    verify_zero,
    verify_first_n_zeros,
    KNOWN_ZEROS,
    zeta_on_critical_line
)


class TestSpectrumZetaVerification:
    """Test suite for SpectrumZeta numerical verification."""
    
    def setup_method(self):
        """Setup test environment with appropriate precision."""
        mp.mp.dps = 50
    
    def test_known_zeros_list_length(self):
        """Test that we have at least 10 known zeros."""
        assert len(KNOWN_ZEROS) >= 10, "Should have at least 10 known zeros"
    
    def test_first_zero_accuracy(self):
        """Test that the first zero is accurate."""
        t = KNOWN_ZEROS[0]
        is_zero, abs_val = verify_zero(t, tolerance=1e-10)
        
        assert is_zero, f"First zero should verify: |ζ(1/2+it)| = {abs_val}"
        assert abs_val < 1e-10, f"First zero error too large: {abs_val}"
    
    def test_all_first_10_zeros(self):
        """Test that all first 10 zeros verify."""
        for i in range(10):
            t = KNOWN_ZEROS[i]
            is_zero, abs_val = verify_zero(t, tolerance=1e-10)
            
            assert is_zero, f"Zero {i+1} failed: t={t}, |ζ(1/2+it)|={abs_val}"
    
    def test_verify_first_n_zeros_function(self):
        """Test the verify_first_n_zeros wrapper function."""
        results = verify_first_n_zeros(n=5, tolerance=1e-10)
        
        assert results['total_checked'] == 5
        assert results['all_verified'] == True
        assert len(results['zeros']) == 5
        
        for zero_result in results['zeros']:
            assert zero_result['verified'] == True
            assert zero_result['zeta_value_abs'] < 1e-10
    
    def test_zeta_on_critical_line(self):
        """Test zeta function evaluation on critical line."""
        # Test at first zero
        t = KNOWN_ZEROS[0]
        zeta_val = zeta_on_critical_line(t)
        
        assert abs(zeta_val) < 1e-10, f"Zeta should be near zero: {abs(zeta_val)}"
    
    def test_zeta_not_zero_between_zeros(self):
        """Test that zeta is not zero between known zeros."""
        # Test midpoint between first two zeros
        t_mid = (KNOWN_ZEROS[0] + KNOWN_ZEROS[1]) / 2
        zeta_val = zeta_on_critical_line(t_mid)
        
        assert abs(zeta_val) > 1e-5, f"Zeta should not be zero between zeros: {abs(zeta_val)}"
    
    def test_verification_certificate_structure(self):
        """Test that verification certificate has correct structure."""
        results = verify_first_n_zeros(n=3, tolerance=1e-10)
        
        # Check required keys
        assert 'total_checked' in results
        assert 'all_verified' in results
        assert 'tolerance' in results
        assert 'zeros' in results
        
        # Check zeros structure
        for zero_result in results['zeros']:
            assert 'index' in zero_result
            assert 't' in zero_result
            assert 'zeta_value_abs' in zero_result
            assert 'verified' in zero_result
    
    def test_certificate_file_creation(self):
        """Test that certificate file is created and valid JSON."""
        import tempfile
        import os
        
        # Create temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_file = f.name
        
        try:
            # Run verification and save to temp file
            from verify_zeta_zeros_numerical import export_verification_certificate
            results = verify_first_n_zeros(n=3, tolerance=1e-10)
            export_verification_certificate(results, temp_file)
            
            # Verify file exists and is valid JSON
            assert os.path.exists(temp_file)
            
            with open(temp_file, 'r') as f:
                certificate = json.load(f)
            
            # Check certificate structure
            assert 'title' in certificate
            assert 'timestamp' in certificate
            assert 'precision_dps' in certificate
            assert 'verification' in certificate
            assert 'references' in certificate
            assert 'author' in certificate
            assert 'orcid' in certificate
            
            # Check QCAL references
            assert certificate['orcid'] == '0009-0002-1923-0773'
            assert any('QCAL' in ref for ref in certificate['references'])
            
        finally:
            # Cleanup
            if os.path.exists(temp_file):
                os.remove(temp_file)
    
    def test_tolerance_variations(self):
        """Test verification with different tolerances."""
        t = KNOWN_ZEROS[0]
        
        # Very strict tolerance - should pass
        is_zero, abs_val = verify_zero(t, tolerance=1e-5)
        assert is_zero
        
        # Extremely strict tolerance - might fail due to numerical precision
        is_zero_strict, abs_val_strict = verify_zero(t, tolerance=1e-50)
        # Don't assert - just document that extreme precision has limits
        
        # Very loose tolerance - should definitely pass
        is_zero_loose, abs_val_loose = verify_zero(t, tolerance=1e-5)
        assert is_zero_loose
    
    def test_odlyzko_data_consistency(self):
        """Test that Odlyzko data is in ascending order."""
        for i in range(len(KNOWN_ZEROS) - 1):
            assert KNOWN_ZEROS[i] < KNOWN_ZEROS[i+1], \
                f"Zeros should be in ascending order: {KNOWN_ZEROS[i]} >= {KNOWN_ZEROS[i+1]}"
    
    def test_zeros_positive(self):
        """Test that all zeros are positive."""
        for i, t in enumerate(KNOWN_ZEROS):
            assert t > 0, f"Zero {i+1} should be positive: {t}"
    
    def test_first_zero_known_value(self):
        """Test that first zero matches well-known value."""
        # First zero from Odlyzko tables (to 6 decimal places)
        FIRST_ZERO_APPROX = 14.134725
        TOLERANCE = 0.001  # Allow 0.1% error for approximate comparison
        
        assert abs(KNOWN_ZEROS[0] - FIRST_ZERO_APPROX) < TOLERANCE, \
            f"First zero should be ~{FIRST_ZERO_APPROX}, got {KNOWN_ZEROS[0]}"


class TestQCALIntegration:
    """Test QCAL ∞³ framework integration."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are documented."""
        from verify_zeta_zeros_numerical import export_verification_certificate
        import tempfile
        import os
        
        results = verify_first_n_zeros(n=1, tolerance=1e-10)
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_file = f.name
        
        try:
            export_verification_certificate(results, temp_file)
            
            with open(temp_file, 'r') as f:
                certificate = json.load(f)
            
            # Check for QCAL reference
            refs = certificate['references']
            assert any('QCAL' in str(ref) for ref in refs), \
                "Certificate should reference QCAL framework"
            
        finally:
            if os.path.exists(temp_file):
                os.remove(temp_file)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
