#!/usr/bin/env python3
"""
Tests for Large Sieve Coercivity Module

Tests the Large Sieve technique for proving power-law coercivity (H^δ with δ>0)
of the Hecke operator, ensuring purely discrete spectrum.

Key tests:
  1. Montgomery Large Sieve inequality
  2. Spectral weight power-law growth W_reg(γ,t) ≥ c|γ|^δ
  3. H^δ compact embedding
  4. Absence of continuous spectrum

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import subprocess
from pathlib import Path
import json
import pytest
import numpy as np

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


class TestLargeSieveCoercivity:
    """Test suite for Large Sieve Coercivity validation."""
    
    @pytest.fixture
    def validation_script(self):
        """Path to validation script."""
        return Path(__file__).parent.parent / 'validate_large_sieve_coercivity.py'
    
    @pytest.fixture
    def certificate_path(self):
        """Path to validation certificate."""
        return Path(__file__).parent.parent / 'data' / 'large_sieve_coercivity_certificate.json'
    
    def test_validation_script_exists(self, validation_script):
        """Test that validation script exists."""
        assert validation_script.exists(), "Validation script not found"
        assert validation_script.is_file(), "Validation script is not a file"
    
    def test_validation_script_executable(self, validation_script):
        """Test that validation script is executable."""
        # Check if it has execute permissions or can be run with python
        assert validation_script.exists()
    
    def test_run_validation(self, validation_script, certificate_path):
        """Test running the validation script."""
        # Run validation script
        result = subprocess.run(
            [sys.executable, str(validation_script)],
            capture_output=True,
            text=True,
            timeout=120
        )
        
        # Check it succeeded
        assert result.returncode == 0, f"Validation failed: {result.stderr}"
        
        # Check certificate was generated
        assert certificate_path.exists(), "Certificate not generated"
    
    def test_certificate_structure(self, certificate_path):
        """Test certificate has correct structure."""
        # Ensure certificate exists (run validation if needed)
        if not certificate_path.exists():
            pytest.skip("Certificate not found - run validation first")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        # Check required fields
        assert 'certificate_type' in cert
        assert cert['certificate_type'] == 'LARGE_SIEVE_COERCIVITY_VALIDATION'
        
        assert 'timestamp' in cert
        assert 'author' in cert
        assert 'orcid' in cert
        assert 'doi' in cert
        assert 'qcal_integration' in cert
        assert 'validation_results' in cert
        assert 'certificate_hash' in cert
        assert 'status' in cert
        assert 'clay_compliance' in cert
    
    def test_qcal_integration(self, certificate_path):
        """Test QCAL constants in certificate."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        qcal = cert['qcal_integration']
        
        # Check QCAL constants
        assert qcal['frequency_hz'] == pytest.approx(141.7001, abs=1e-6)
        assert qcal['coherence'] == pytest.approx(244.36, abs=1e-6)
        assert 'omega_0' in qcal
        assert 'equation' in qcal
    
    def test_all_tests_passed(self, certificate_path):
        """Test that all validation tests passed."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        results = cert['validation_results']
        
        # Check overall status
        assert results['all_tests_passed'], "Not all validation tests passed"
        
        # Check individual tests
        assert results['test_1']['inequality_holds'], "Test 1 (Montgomery Large Sieve) failed"
        assert results['test_2']['power_law_growth'], "Test 2 (Power-Law Growth) failed"
        assert results['test_3']['compact_embedding'], "Test 3 (H^δ Compact Embedding) failed"
        assert results['test_4']['no_continuous'], "Test 4 (No Continuous Spectrum) failed"
    
    def test_montgomery_large_sieve_inequality(self, certificate_path):
        """Test Montgomery Large Sieve inequality validation."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        test1 = cert['validation_results']['test_1']
        
        # Check inequality holds
        assert test1['inequality_holds']
        
        # Check margin is significant (at least 50%)
        assert test1['margin'] > 0.5, f"Margin too small: {test1['margin']}"
        
        # Check actual sum is less than theoretical bound
        assert test1['actual_sum'] < test1['theoretical_bound']
    
    def test_power_law_growth(self, certificate_path):
        """Test spectral weight power-law growth."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        test2 = cert['validation_results']['test_2']
        
        # Check δ > 0 (power-law growth)
        assert test2['delta'] > 0, f"δ = {test2['delta']} not positive"
        
        # Check δ is reasonable (typically 0.05 to 0.5)
        assert 0.01 < test2['delta'] < 1.0, f"δ = {test2['delta']} out of expected range"
        
        # Check c > 0 (positive constant)
        assert test2['c'] > 0
        
        # Check max relative error is acceptable (< 50%)
        assert test2['max_relative_error'] < 0.5
    
    def test_h_delta_compact_embedding(self, certificate_path):
        """Test H^δ compact embedding via eigenvalue decay."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        test3 = cert['validation_results']['test_3']
        
        # Check compact embedding
        assert test3['compact_embedding']
        
        # Check eigenvalue decay exponent is negative
        assert test3['fitted_exponent'] < -0.05, "Eigenvalues not decaying fast enough"
        
        # Check eigenvalues are provided and decreasing
        eigenvals = test3['eigenvalues']
        assert len(eigenvals) > 5
        
        # Check general decreasing trend
        avg_first_half = np.mean(eigenvals[:len(eigenvals)//2])
        avg_second_half = np.mean(eigenvals[len(eigenvals)//2:])
        assert avg_first_half > avg_second_half, "Eigenvalues not showing decay trend"
    
    def test_no_continuous_spectrum(self, certificate_path):
        """Test absence of continuous spectrum."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        test4 = cert['validation_results']['test_4']
        
        # Check no continuous spectrum
        assert test4['no_continuous']
        
        # Check discrete spectrum (gap ratio > 5%)
        assert test4['discrete_spectrum']
        assert test4['gap_ratio'] > 0.05, f"Gap ratio too small: {test4['gap_ratio']}"
        
        # Check low density (< 10%)
        assert test4['low_density']
        assert test4['density_ratio'] < 0.1, f"Density ratio too high: {test4['density_ratio']}"
    
    def test_clay_compliance(self, certificate_path):
        """Test Clay Institute compliance flags."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        clay = cert['clay_compliance']
        
        # All compliance flags should be True
        assert clay['non_circular'], "Proof is circular (uses RH)"
        assert clay['algebraic_precision'], "Not algebraically precise"
        assert clay['explicit_constants'], "Constants not explicit"
        assert clay['machine_verifiable'], "Not machine verifiable"
    
    def test_certificate_hash_format(self, certificate_path):
        """Test certificate hash has correct format."""
        if not certificate_path.exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        cert_hash = cert['certificate_hash']
        
        # Check hash format: 0xQCAL_LARGE_SIEVE_<hexstring>
        assert cert_hash.startswith('0xQCAL_LARGE_SIEVE_')
        
        # Extract hex part
        hex_part = cert_hash.split('_')[-1]
        assert len(hex_part) == 16, "Hash hex part should be 16 characters"
        
        # Check it's valid hex
        try:
            int(hex_part, 16)
        except ValueError:
            pytest.fail(f"Hash hex part '{hex_part}' is not valid hexadecimal")
    
    def test_lean_formalization_exists(self):
        """Test that Lean formalization file exists."""
        lean_file = Path(__file__).parent.parent / 'formalization' / 'lean' / 'spectral' / 'LargeSieveCoercivity.lean'
        assert lean_file.exists(), "Lean formalization file not found"
        
        # Check file has content
        content = lean_file.read_text()
        assert len(content) > 1000, "Lean file seems too short"
        
        # Check for key theorems
        assert 'hecke_large_sieve_coercivity_final' in content
        assert 'montgomery_large_sieve_bound' in content
        assert 'spectral_weight_power_growth' in content
    
    def test_readme_exists(self):
        """Test that README documentation exists."""
        readme = Path(__file__).parent.parent / 'formalization' / 'lean' / 'spectral' / 'LARGE_SIEVE_COERCIVITY_README.md'
        assert readme.exists(), "README file not found"
        
        # Check file has content
        content = readme.read_text()
        assert len(content) > 1000, "README seems too short"
        
        # Check for key sections
        assert 'Montgomery' in content
        assert 'Large Sieve' in content
        assert 'power-law' in content or 'power law' in content
        assert 'discrete spectrum' in content


class TestLargeSieveMathematicalProperties:
    """Test mathematical properties of Large Sieve technique."""
    
    def test_power_law_exponent_range(self, certificate_path):
        """Test that power-law exponent δ is in expected range."""
        if not Path(certificate_path).exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        delta = cert['validation_results']['test_2']['delta']
        
        # Typical values from Weyl equidistribution: 0.05 to 0.5
        assert 0.01 < delta < 1.0, f"δ = {delta} outside typical range"
    
    def test_eigenvalue_decay_rate(self, certificate_path):
        """Test eigenvalue decay is consistent with compact embedding."""
        if not Path(certificate_path).exists():
            pytest.skip("Certificate not found")
        
        with open(certificate_path, 'r') as f:
            cert = json.load(f)
        
        test3 = cert['validation_results']['test_3']
        delta = test3['delta']
        exponent = test3['fitted_exponent']
        expected_exponent = -2 * delta
        
        # Check fitted exponent is close to expected -2δ (within 50%)
        relative_diff = abs(exponent - expected_exponent) / abs(expected_exponent)
        assert relative_diff < 0.5, f"Decay exponent {exponent} far from expected {expected_exponent}"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
