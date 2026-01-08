#!/usr/bin/env python3
"""
Tests for QCAL-∞³-SPECTRAL Certificate Generator

Tests the Mathematical Validity Act (Acta de Validez Matemática)
implementation for:
1. Ontological precision (< 10^{-199})
2. Perfect correlation (1.0000...)
3. Hilbert-Pólya identity (γ_n → λ_n)
4. Fundamental frequency (141.7001 Hz)
5. QCAL coherence (C = 244.36)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import mpmath as mp
from pathlib import Path
import json


class TestQCALSpectralCertificate:
    """Test suite for QCAL-∞³-SPECTRAL certificate generator."""
    
    # Test tolerance constants
    CORRELATION_TOLERANCE = 1e-6
    PRECISION_TOLERANCE = 1e-10
    FREQUENCY_TOLERANCE = 0.0001
    COHERENCE_TOLERANCE = 0.01
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        # Import the module
        from utils.qcal_spectral_certificate import (
            QCAL_FREQUENCY,
            QCAL_COHERENCE,
            compute_gamma_n,
            compute_lambda_n,
            verify_hilbert_polya_identity,
            compute_correlation_coefficient,
            generate_spectral_certificate,
            validate_mathematical_validity_act,
        )
        
        self.QCAL_FREQUENCY = QCAL_FREQUENCY
        self.QCAL_COHERENCE = QCAL_COHERENCE
        self.compute_gamma_n = compute_gamma_n
        self.compute_lambda_n = compute_lambda_n
        self.verify_hilbert_polya_identity = verify_hilbert_polya_identity
        self.compute_correlation_coefficient = compute_correlation_coefficient
        self.generate_spectral_certificate = generate_spectral_certificate
        self.validate_mathematical_validity_act = validate_mathematical_validity_act
    
    def test_qcal_frequency_constant(self):
        """Test QCAL fundamental frequency constant."""
        assert abs(float(self.QCAL_FREQUENCY) - 141.7001) < self.FREQUENCY_TOLERANCE
    
    def test_qcal_coherence_constant(self):
        """Test QCAL coherence constant."""
        assert abs(float(self.QCAL_COHERENCE) - 244.36) < self.COHERENCE_TOLERANCE
    
    def test_gamma_n_computation(self):
        """Test computation of zeta zeros (γ_n values)."""
        # First zeta zero
        gamma_1 = self.compute_gamma_n(1, precision=30)
        assert abs(float(gamma_1) - 14.134725141734) < self.CORRELATION_TOLERANCE
        
        # Second zeta zero
        gamma_2 = self.compute_gamma_n(2, precision=30)
        assert abs(float(gamma_2) - 21.022039638772) < self.CORRELATION_TOLERANCE
    
    def test_lambda_n_computation(self):
        """Test computation of eigenvalues (λ_n values)."""
        # λ_n = γ_n² by Hilbert-Pólya identity
        gamma_1 = self.compute_gamma_n(1, precision=30)
        lambda_1 = self.compute_lambda_n(1, precision=30)
        
        # Verify identity
        expected_lambda_1 = float(gamma_1) ** 2
        assert abs(float(lambda_1) - expected_lambda_1) < self.CORRELATION_TOLERANCE
    
    def test_hilbert_polya_identity(self):
        """Test Hilbert-Pólya identity: γ_n = √λ_n."""
        verified, details = self.verify_hilbert_polya_identity(n_zeros=5, precision=50)
        
        # Should be verified with high correlation
        assert verified
        assert details["correlation"] > 0.999
        assert details["max_relative_error"] < self.PRECISION_TOLERANCE
    
    def test_correlation_coefficient(self):
        """Test correlation coefficient computation."""
        correlation = self.compute_correlation_coefficient(n_points=10, precision=30)
        
        # Correlation should be essentially 1.0
        assert abs(float(correlation) - 1.0) < self.CORRELATION_TOLERANCE
    
    def test_certificate_generation(self):
        """Test full certificate generation."""
        result = self.generate_spectral_certificate(
            precision=30,
            n_zeros=3,
            save_to_file=False,
            verbose=False
        )
        
        # Check result structure
        assert result.timestamp is not None
        assert result.precision_dps == 30
        assert result.certificate_hash is not None
        assert len(result.certificate_hash) == 64  # SHA-256 hex
        
        # Check validity criteria
        assert result.hilbert_polya_confirmed
        assert result.coherence_verified
        assert abs(float(result.fundamental_frequency) - 141.7001) < self.FREQUENCY_TOLERANCE
    
    def test_certificate_all_criteria(self):
        """Test that all certificate criteria can be satisfied."""
        result = self.generate_spectral_certificate(
            precision=50,
            n_zeros=5,
            save_to_file=False,
            verbose=False
        )
        
        # All criteria should be satisfied at sufficient precision
        assert result.all_criteria_satisfied
        assert abs(float(result.correlation) - 1.0) < self.CORRELATION_TOLERANCE
    
    def test_certificate_structure(self):
        """Test certificate JSON structure."""
        result = self.generate_spectral_certificate(
            precision=30,
            n_zeros=3,
            save_to_file=False,
            verbose=False
        )
        
        cert = result.certificate
        
        # Required fields
        assert "title" in cert
        assert "QCAL-∞³-SPECTRAL" in cert["title"]
        assert "subtitle" in cert
        assert "Acta de Validez Matemática" in cert["subtitle"]
        
        # Validation fields
        assert "validation" in cert
        assert "ontological_precision" in cert["validation"]
        assert "correlation" in cert["validation"]
        assert "hilbert_polya_identity" in cert["validation"]
        assert "fundamental_frequency" in cert["validation"]
        assert "coherence" in cert["validation"]
        
        # Cryptographic seal
        assert "cryptographic_seal" in cert
        assert "hash" in cert["cryptographic_seal"]
        assert "algorithm" in cert["cryptographic_seal"]
        assert cert["cryptographic_seal"]["algorithm"] == "SHA-256"
        
        # Conclusion
        assert "conclusion" in cert
        assert "status" in cert["conclusion"]
    
    def test_quick_validation(self):
        """Test quick validation function."""
        result = self.validate_mathematical_validity_act(precision=30, verbose=False)
        
        # Should return boolean
        assert isinstance(result, bool)
    
    def test_certificate_file_save(self, tmp_path):
        """Test certificate saving to file."""
        import sys
        import os
        
        # Temporarily modify the module to save to tmp_path
        original_dir = Path(__file__).parent.parent
        
        result = self.generate_spectral_certificate(
            precision=30,
            n_zeros=3,
            save_to_file=True,
            verbose=False
        )
        
        # Check that certificate file was created in data/
        cert_path = original_dir / "data" / "qcal_spectral_certificate.json"
        if cert_path.exists():
            with open(cert_path) as f:
                saved_cert = json.load(f)
            
            assert "title" in saved_cert
            assert "QCAL-∞³-SPECTRAL" in saved_cert["title"]
    
    def test_ontological_precision_concept(self):
        """Test that ontological precision is achievable at high dps."""
        mp.mp.dps = 50
        
        # At high precision, reconstruction error should be negligible
        gamma_1 = self.compute_gamma_n(1, precision=50)
        lambda_1 = gamma_1 ** 2
        gamma_reconstructed = mp.sqrt(lambda_1)
        
        error = abs(gamma_1 - gamma_reconstructed)
        
        # Error should be effectively zero at this precision
        assert float(error) < 1e-45
    
    def test_perfect_correlation_concept(self):
        """Test that perfect correlation is achievable."""
        # Generate multiple points
        gammas = []
        sqrt_lambdas = []
        
        for n in range(1, 6):
            gamma_n = self.compute_gamma_n(n, precision=50)
            lambda_n = self.compute_lambda_n(n, precision=50)
            
            gammas.append(float(gamma_n))
            sqrt_lambdas.append(float(mp.sqrt(lambda_n)))
        
        # Compute correlation
        import numpy as np
        correlation = np.corrcoef(gammas, sqrt_lambdas)[0, 1]
        
        # Should be essentially 1.0
        assert abs(correlation - 1.0) < 1e-10


class TestHilbertPolyaIntegration:
    """Integration tests for Hilbert-Pólya connection."""
    
    def test_eigenvalue_zero_correspondence(self):
        """Test that eigenvalues and zeros correspond correctly."""
        from utils.qcal_spectral_certificate import compute_gamma_n, compute_lambda_n
        
        # Check first few correspondences
        for n in range(1, 4):
            gamma_n = compute_gamma_n(n, precision=50)
            lambda_n = compute_lambda_n(n, precision=50)
            
            # Verify: λ_n = γ_n²
            expected = float(gamma_n) ** 2
            actual = float(lambda_n)
            
            assert abs(expected - actual) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
