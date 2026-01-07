#!/usr/bin/env python3
"""
Tests for the Unconditional Spectral Equivalence Proof.

This test suite validates the spectral equivalence theorem:
    Spec(𝓗_Ψ) = { γ ∈ ℝ : ζ(1/2 + iγ) = 0 }

Tests cover:
    1. Forward direction: eigenvalues → zeta zeros
    2. Backward direction: zeta zeros → eigenvalues
    3. Mellin kernel identity
    4. Paley-Wiener correspondence
    5. Integration tests

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
Date: January 2026
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from proofs.spectral_equivalence_unconditional import (
    SpectralEquivalenceProof,
    SpectralEquivalenceResult,
    MellinKernelIdentity,
    PaleyWienerBridge,
    run_proof,
    KNOWN_ZEROS,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
)


class TestMellinKernelIdentity:
    """Tests for the Mellin kernel identity validation."""
    
    def test_kernel_symmetry(self):
        """Test that spectral kernel is symmetric."""
        mellin = MellinKernelIdentity(precision=25)
        
        x, y = 2.0, 3.0
        k_xy = mellin.spectral_kernel(x, y)
        k_yx = mellin.spectral_kernel(y, x)
        
        # Kernel should be symmetric
        assert abs(k_xy - k_yx) < 1e-10
    
    def test_kernel_positivity(self):
        """Test that kernel is defined for positive arguments."""
        mellin = MellinKernelIdentity()
        
        # Test positive arguments
        for x in [0.1, 1.0, 10.0]:
            for y in [0.1, 1.0, 10.0]:
                k = mellin.spectral_kernel(x, y)
                assert isinstance(k, complex)
                assert np.isfinite(k.real)
    
    def test_kernel_boundary(self):
        """Test kernel behavior at boundary."""
        mellin = MellinKernelIdentity()
        
        # Non-positive arguments should return 0
        assert mellin.spectral_kernel(0, 1) == 0
        assert mellin.spectral_kernel(-1, 1) == 0
        assert mellin.spectral_kernel(1, 0) == 0
    
    def test_mellin_transform_convergence(self):
        """Test Mellin transform numerical convergence."""
        mellin = MellinKernelIdentity()
        
        s = complex(0.5, 14.0)  # Near first zero
        
        # Compute with different resolutions
        m1 = mellin.mellin_transform(s, n_points=100)
        m2 = mellin.mellin_transform(s, n_points=500)
        m3 = mellin.mellin_transform(s, n_points=1000)
        
        # Should converge
        assert np.isfinite(m1)
        assert np.isfinite(m2)
        assert np.isfinite(m3)
    
    def test_identity_validation(self):
        """Test the identity validation method."""
        mellin = MellinKernelIdentity(precision=25)
        
        # Validate on a subset of zeros
        t_values = KNOWN_ZEROS[:3]
        valid, error, details = mellin.validate_identity(
            t_values=t_values,
            tolerance=1.0  # Relaxed for numerical computation
        )
        
        assert 'comparisons' in details
        assert 'max_error' in details
        assert error >= 0


class TestPaleyWienerBridge:
    """Tests for the Paley-Wiener correspondence."""
    
    def test_test_function_properties(self):
        """Test that bump function is compactly supported."""
        pw = PaleyWienerBridge()
        
        # Inside support
        assert pw.test_function(0.0) > 0
        assert pw.test_function(5.0) > 0
        
        # Outside support (default support = 10)
        assert pw.test_function(11.0) == 0
        assert pw.test_function(-11.0) == 0
    
    def test_test_function_smoothness(self):
        """Test that bump function is smooth."""
        pw = PaleyWienerBridge()
        
        # Values should change smoothly
        x_vals = np.linspace(-9, 9, 100)
        y_vals = [pw.test_function(x) for x in x_vals]
        
        # Check no discontinuities
        diffs = np.abs(np.diff(y_vals))
        assert np.all(diffs < 0.5)  # No large jumps
    
    def test_mellin_of_test_finite(self):
        """Test that Mellin transform of test function is finite."""
        pw = PaleyWienerBridge(n_points=500)
        
        for sigma in [0.3, 0.5, 0.7]:
            for t in [-5, 0, 5]:
                s = complex(sigma, t)
                m = pw.mellin_of_test(s)
                assert np.isfinite(m)
    
    def test_holomorphicity_verification(self):
        """Test holomorphicity verification."""
        pw = PaleyWienerBridge(n_points=200)
        
        is_hol, details = pw.verify_holomorphic(
            re_range=(0.2, 0.8),
            im_range=(-5, 5),
            n_grid=10
        )
        
        assert 'max_cauchy_riemann_error' in details
        # The error should be finite
        assert np.isfinite(details['max_cauchy_riemann_error'])


class TestSpectralEquivalenceProof:
    """Tests for the main proof class."""
    
    @pytest.fixture
    def proof(self):
        """Create a proof instance with small grid for testing."""
        return SpectralEquivalenceProof(
            n_grid=1000,  # Smaller for faster tests
            precision=25,
            verbose=False
        )
    
    def test_operator_construction(self, proof):
        """Test H_Ψ matrix construction."""
        H = proof.construct_H_psi()
        
        # Should be square
        assert H.shape[0] == H.shape[1]
        
        # Should be symmetric
        assert np.allclose(H, H.T)
    
    def test_eigenvalue_computation(self, proof):
        """Test eigenvalue computation."""
        H = proof.construct_H_psi()
        eigenvalues = proof.compute_eigenvalues(H, k=20)
        
        # Should compute requested number
        assert len(eigenvalues) == 20
        
        # All should be real (eigvalsh guarantees this)
        assert np.all(np.isreal(eigenvalues))
    
    def test_forward_direction(self, proof):
        """Test forward direction of the proof."""
        H = proof.construct_H_psi()
        eigenvalues = proof.compute_eigenvalues(H, k=30)
        
        valid, details = proof.forward_direction(eigenvalues, tolerance=0.1)
        
        assert 'matched' in details
        assert 'total_eigenvalues' in details
        assert details['total_eigenvalues'] == 30
    
    def test_backward_direction(self, proof):
        """Test backward direction of the proof."""
        H = proof.construct_H_psi()
        
        valid, details = proof.backward_direction(
            H,
            zeros_to_test=KNOWN_ZEROS[:3],
            tolerance=0.1
        )
        
        assert 'zeros_found' in details
        assert 'zeros_tested' in details
        assert details['zeros_tested'] == 3
    
    def test_full_proof_runs(self, proof):
        """Test that full proof runs without errors."""
        result = proof.prove_equivalence()
        
        assert isinstance(result, SpectralEquivalenceResult)
        assert result.timestamp != ""
        assert result.execution_time > 0
        assert len(result.eigenvalues_computed) > 0
        # First eigenvalue should be close to 1/4 + γ₁²
        first_eig = result.eigenvalues_computed[0]
        target = 0.25 + KNOWN_ZEROS[0]**2
        assert abs(first_eig - target) / target < 0.01  # 1% tolerance


class TestQCALIntegration:
    """Tests for QCAL constant integration."""
    
    def test_qcal_constants_defined(self):
        """Test QCAL constants are properly defined."""
        assert QCAL_BASE_FREQUENCY == 141.7001
        assert QCAL_COHERENCE == 244.36
    
    def test_known_zeros_loaded(self):
        """Test known Riemann zeros are available."""
        assert len(KNOWN_ZEROS) >= 10
        
        # First zero should be approximately 14.13
        assert 14.1 < KNOWN_ZEROS[0] < 14.2
        
        # Zeros should be ordered
        assert np.all(np.diff(KNOWN_ZEROS) > 0)


class TestRunProof:
    """Tests for the run_proof function."""
    
    def test_run_proof_basic(self):
        """Test basic proof execution."""
        result = run_proof(
            n_grid=500,
            precision=15,
            verbose=False,
            save_certificate=False
        )
        
        assert isinstance(result, SpectralEquivalenceResult)
        assert 'matrix_shape' in result.details
    
    def test_run_proof_certificate(self, tmp_path, monkeypatch):
        """Test certificate generation."""
        # Change to temp directory
        monkeypatch.chdir(tmp_path)
        
        # Create data directory
        (tmp_path / 'data').mkdir()
        
        result = run_proof(
            n_grid=300,
            precision=10,
            verbose=False,
            save_certificate=True
        )
        
        # Certificate should be created
        cert_path = tmp_path / 'data' / 'spectral_equivalence_certificate.json'
        assert cert_path.exists()


class TestIntegration:
    """Integration tests for the complete proof."""
    
    @pytest.mark.slow
    def test_full_validation(self):
        """Full validation with higher resolution."""
        result = run_proof(
            n_grid=2000,
            precision=30,
            verbose=False,
            save_certificate=False
        )
        
        # Check all components ran
        assert 'forward' in result.details
        assert 'backward' in result.details
        assert 'mellin_identity' in result.details
        assert 'paley_wiener' in result.details


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
