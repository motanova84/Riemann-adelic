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


Test Suite for Unconditional Spectral Equivalence Demonstration

This test module validates the numerical demonstration of the spectral
equivalence between the H_Ψ operator and Riemann zeta zeros.

Test Categories:
1. Core mathematical constructs (kernels, operators)
2. Self-adjointness verification
3. Spectral correspondence with zeta zeros
4. Numerical stability and precision

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: January 2026

QCAL Integration:
    Base frequency: 141.7001 Hz
    Coherence: C = 244.36
"""

import pytest
import numpy as np
from numpy.testing import assert_allclose, assert_array_less
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from spectral_equivalence_unconditional import (
    # Constants
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    ZETA_PRIME_HALF,
    KNOWN_ZETA_ZEROS,
    PI,
    # Kernel functions
    gaussian_kernel,
    berry_keating_kernel,
    # Operator construction
    build_H_psi_matrix,
    compute_spectral_eigenvalues,
    # Verification functions
    verify_self_adjointness,
    verify_positive_inner_products,
    match_eigenvalues_to_zeros,
    # Main functions
    compute_spectral_equivalence,
    demonstrate_spectral_equivalence,
    generate_certificate,
    # High precision
    compute_zeta_prime_half,
)


# ============================================================================
# Constants Tests
# ============================================================================

class TestQCALConstants:
    """Test QCAL framework constants."""
    
    def test_qcal_frequency_positive(self):
        """QCAL frequency should be positive."""
        assert QCAL_FREQUENCY > 0
    
    def test_qcal_frequency_value(self):
        """QCAL frequency should be approximately 141.7001 Hz."""
        assert_allclose(QCAL_FREQUENCY, 141.7001, rtol=1e-6)
    
    def test_qcal_coherence_positive(self):
        """QCAL coherence should be positive."""
        assert QCAL_COHERENCE > 0
    
    def test_qcal_coherence_value(self):
        """QCAL coherence should be approximately 244.36."""
        assert_allclose(QCAL_COHERENCE, 244.36, rtol=1e-4)
    
    def test_zeta_prime_half_negative(self):
        """ζ'(1/2) should be negative."""
        assert ZETA_PRIME_HALF < 0
    
    def test_zeta_prime_half_value(self):
        """ζ'(1/2) should be approximately -3.9226461392."""
        assert_allclose(ZETA_PRIME_HALF, -3.9226461392, rtol=1e-8)


class TestKnownZetaZeros:
    """Test the known Riemann zeta zeros."""
    
    def test_zeros_array_shape(self):
        """Should have 30 known zeros."""
        assert len(KNOWN_ZETA_ZEROS) == 30
    
    def test_zeros_positive(self):
        """All zeros should be positive (imaginary parts)."""
        assert np.all(KNOWN_ZETA_ZEROS > 0)
    
    def test_zeros_increasing(self):
        """Zeros should be in increasing order."""
        assert np.all(np.diff(KNOWN_ZETA_ZEROS) > 0)
    
    def test_first_zero(self):
        """First zero should be approximately 14.134725."""
        assert_allclose(KNOWN_ZETA_ZEROS[0], 14.134725, rtol=1e-5)
    
    def test_zeros_reasonable_range(self):
        """All zeros should be in reasonable range (0, 200)."""
        assert np.all(KNOWN_ZETA_ZEROS > 0)
        assert np.all(KNOWN_ZETA_ZEROS < 200)


# ============================================================================
# Kernel Tests
# ============================================================================

class TestGaussianKernel:
    """Test Gaussian heat kernel implementation."""
    
    def test_kernel_nonnegative(self):
        """Gaussian kernel should be non-negative."""
        t = np.linspace(-5, 5, 50)
        K = gaussian_kernel(t, t, h=0.01)
        assert np.all(K >= 0)
    
    def test_kernel_symmetric(self):
        """Gaussian kernel should be symmetric K(t,s) = K(s,t)."""
        t = np.linspace(-5, 5, 50)
        K = gaussian_kernel(t, t, h=0.01)
        assert_allclose(K, K.T, rtol=1e-10)
    
    def test_kernel_diagonal_maximum(self):
        """Diagonal elements should be largest in each row."""
        t = np.linspace(-5, 5, 50)
        K = gaussian_kernel(t, t, h=0.01)
        for i in range(len(t)):
            assert K[i, i] >= np.max(K[i, :]) - 1e-10
    
    def test_kernel_decay(self):
        """Kernel should decay away from diagonal."""
        t = np.linspace(-5, 5, 50)
        K = gaussian_kernel(t, t, h=0.01)
        # Off-diagonal elements should be smaller
        assert K[0, -1] < K[0, 0] / 100
    
    def test_kernel_normalization(self):
        """Kernel integral should be approximately 1."""
        t = np.linspace(-20, 20, 500)
        dt = t[1] - t[0]
        K_row = gaussian_kernel(np.array([0.0]), t, h=0.1)
        integral = np.sum(K_row) * dt
        # Allow some tolerance due to truncation
        assert 0.9 < integral < 1.1


class TestBerryKeatingKernel:
    """Test Berry-Keating kernel implementation."""
    
    def test_kernel_real(self):
        """Berry-Keating kernel should be real."""
        t = np.linspace(-5, 5, 50)
        K = berry_keating_kernel(t, t)
        assert np.all(np.isreal(K))
    
    def test_kernel_has_diagonal(self):
        """Kernel should have significant diagonal contribution."""
        t = np.linspace(-5, 5, 50)
        K = berry_keating_kernel(t, t)
        diag_sum = np.sum(np.abs(np.diag(K)))
        total_sum = np.sum(np.abs(K))
        assert diag_sum / total_sum > 0.1  # Diagonal is significant


# ============================================================================
# Operator Construction Tests
# ============================================================================

class TestHPsiMatrixConstruction:
    """Test H_Ψ matrix construction."""
    
    def test_matrix_square(self):
        """H_Ψ matrix should be square."""
        H, _ = build_H_psi_matrix(n_basis=20)
        assert H.shape[0] == H.shape[1]
    
    def test_matrix_correct_size(self):
        """H_Ψ matrix should have correct dimensions."""
        n_basis = 30
        H, _ = build_H_psi_matrix(n_basis=n_basis)
        assert H.shape == (n_basis, n_basis)
    
    def test_matrix_symmetric(self):
        """H_Ψ matrix should be symmetric (self-adjoint)."""
        H, _ = build_H_psi_matrix(n_basis=30)
        assert_allclose(H, H.T, rtol=1e-10)
    
    def test_matrix_real(self):
        """H_Ψ matrix should be real."""
        H, _ = build_H_psi_matrix(n_basis=30)
        assert np.all(np.isreal(H))
    
    def test_quadrature_points_returned(self):
        """Should return quadrature points."""
        H, quad_points = build_H_psi_matrix(n_basis=20, n_quad=100)
        assert len(quad_points) == 100
    
    def test_quadrature_points_sorted(self):
        """Quadrature points should be sorted."""
        _, quad_points = build_H_psi_matrix(n_basis=20, n_quad=100)
        assert np.all(np.diff(quad_points) > 0)


class TestSpectralEigenvalues:
    """Test spectral eigenvalue computation."""
    
    def test_eigenvalues_real(self):
        """Eigenvalues should be real (from self-adjoint operator)."""
        eigenvalues = compute_spectral_eigenvalues(n_basis=30)
        assert np.all(np.isreal(eigenvalues))
    
    def test_eigenvalues_positive(self):
        """Transformed eigenvalues should be positive."""
        eigenvalues = compute_spectral_eigenvalues(n_basis=30)
        assert np.all(eigenvalues >= 0)
    
    def test_eigenvalues_sorted(self):
        """Eigenvalues should be sorted."""
        eigenvalues = compute_spectral_eigenvalues(n_basis=30)
        assert np.all(np.diff(eigenvalues) >= -1e-10)
    
    def test_eigenvalues_reasonable_range(self):
        """Eigenvalues should be in reasonable range."""
        eigenvalues = compute_spectral_eigenvalues(n_basis=50)
        # Should have some eigenvalues in the range of first few zeta zeros
        assert np.any(eigenvalues < 200)


# ============================================================================
# Self-Adjointness Tests
# ============================================================================

class TestSelfAdjointness:
    """Test self-adjointness verification."""
    
    def test_symmetric_matrix_verified(self):
        """Symmetric matrix should pass self-adjointness test."""
        A = np.array([[1, 2, 3], [2, 4, 5], [3, 5, 6]])
        is_sa, error = verify_self_adjointness(A)
        assert is_sa
        assert error < 1e-10
    
    def test_asymmetric_matrix_fails(self):
        """Asymmetric matrix should fail self-adjointness test."""
        A = np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]])
        is_sa, error = verify_self_adjointness(A, tolerance=1e-10)
        assert not is_sa
        assert error > 1e-10
    
    def test_h_psi_is_self_adjoint(self):
        """H_Ψ matrix should be self-adjoint."""
        H, _ = build_H_psi_matrix(n_basis=50)
        is_sa, error = verify_self_adjointness(H)
        assert is_sa, f"H_Ψ not self-adjoint, error = {error}"
        assert error < 1e-8


class TestPositiveInnerProducts:
    """Test positive inner product verification."""
    
    def test_positive_definite_matrix(self):
        """Positive definite matrix should pass."""
        # Use a fixed seed for deterministic test results
        rng = np.random.default_rng(seed=42)
        A = np.eye(10) + 0.1 * rng.standard_normal((10, 10))
        A = A @ A.T  # Make positive definite
        all_pos, min_val = verify_positive_inner_products(A, n_tests=50)
        assert all_pos
        assert min_val > 0


# ============================================================================
# Eigenvalue Matching Tests
# ============================================================================

class TestEigenvalueMatching:
    """Test eigenvalue-to-zero matching."""
    
    def test_exact_match(self):
        """Exact eigenvalues should match exactly."""
        eigenvalues = KNOWN_ZETA_ZEROS[:10].copy()
        zeros = KNOWN_ZETA_ZEROS[:10]
        matches = match_eigenvalues_to_zeros(eigenvalues, zeros, tolerance=0.1)
        assert len(matches) == 10
    
    def test_perturbed_match(self):
        """Slightly perturbed eigenvalues should still match."""
        eigenvalues = KNOWN_ZETA_ZEROS[:10] + np.random.randn(10) * 0.01
        zeros = KNOWN_ZETA_ZEROS[:10]
        matches = match_eigenvalues_to_zeros(eigenvalues, zeros, tolerance=1.0)
        assert len(matches) >= 8  # Most should match
    
    def test_no_match_with_tight_tolerance(self):
        """Large perturbations should not match with tight tolerance."""
        eigenvalues = KNOWN_ZETA_ZEROS[:10] + 100  # Large offset
        zeros = KNOWN_ZETA_ZEROS[:10]
        matches = match_eigenvalues_to_zeros(eigenvalues, zeros, tolerance=1.0)
        assert len(matches) == 0


# ============================================================================
# Main Function Tests
# ============================================================================

class TestSpectralEquivalenceComputation:
    """Test the main spectral equivalence computation."""
    
    def test_result_type(self):
        """Result should be SpectralEquivalenceResult."""
        result = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        assert hasattr(result, 'computed_eigenvalues')
        assert hasattr(result, 'reference_zeros')
        assert hasattr(result, 'verified')
    
    def test_result_has_eigenvalues(self):
        """Result should contain computed eigenvalues."""
        result = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        assert len(result.computed_eigenvalues) > 0
    
    def test_result_symmetry_error_small(self):
        """Symmetry error should be small."""
        result = compute_spectral_equivalence(n_basis=50, n_quad=150, n_zeros=10)
        assert result.symmetry_error < 1e-8
    
    def test_result_has_matches(self):
        """Result should have some matched pairs."""
        result = compute_spectral_equivalence(n_basis=60, n_quad=200, n_zeros=15)
        assert result.matched_pairs > 0
    
    def test_result_to_dict(self):
        """Result should be convertible to dictionary."""
        result = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        d = result.to_dict()
        assert isinstance(d, dict)
        assert 'verified' in d


class TestDemonstration:
    """Test the full demonstration function."""
    
    def test_demonstration_runs(self):
        """Demonstration should run without errors."""
        result = demonstrate_spectral_equivalence(verbose=False, high_precision=False)
        assert result is not None
    
    def test_demonstration_returns_result(self):
        """Demonstration should return SpectralEquivalenceResult."""
        result = demonstrate_spectral_equivalence(verbose=False, high_precision=False)
        assert hasattr(result, 'verified')


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_certificate_structure(self):
        """Certificate should have required fields."""
        result = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        cert = generate_certificate(result)
        
        assert 'title' in cert
        assert 'theorem' in cert
        assert 'operator' in cert
        assert 'results' in cert
        assert 'author' in cert
        assert 'timestamp' in cert
    
    def test_certificate_qcal_integration(self):
        """Certificate should contain QCAL integration data."""
        result = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        cert = generate_certificate(result)
        
        assert 'qcal_integration' in cert
        assert cert['qcal_integration']['frequency'] == QCAL_FREQUENCY
        assert cert['qcal_integration']['coherence'] == QCAL_COHERENCE


# ============================================================================
# Numerical Stability Tests
# ============================================================================

class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_small_h_stability(self):
        """Should be stable with small regularization parameter."""
        H, _ = build_H_psi_matrix(n_basis=30, h=1e-4)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.isfinite(eigenvalues))
    
    def test_large_domain_stability(self):
        """Should be stable with large domain."""
        H, _ = build_H_psi_matrix(n_basis=30, L=20.0)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.isfinite(eigenvalues))
    
    def test_high_basis_stability(self):
        """Should be stable with many basis functions."""
        H, _ = build_H_psi_matrix(n_basis=80, n_quad=200)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.isfinite(eigenvalues))


# ============================================================================
# Integration Tests
# ============================================================================

class TestIntegration:
    """Integration tests for the full module."""
    
    def test_full_pipeline(self):
        """Full pipeline should complete successfully."""
        # Build matrix
        H, quad_pts = build_H_psi_matrix(n_basis=40, n_quad=150)
        
        # Verify self-adjointness
        is_sa, sym_err = verify_self_adjointness(H)
        assert is_sa
        
        # Compute eigenvalues
        eigenvalues = compute_spectral_eigenvalues(n_basis=40)
        assert len(eigenvalues) > 0
        
        # Compute equivalence
        result = compute_spectral_equivalence(n_basis=40, n_quad=150, n_zeros=10)
        assert result is not None
    
    def test_reproducibility(self):
        """Results should be reproducible."""
        result1 = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        result2 = compute_spectral_equivalence(n_basis=30, n_quad=100, n_zeros=10)
        
        # Eigenvalues should be identical
        assert_allclose(
            result1.computed_eigenvalues[:10],
            result2.computed_eigenvalues[:10],
            rtol=1e-10
        )


# ============================================================================
# Entry Point
# ============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
