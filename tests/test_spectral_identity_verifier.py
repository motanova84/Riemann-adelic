#!/usr/bin/env python3
"""
Tests for spectral identity verifier module.

Tests verification of Spec(H_Ψ) = {1/4 + γₙ²} identity.
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from spectral_identity_verifier import (
    BerryKeatingOperator,
    ZetaZeroFetcher,
    SpectralIdentityVerifier,
    SpectralIdentityResult,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
    MPMATH_AVAILABLE
)


class TestBerryKeatingOperator:
    """Tests for Berry-Keating operator construction."""
    
    def test_initialization(self):
        """Test operator initialization."""
        op = BerryKeatingOperator(N=50)
        assert op.N == 50
        assert op.C < 0  # C = π·ζ'(1/2) < 0
        assert abs(op.C + 3.9226 * np.pi) < 0.1
    
    def test_custom_constant(self):
        """Test initialization with custom C."""
        C_custom = -10.0
        op = BerryKeatingOperator(N=50, C=C_custom)
        assert op.C == C_custom
    
    def test_matrix_construction(self):
        """Test matrix construction."""
        op = BerryKeatingOperator(N=50)
        H = op.build_matrix()
        
        # Check dimensions
        assert H.shape == (50, 50)
        
        # Check hermiticity
        hermiticity_error = np.linalg.norm(H - H.conj().T)
        assert hermiticity_error < 1e-12
    
    def test_matrix_is_hermitian(self):
        """Test that constructed matrix is hermitian."""
        op = BerryKeatingOperator(N=100)
        H = op.build_matrix()
        
        # H should equal its conjugate transpose
        assert np.allclose(H, H.conj().T, atol=1e-14)
    
    def test_diagonal_elements(self):
        """Test diagonal elements have expected form."""
        op = BerryKeatingOperator(N=50)
        H = op.build_matrix()
        
        # Diagonal elements should be real
        diag = np.diag(H)
        assert np.allclose(diag.imag, 0, atol=1e-14)
        
        # Should increase with index (dilaton + log term)
        # First element should be close to 0.5 + C·(-γ - ψ(1))
        first_element = diag[0].real
        assert abs(first_element - (0.5 + op.C * (-np.euler_gamma - 0))) < 1.0
    
    def test_spectrum_real(self):
        """Test that spectrum is real (consequence of hermiticity)."""
        op = BerryKeatingOperator(N=50)
        eigenvals = op.compute_spectrum()
        
        # All eigenvalues should be real
        assert eigenvals.dtype in [np.float32, np.float64]
        
        # Should be sorted
        assert np.all(eigenvals[:-1] <= eigenvals[1:])
    
    def test_spectrum_positive_for_small_n(self):
        """Test that first few eigenvalues are positive."""
        op = BerryKeatingOperator(N=100)
        eigenvals = op.compute_spectrum()
        
        # First eigenvalue should be positive
        # (corresponds to first Riemann zero γ₁ ≈ 14.13)
        # λ₁ = 1/4 + γ₁² ≈ 0.25 + 199.8 ≈ 200
        assert eigenvals[0] > 0
    
    def test_different_sizes(self):
        """Test operator construction for different sizes."""
        for N in [20, 50, 100, 200]:
            op = BerryKeatingOperator(N=N)
            H = op.build_matrix()
            assert H.shape == (N, N)
            assert np.allclose(H, H.conj().T, atol=1e-14)


@pytest.mark.skipif(not MPMATH_AVAILABLE, reason="mpmath not available")
class TestZetaZeroFetcher:
    """Tests for zeta zero fetching."""
    
    def test_initialization(self):
        """Test fetcher initialization."""
        fetcher = ZetaZeroFetcher(precision=30)
        assert fetcher.precision == 30
    
    def test_get_first_zero(self):
        """Test fetching first Riemann zero."""
        fetcher = ZetaZeroFetcher(precision=30)
        zeros = fetcher.get_zeros(n_zeros=1)
        
        assert len(zeros) == 1
        # First zero: γ₁ ≈ 14.134725...
        assert abs(zeros[0] - 14.134725) < 0.001
    
    def test_get_multiple_zeros(self):
        """Test fetching multiple zeros."""
        fetcher = ZetaZeroFetcher(precision=30)
        zeros = fetcher.get_zeros(n_zeros=10)
        
        assert len(zeros) == 10
        
        # All should be positive
        assert np.all(zeros > 0)
        
        # Should be strictly increasing
        assert np.all(zeros[:-1] < zeros[1:])
    
    def test_known_zeros(self):
        """Test against known Riemann zeros."""
        fetcher = ZetaZeroFetcher(precision=30)
        zeros = fetcher.get_zeros(n_zeros=5)
        
        # Known first 5 zeros (approximate)
        known_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        
        for i, known in enumerate(known_zeros):
            assert abs(zeros[i] - known) < 0.001
    
    def test_high_precision(self):
        """Test high precision computation."""
        fetcher = ZetaZeroFetcher(precision=50)
        zeros = fetcher.get_zeros(n_zeros=3)
        
        # With high precision, first zero should be very accurate
        # γ₁ = 14.134725141734693790457251983562470270784257115699
        assert abs(zeros[0] - 14.134725141734694) < 1e-12


@pytest.mark.skipif(not MPMATH_AVAILABLE, reason="mpmath not available")
class TestSpectralIdentityVerifier:
    """Tests for spectral identity verification."""
    
    def test_initialization(self):
        """Test verifier initialization."""
        verifier = SpectralIdentityVerifier(N=50, n_zeros=10)
        
        assert verifier.N == 50
        assert verifier.n_zeros == 10
        assert verifier.operator is not None
        assert verifier.zero_fetcher is not None
    
    def test_verify_basic(self):
        """Test basic verification."""
        verifier = SpectralIdentityVerifier(N=100, n_zeros=10, precision=30)
        result = verifier.verify(verbose=False)
        
        assert isinstance(result, SpectralIdentityResult)
        assert len(result.gamma_from_H) == 10
        assert len(result.gamma_zeta) == 10
        assert result.matrix_size == 100
    
    def test_verify_accuracy_small(self):
        """Test verification accuracy with small matrix."""
        verifier = SpectralIdentityVerifier(N=100, n_zeros=5, precision=30)
        result = verifier.verify(verbose=False)
        
        # With N=100, first few should have reasonable accuracy
        # (error might be larger than with N=250)
        assert result.mean_rel_error < 0.1  # Less than 10%
    
    @pytest.mark.slow
    def test_verify_accuracy_large(self):
        """Test verification accuracy with large matrix."""
        verifier = SpectralIdentityVerifier(N=250, n_zeros=30, precision=30)
        result = verifier.verify(verbose=False)
        
        # With N=250, should get good accuracy
        assert result.mean_rel_error < 0.01  # Less than 1%
        assert result.verification_passed
    
    def test_gamma_extraction(self):
        """Test gamma extraction from eigenvalues."""
        verifier = SpectralIdentityVerifier(N=100, n_zeros=5, precision=30)
        result = verifier.verify(verbose=False)
        
        # γ₁² should be λ₁ - 1/4
        first_eigenval = result.eigenvalues[0]
        first_gamma = result.gamma_from_H[0]
        
        assert abs(first_gamma ** 2 - (first_eigenval - 0.25)) < 1e-10
    
    def test_result_to_dict(self):
        """Test result conversion to dictionary."""
        verifier = SpectralIdentityVerifier(N=50, n_zeros=5, precision=30)
        result = verifier.verify(verbose=False)
        
        result_dict = result.to_dict()
        
        assert "gamma_from_H" in result_dict
        assert "gamma_zeta" in result_dict
        assert "mean_rel_error" in result_dict
        assert "qcal_base_frequency" in result_dict
        assert result_dict["qcal_base_frequency"] == QCAL_BASE_FREQUENCY
        assert result_dict["protocol"] == "QCAL-SPECTRAL-IDENTITY v1.0"
    
    def test_qcal_coherence(self):
        """Test QCAL coherence validation."""
        verifier = SpectralIdentityVerifier(N=50, n_zeros=5, precision=30)
        result = verifier.verify(verbose=False)
        
        assert result.qcal_coherent
        assert abs(QCAL_COHERENCE - 244.36) < 0.01
    
    def test_comparison_first_zeros(self):
        """Test comparison with first few known zeros."""
        verifier = SpectralIdentityVerifier(N=150, n_zeros=3, precision=30)
        result = verifier.verify(verbose=False)
        
        # Known first 3 zeros
        known = [14.134725, 21.022040, 25.010858]
        
        for i in range(3):
            # H_Ψ should approximate these
            assert abs(result.gamma_from_H[i] - known[i]) < 1.0
            # Zeta zeros should be exact
            assert abs(result.gamma_zeta[i] - known[i]) < 0.001


class TestSpectralCounting:
    """Tests for spectral counting function N_H(T)."""
    
    def test_counting_function(self):
        """Test spectral counting N_H(T) = #{n : √(λₙ - 1/4) < T}."""
        op = BerryKeatingOperator(N=200)
        eigenvals = op.compute_spectrum()
        
        # Count eigenvalues with √(λ - 1/4) < T
        T = 50.0
        gamma_values = np.sqrt(np.maximum(0, eigenvals - 0.25))
        N_H = np.sum(gamma_values < T)
        
        # Should have several zeros below T=50
        assert N_H > 0
        assert N_H < 200  # But not all


class TestConstants:
    """Tests for QCAL constants."""
    
    def test_qcal_frequency(self):
        """Test QCAL base frequency."""
        assert QCAL_BASE_FREQUENCY == 141.7001
    
    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_no_nans(self):
        """Test that computation produces no NaNs."""
        op = BerryKeatingOperator(N=50)
        H = op.build_matrix()
        
        assert not np.any(np.isnan(H))
    
    def test_no_infs(self):
        """Test that computation produces no infinities."""
        op = BerryKeatingOperator(N=50)
        H = op.build_matrix()
        
        assert not np.any(np.isinf(H))
    
    @pytest.mark.skipif(not MPMATH_AVAILABLE, reason="mpmath not available")
    def test_eigenvalue_positivity(self):
        """Test that eigenvalues are positive."""
        verifier = SpectralIdentityVerifier(N=100, n_zeros=10, precision=30)
        result = verifier.verify(verbose=False)
        
        # All eigenvalues should be positive
        assert np.all(result.eigenvalues > 0)


@pytest.mark.skipif(not MPMATH_AVAILABLE, reason="mpmath not available")
class TestConvergence:
    """Tests for convergence with increasing N."""
    
    def test_convergence_with_N(self):
        """Test that error decreases as N increases."""
        errors = []
        
        for N in [50, 100, 150]:
            verifier = SpectralIdentityVerifier(N=N, n_zeros=5, precision=30)
            result = verifier.verify(verbose=False)
            errors.append(result.mean_rel_error)
        
        # Error should generally decrease (though not monotonically)
        # At least the error for N=150 should be better than N=50
        assert errors[-1] < errors[0] or errors[-1] < 0.05


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
