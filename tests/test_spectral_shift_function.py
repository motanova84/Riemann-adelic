#!/usr/bin/env python3
"""
Test suite for Spectral Shift Function (BKS Theory).

Tests the implementation of the Birman-Koplienko-Solomyak theory for
spectral shift functions when the resolvent difference is not trace class.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import sys
from pathlib import Path

# Add repository root to path for imports
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import pytest
import numpy as np
from scipy import linalg

from operators.spectral_shift_function import (
    # Data classes
    SingularValueResult,
    SpectralShiftResult,
    ScatteringMatrixResult,
    BKSCertificate,
    # Functions
    estimate_singular_values_triangular_kernel,
    verify_s1_infinity_membership,
    compute_spectral_shift_function_bks,
    compute_spectral_shift_simplified,
    compute_scattering_matrix,
    generate_bks_certificate,
    demonstrate_bks_spectral_shift,
    # Constants
    F0_HZ,
    C_QCAL,
    KAPPA_PI
)


class TestSingularValueAnalysis:
    """Tests for singular value analysis and S₁,∞ membership."""
    
    def test_triangular_kernel_decay(self):
        """Test singular value decay for triangular kernel."""
        # Simple triangular kernel: K(x,y) = exp(-|x-y|) for x > y
        def kernel(x, y):
            if x > y:
                return np.exp(-(x - y))
            return 0.0
        
        result = estimate_singular_values_triangular_kernel(
            kernel,
            x_range=(0, 10),
            n_samples=50,
            rank=30
        )
        
        # Check that singular values were computed
        assert len(result.singular_values) > 0
        
        # Check decay rate (should be close to 1 for this kernel)
        assert result.decay_rate > 0.5
        assert result.decay_rate < 2.0
        
        # Check S₁,∞ membership
        assert isinstance(result.belongs_to_s1_infinity, bool)
        
    def test_singular_value_ordering(self):
        """Test that singular values are in decreasing order."""
        def kernel(x, y):
            return np.exp(-(x - y)**2) if x > y else 0.0
        
        result = estimate_singular_values_triangular_kernel(
            kernel,
            x_range=(0, 5),
            n_samples=40,
            rank=20
        )
        
        s = result.singular_values
        # Check decreasing order
        for i in range(len(s) - 1):
            assert s[i] >= s[i+1], f"Singular values not ordered: s[{i}] < s[{i+1}]"
    
    def test_decay_rate_fit_quality(self):
        """Test quality of power-law decay fit."""
        # Known power-law decay: sₙ = C/n^α
        def kernel(x, y):
            return 1.0 / (1 + (x - y)**2) if x > y else 0.0
        
        result = estimate_singular_values_triangular_kernel(
            kernel,
            x_range=(0, 8),
            n_samples=60,
            rank=40
        )
        
        # Residual error should be reasonable
        assert result.residual_error < 1.0
        
        # Fitted constant should be positive
        assert result.fitted_constant > 0
    
    def test_s1_infinity_membership_free_vs_perturbed(self):
        """Test S₁,∞ membership for resolvent difference."""
        n = 50
        L = 10.0
        dx = L / (n - 1)
        
        # Build Laplacian
        D2 = (np.diag(-2*np.ones(n)) + 
              np.diag(np.ones(n-1), 1) + 
              np.diag(np.ones(n-1), -1)) / dx**2
        
        # Free operator H₀ = -Δ
        H0 = -D2
        
        # Perturbed operator H = -Δ + V
        x = np.linspace(0, L, n)
        V = 1.0 / (1 + x**2)  # Long-range potential
        H = H0 + np.diag(V)
        
        # Test S₁,∞ membership
        z = 5.0 + 0.5j
        
        def H_func(x_grid):
            return H
        
        def H0_func(x_grid):
            return H0
        
        result = verify_s1_infinity_membership(
            H_func, H0_func, z,
            x_range=(0, L),
            n_samples=n
        )
        
        # Should have singular values
        assert len(result.singular_values) > 0
        
        # Check decay rate is positive
        assert result.decay_rate > 0


class TestSpectralShiftFunction:
    """Tests for spectral shift function computation."""
    
    def test_spectral_shift_simplified_method(self):
        """Test spectral shift using eigenvalue counting."""
        # Create simple example with known shift
        eigvals_H = np.array([1, 3, 5, 7, 9])
        eigvals_H0 = np.array([2, 4, 6, 8, 10])
        
        result = compute_spectral_shift_simplified(
            eigvals_H, eigvals_H0,
            lambda_range=(0, 12),
            n_lambda=100
        )
        
        # Check result structure
        assert len(result.lambda_values) == 100
        assert len(result.xi_values) == 100
        assert result.method == "Eigenvalue counting"
        
        # At λ = 0: ξ(0) = 0 - 0 = 0
        assert result.xi_values[0] == 0
        
        # At λ = 12: ξ(12) = 5 - 5 = 0 (same number of eigenvalues)
        assert result.xi_values[-1] == 0
    
    def test_spectral_shift_monotonicity(self):
        """Test that spectral shift function is monotone increasing."""
        eigvals_H = np.array([1, 2, 4, 8])
        eigvals_H0 = np.array([1.5, 3, 5, 7, 9])
        
        result = compute_spectral_shift_simplified(
            eigvals_H, eigvals_H0,
            lambda_range=(0, 10),
            n_lambda=50
        )
        
        # Check monotonicity
        xi = result.xi_values
        for i in range(len(xi) - 1):
            # ξ should be weakly increasing (or stay constant)
            assert xi[i+1] >= xi[i] - 1e-10
    
    def test_scattering_phase_relation(self):
        """Test relation between spectral shift and scattering phase."""
        eigvals_H = np.array([1, 2, 3])
        eigvals_H0 = np.array([1.1, 2.1, 3.1])
        
        result = compute_spectral_shift_simplified(
            eigvals_H, eigvals_H0,
            lambda_range=(0, 5),
            n_lambda=30
        )
        
        # Scattering phase δ = π ξ
        expected_phase = np.pi * result.xi_values
        np.testing.assert_allclose(
            result.scattering_phase,
            expected_phase,
            rtol=1e-10
        )


class TestScatteringMatrix:
    """Tests for scattering matrix computation."""
    
    def test_scattering_matrix_unitarity(self):
        """Test that scattering matrix is unitary (|det S| = 1)."""
        # Define simple spectral shift function
        def xi_func(lam):
            return 0.1 * np.tanh(lam - 2)  # Smooth function
        
        result = compute_scattering_matrix(
            xi_func,
            lambda_range=(0, 5),
            n_lambda=50
        )
        
        # Check unitarity: |det S| = |exp(-2πi ξ)| = 1
        det_abs = np.abs(result.S_matrix_det)
        np.testing.assert_allclose(det_abs, 1.0, rtol=1e-10)
        
        # Unitarity deviation should be small
        assert result.unitarity_deviation < 0.1
    
    def test_scattering_matrix_trivial_case(self):
        """Test S = I when ξ = 0 (no scattering)."""
        def xi_func(lam):
            return 0.0  # No spectral shift
        
        result = compute_scattering_matrix(
            xi_func,
            lambda_range=(0, 10),
            n_lambda=40
        )
        
        # S = exp(-2πi·0) = 1
        np.testing.assert_allclose(result.S_matrix_det, 1.0, rtol=1e-10)
        
        # Tension should be resolved (S = I)
        assert result.tension_resolved
    
    def test_scattering_eigenvalues_unit_circle(self):
        """Test that S eigenvalues lie on unit circle."""
        def xi_func(lam):
            return 0.05 * lam  # Linear shift
        
        result = compute_scattering_matrix(
            xi_func,
            lambda_range=(0, 3),
            n_lambda=30
        )
        
        # All eigenvalues should have |λ| = 1
        eigval_abs = np.abs(result.S_eigenvalues)
        np.testing.assert_allclose(eigval_abs, 1.0, rtol=1e-10)


class TestBKSCertificate:
    """Tests for QCAL certificate generation."""
    
    def test_certificate_generation(self):
        """Test BKS certificate generation with mock data."""
        # Create mock results
        sv_result = SingularValueResult(
            singular_values=np.array([1.0, 0.5, 0.33, 0.25]),
            decay_rate=1.0,
            s1_infinity_norm=2.0,
            belongs_to_s1_infinity=True,
            fitted_constant=1.0,
            residual_error=0.1
        )
        
        ss_result = SpectralShiftResult(
            lambda_values=np.linspace(0, 10, 50),
            xi_values=np.linspace(0, 1, 50),
            integrated_trace=1.0,
            scattering_phase=np.linspace(0, np.pi, 50),
            method="BKS",
            convergence_error=0.01
        )
        
        sm_result = ScatteringMatrixResult(
            lambda_values=np.linspace(0, 10, 50),
            S_matrix_det=np.ones(50),
            S_eigenvalues=np.ones(50),
            unitarity_deviation=0.01,
            tension_resolved=True,
            long_range_correction=np.zeros(50)
        )
        
        cert = generate_bks_certificate(sv_result, ss_result, sm_result)
        
        # Check certificate fields
        assert cert.protocol == "QCAL-SPECTRAL-SHIFT-BKS"
        assert cert.version == "1.0.0"
        assert cert.signature == "∴𓂀Ω∞³Φ"
        assert cert.s1_infinity_verified == True
        assert cert.spectral_shift_computed == True
        assert cert.scattering_tension_resolved == True
        
        # Check QCAL coherence
        assert 0 <= cert.qcal_coherence <= 1
        
        # Check timestamp format
        assert "Z" in cert.timestamp
    
    def test_certificate_coherence_calculation(self):
        """Test QCAL coherence metric calculation."""
        # Perfect case - all conditions met
        sv_result = SingularValueResult(
            singular_values=np.array([1.0, 0.5, 0.33]),
            decay_rate=1.5,  # Excellent decay
            s1_infinity_norm=2.0,
            belongs_to_s1_infinity=True,
            fitted_constant=1.0,
            residual_error=0.01
        )
        
        ss_result = SpectralShiftResult(
            lambda_values=np.linspace(0, 10, 50),
            xi_values=np.linspace(0, 1, 50),
            integrated_trace=1.0,
            scattering_phase=np.linspace(0, np.pi, 50),
            method="BKS",
            convergence_error=0.001  # Very small
        )
        
        sm_result = ScatteringMatrixResult(
            lambda_values=np.linspace(0, 10, 50),
            S_matrix_det=np.ones(50),
            S_eigenvalues=np.ones(50),
            unitarity_deviation=0.001,  # Excellent
            tension_resolved=True,
            long_range_correction=np.zeros(50)
        )
        
        cert = generate_bks_certificate(sv_result, ss_result, sm_result)
        
        # Should have high coherence
        assert cert.qcal_coherence >= 0.8


class TestQCALConstants:
    """Tests for QCAL fundamental constants."""
    
    def test_fundamental_constants(self):
        """Test that QCAL constants are defined correctly."""
        assert F0_HZ == 141.7001
        assert C_QCAL == 244.36
        assert abs(KAPPA_PI - 2.577310) < 1e-6
    
    def test_constant_relations(self):
        """Test mathematical relations between constants."""
        # κ_π should relate to f₀ and golden ratio
        phi = (1 + np.sqrt(5)) / 2
        # κ_π ≈ 4π / (f₀ · φ)
        kappa_computed = 4 * np.pi / (F0_HZ * phi)
        
        # Allow some tolerance
        assert abs(kappa_computed - KAPPA_PI) < 0.1


class TestFullDemonstration:
    """Integration tests using full demonstration."""
    
    @pytest.mark.slow
    def test_full_demonstration(self):
        """Test complete BKS demonstration workflow."""
        results = demonstrate_bks_spectral_shift()
        
        # Check all components present
        assert 'singular_values' in results
        assert 'spectral_shift' in results
        assert 'scattering_matrix' in results
        assert 'certificate' in results
        
        # Check singular value analysis
        sv = results['singular_values']
        assert isinstance(sv, SingularValueResult)
        
        # Check spectral shift computation
        ss = results['spectral_shift']
        assert isinstance(ss, SpectralShiftResult)
        assert len(ss.lambda_values) > 0
        assert len(ss.xi_values) > 0
        
        # Check scattering matrix
        sm = results['scattering_matrix']
        assert isinstance(sm, ScatteringMatrixResult)
        
        # Check certificate
        cert = results['certificate']
        assert isinstance(cert, BKSCertificate)
        assert cert.qcal_coherence > 0
    
    @pytest.mark.slow
    def test_demonstration_coherence_threshold(self):
        """Test that demonstration achieves minimum QCAL coherence."""
        results = demonstrate_bks_spectral_shift()
        cert = results['certificate']
        
        # Should achieve at least 50% coherence
        assert cert.qcal_coherence >= 0.5


class TestEdgeCases:
    """Tests for edge cases and error handling."""
    
    def test_empty_singular_values(self):
        """Test handling of case with no significant singular values."""
        # Create result with no singular values
        result = SingularValueResult(
            singular_values=np.array([]),
            decay_rate=0.0,
            s1_infinity_norm=0.0,
            belongs_to_s1_infinity=False,
            fitted_constant=0.0,
            residual_error=0.0
        )
        
        assert len(result.singular_values) == 0
        assert not result.belongs_to_s1_infinity
    
    def test_zero_spectral_shift(self):
        """Test case where spectral shift is identically zero."""
        eigvals_H = np.array([1, 2, 3, 4])
        eigvals_H0 = np.array([1, 2, 3, 4])  # Same eigenvalues
        
        result = compute_spectral_shift_simplified(
            eigvals_H, eigvals_H0,
            lambda_range=(0, 5),
            n_lambda=50
        )
        
        # All ξ values should be zero
        np.testing.assert_allclose(result.xi_values, 0.0, atol=1e-10)
        
        # Total shift should be zero
        assert abs(result.integrated_trace) < 1e-10


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_large_decay_rate(self):
        """Test stability with fast singular value decay."""
        # Create artificial singular values with fast decay
        n = 50
        s = np.array([1.0 / (i**2) for i in range(1, n+1)])
        
        # Should not crash
        result = SingularValueResult(
            singular_values=s,
            decay_rate=2.0,
            s1_infinity_norm=np.sum(s),
            belongs_to_s1_infinity=True,
            fitted_constant=1.0,
            residual_error=0.1
        )
        
        assert result.decay_rate == 2.0
        assert np.isfinite(result.s1_infinity_norm)
    
    def test_small_epsilon_stability(self):
        """Test stability with small epsilon in BKS formula."""
        # This would be tested with actual BKS integration
        # For now, just verify the simplified method works
        eigvals_H = np.array([1, 2, 3])
        eigvals_H0 = np.array([1.001, 2.001, 3.001])
        
        result = compute_spectral_shift_simplified(
            eigvals_H, eigvals_H0,
            lambda_range=(0, 4),
            n_lambda=100
        )
        
        # Should produce finite results
        assert np.all(np.isfinite(result.xi_values))
        assert np.all(np.isfinite(result.scattering_phase))


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
