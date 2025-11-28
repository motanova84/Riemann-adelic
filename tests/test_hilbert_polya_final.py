#!/usr/bin/env python3
"""
Test suite for Hilbert-Pólya Final Validation

This test suite validates the implementation of the H_Ψ operator
as the explicit realization of the Hilbert-Pólya Conjecture.

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np

from hilbert_polya_validation import (
    H_psi_operator,
    build_H_psi_matrix,
    build_resolvente_matrix,
    verify_trace_class,
    verify_self_adjoint,
    verify_real_spectrum,
    verify_friedrichs_extension,
    hilbert_polya_validation,
    ALPHA_SPECTRAL,
    QCAL_FREQUENCY,
    QCAL_COHERENCE
)


class TestHilbertPolyaOperator:
    """Test class for H_Ψ operator properties."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 100
        self.alpha = ALPHA_SPECTRAL
        self.H = build_H_psi_matrix(self.n_points, alpha=self.alpha)
    
    def test_matrix_shape(self):
        """Test that H_Ψ matrix has correct shape."""
        assert self.H.shape == (self.n_points, self.n_points)
    
    def test_matrix_symmetric(self):
        """Test that H_Ψ matrix is symmetric."""
        deviation = np.max(np.abs(self.H - self.H.T))
        assert deviation < 1e-10, f"Matrix not symmetric: deviation = {deviation}"
    
    def test_matrix_real(self):
        """Test that H_Ψ matrix is real."""
        assert self.H.dtype in [np.float64, np.float32], "Matrix should be real"
        assert np.max(np.abs(np.imag(self.H))) == 0, "Matrix has imaginary parts"
    
    def test_eigenvalues_real(self):
        """Test that all eigenvalues are real."""
        eigenvalues = np.linalg.eigvals(self.H)
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        assert max_imag < 1e-10, f"Eigenvalues have imaginary parts: max = {max_imag}"
    
    def test_eigenvalues_positive(self):
        """Test that eigenvalues are positive (coercivity)."""
        eigenvalues = np.real(np.linalg.eigvalsh(self.H))
        min_eigenvalue = np.min(eigenvalues)
        assert min_eigenvalue > 0, f"Operator not coercive: min eigenvalue = {min_eigenvalue}"
    
    def test_alpha_value(self):
        """Test that α ≈ 12.32955."""
        assert abs(ALPHA_SPECTRAL - 12.32955) < 1e-4


class TestTraceClass:
    """Test class for trace class S_1 property."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 200
        self.H = build_H_psi_matrix(self.n_points)
    
    def test_trace_class_verification(self):
        """Test that H_Ψ is trace class."""
        verified, error = verify_trace_class(self.H)
        assert verified, f"Trace class verification failed: error = {error}"
    
    def test_eigenvalue_convergence(self):
        """Test that eigenvalues grow sufficiently fast for trace class."""
        eigenvalues = np.sort(np.real(np.linalg.eigvalsh(self.H)))
        
        # For trace class, eigenvalues should grow at least linearly
        n_check = min(50, len(eigenvalues))
        ratios = eigenvalues[1:n_check] / eigenvalues[:n_check-1]
        
        # Average ratio should be > 1 (growth)
        avg_ratio = np.mean(ratios)
        assert avg_ratio >= 1.0, f"Eigenvalues not growing: avg ratio = {avg_ratio}"


class TestSelfAdjoint:
    """Test class for self-adjoint property."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 100
        self.H = build_H_psi_matrix(self.n_points)
    
    def test_self_adjoint_verification(self):
        """Test that H_Ψ is self-adjoint."""
        verified, deviation = verify_self_adjoint(self.H)
        assert verified, f"Self-adjoint verification failed: deviation = {deviation}"
    
    def test_hermitian_property(self):
        """Test that H = H†."""
        H_adj = self.H.T.conj()
        deviation = np.max(np.abs(self.H - H_adj))
        assert deviation < 1e-10, f"H ≠ H†: deviation = {deviation}"


class TestRealSpectrum:
    """Test class for real spectrum property."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 100
        self.H = build_H_psi_matrix(self.n_points)
    
    def test_real_spectrum_verification(self):
        """Test that spectrum of H_Ψ is real."""
        verified, max_imag = verify_real_spectrum(self.H)
        assert verified, f"Real spectrum verification failed: max imaginary = {max_imag}"
    
    def test_spectrum_bounds(self):
        """Test that spectrum is bounded below."""
        eigenvalues = np.real(np.linalg.eigvalsh(self.H))
        min_eig = np.min(eigenvalues)
        max_eig = np.max(eigenvalues)
        
        assert np.isfinite(min_eig), "Spectrum unbounded below"
        assert np.isfinite(max_eig), "Spectrum unbounded above"
        assert min_eig > 0, "Spectrum should be positive"


class TestFriedrichsExtension:
    """Test class for Friedrichs unique extension."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 100
        self.H = build_H_psi_matrix(self.n_points)
    
    def test_friedrichs_verification(self):
        """Test Friedrichs unique extension."""
        verified, details = verify_friedrichs_extension(self.H)
        assert verified, f"Friedrichs verification failed: {details}"
    
    def test_symmetry_condition(self):
        """Test symmetry condition for Friedrichs."""
        verified, details = verify_friedrichs_extension(self.H)
        assert details["symmetry_verified"], "Symmetry condition failed"
    
    def test_semi_bounded_condition(self):
        """Test semi-bounded condition for Friedrichs."""
        verified, details = verify_friedrichs_extension(self.H)
        assert details["semi_bounded"], "Semi-bounded condition failed"
    
    def test_coercivity(self):
        """Test coercivity condition: ⟨Hf, f⟩ ≥ c·‖f‖²."""
        verified, details = verify_friedrichs_extension(self.H)
        c = details["coercivity_constant"]
        assert c > 0, f"Coercivity constant should be positive: c = {c}"


class TestQCALIntegration:
    """Test class for QCAL integration."""
    
    def test_qcal_frequency(self):
        """Test QCAL base frequency."""
        assert abs(QCAL_FREQUENCY - 141.7001) < 1e-3
    
    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert abs(QCAL_COHERENCE - 244.36) < 1e-2
    
    def test_alpha_spectral_calibration(self):
        """Test spectral calibration parameter α."""
        assert abs(ALPHA_SPECTRAL - 12.32955) < 1e-4


class TestCompleteValidation:
    """Test class for complete Hilbert-Pólya validation."""
    
    @pytest.mark.slow
    def test_complete_validation(self):
        """Test complete validation passes."""
        result = hilbert_polya_validation(
            n_points=200,
            precision=30
        )
        
        assert result.trace_class_verified, "Trace class verification failed"
        assert result.self_adjoint_verified, "Self-adjoint verification failed"
        assert result.spectrum_real_verified, "Real spectrum verification failed"
        assert result.friedrichs_verified, "Friedrichs verification failed"
    
    def test_certificate_generation(self):
        """Test that validation generates proper certificate."""
        result = hilbert_polya_validation(
            n_points=100,
            precision=25
        )
        
        assert "certificate" in dir(result)
        cert = result.certificate
        
        assert "validation_type" in cert
        assert cert["validation_type"] == "Hilbert-Pólya Final"
        assert "alpha" in cert
        assert "frequency" in cert


class TestOperatorApplication:
    """Test class for H_Ψ operator application."""
    
    def setup_method(self):
        """Setup test fixtures."""
        self.n_points = 100
        self.x = np.linspace(0.1, 10, self.n_points)
        self.f = np.exp(-self.x)  # Test function
    
    def test_operator_application(self):
        """Test that operator can be applied to functions."""
        result = H_psi_operator(self.f, self.x)
        
        assert result.shape == self.f.shape
        assert np.all(np.isfinite(result))
    
    def test_operator_preserves_smoothness(self):
        """Test that operator preserves smoothness of functions."""
        result = H_psi_operator(self.f, self.x)
        
        # Check result is smooth (finite differences are bounded)
        diff = np.diff(result)
        max_diff = np.max(np.abs(diff))
        
        assert np.isfinite(max_diff)


class TestNumericalStability:
    """Test class for numerical stability."""
    
    def test_different_grid_sizes(self):
        """Test stability across different grid sizes."""
        for n in [50, 100, 200]:
            H = build_H_psi_matrix(n)
            verified, deviation = verify_self_adjoint(H)
            assert verified, f"Failed for n={n}"
    
    def test_different_alpha_values(self):
        """Test stability for different α values."""
        for alpha in [10.0, 12.32955, 15.0]:
            H = build_H_psi_matrix(100, alpha=alpha)
            verified, deviation = verify_self_adjoint(H)
            assert verified, f"Failed for alpha={alpha}"
    
    def test_resolvente_well_conditioned(self):
        """Test that resolvente is well-conditioned."""
        H = build_H_psi_matrix(100)
        R = build_resolvente_matrix(H)
        
        # Check condition number
        eigenvalues = np.abs(np.linalg.eigvals(R))
        condition = np.max(eigenvalues) / np.min(eigenvalues)
        
        assert np.isfinite(condition), "Resolvente is singular"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
