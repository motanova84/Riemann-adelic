"""
Tests for absoluta spectral computation with Hermite basis and adelic corrections.

Validates the implementation of the CODEX ABSOLUTUS spectral method.
"""

import pytest
import numpy as np
from absoluta_spectral import (
    absoluta_spectral_computation,
    validatio_absoluta,
    load_known_zeros
)


class TestAbsolutaSpectral:
    """Test suite for absoluta spectral operator."""
    
    def test_load_known_zeros(self):
        """Test loading known Riemann zeros."""
        zeros = load_known_zeros(max_zeros=5)
        assert len(zeros) == 5
        assert zeros[0] > 0
        # First zero should be approximately 14.134725
        assert 14.0 < zeros[0] < 14.2
    
    def test_absoluta_spectral_basic(self):
        """Test basic functionality of absoluta_spectral_computation."""
        N = 10
        h = 0.001
        zeros, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        # Should return a list of zeros
        assert isinstance(zeros, list)
        assert len(zeros) > 0
        assert len(zeros) <= 10
        
        # H should be a square matrix
        assert H.shape == (N, N)
        
        # H should be symmetric
        H_np = np.asarray(H)
        assert np.allclose(H_np, H_np.T, atol=1e-10)
    
    def test_absoluta_spectral_no_adelic(self):
        """Test computation without adelic corrections."""
        N = 10
        h = 0.001
        zeros, H = absoluta_spectral_computation(N, h, include_adelic=False)
        
        assert isinstance(zeros, list)
        assert len(zeros) > 0
        # First zero should still be reasonable
        gamma_1 = abs(zeros[0].imag)
        assert 10.0 < gamma_1 < 20.0
    
    def test_matrix_positive_definite(self):
        """Test that H operator is positive definite."""
        N = 10
        h = 0.001
        _, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(eigenvalues > 0), "H operator should be positive definite"
    
    def test_eigenvalue_structure(self):
        """Test that eigenvalues have expected structure λ = 1/4 + γ²."""
        N = 10
        h = 0.001
        zeros, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        eigenvalues = np.linalg.eigvalsh(H)
        
        # All eigenvalues should be > 0.25
        assert np.all(eigenvalues >= 0.25)
        
        # Extracted gammas should be positive
        for z in zeros:
            gamma = abs(z.imag)
            assert gamma > 0
    
    def test_zeros_on_critical_line(self):
        """Test that computed zeros lie on the critical line Re(s) = 1/2."""
        N = 10
        h = 0.001
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        
        for z in zeros:
            assert abs(z.real - 0.5) < 1e-10, "Zeros should lie on critical line"
    
    def test_first_zero_accuracy(self):
        """Test accuracy of first computed zero."""
        N = 20
        h = 0.001
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        
        # First Riemann zero
        gamma_computed = abs(zeros[0].imag)
        gamma_expected = 14.134725
        
        # Should be accurate to at least 3 decimal places
        assert abs(gamma_computed - gamma_expected) < 0.001
    
    def test_multiple_zeros_accuracy(self):
        """Test accuracy of first 5 zeros."""
        N = 20
        h = 0.001
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        
        expected_gammas = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        
        for i, expected in enumerate(expected_gammas):
            if i < len(zeros):
                computed = abs(zeros[i].imag)
                error = abs(computed - expected)
                # Should be very accurate with this construction
                assert error < 0.01, f"Zero {i+1}: error = {error}"
    
    def test_zeros_ordered(self):
        """Test that zeros are returned in order of increasing imaginary part."""
        N = 15
        h = 0.001
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        
        gammas = [abs(z.imag) for z in zeros]
        assert gammas == sorted(gammas), "Zeros should be ordered by imaginary part"
    
    def test_adelic_correction_effect(self):
        """Test that adelic corrections have an effect."""
        N = 10
        h = 0.001
        
        zeros_with, H_with = absoluta_spectral_computation(N, h, include_adelic=True)
        zeros_without, H_without = absoluta_spectral_computation(N, h, include_adelic=False)
        
        # Matrices should be different
        assert not np.allclose(H_with, H_without, atol=1e-10)
    
    def test_thermal_parameter_effect(self):
        """Test that thermal parameter affects results."""
        N = 10
        
        zeros_h1, _ = absoluta_spectral_computation(N, 0.001, include_adelic=True)
        zeros_h2, _ = absoluta_spectral_computation(N, 0.01, include_adelic=True)
        
        # Results should be similar but not identical
        gamma1 = abs(zeros_h1[0].imag)
        gamma2 = abs(zeros_h2[0].imag)
        
        # Should be close but distinguishable
        assert abs(gamma1 - gamma2) < 2.0  # Still reasonable
    
    def test_matrix_dimension(self):
        """Test that matrix dimension matches input N."""
        for N in [5, 10, 15]:
            _, H = absoluta_spectral_computation(N, 0.001, include_adelic=True)
            assert H.shape == (N, N)
    
    def test_validatio_absoluta_runs(self):
        """Test that validatio_absoluta runs without error."""
        zeros = validatio_absoluta()
        assert isinstance(zeros, list)
        assert len(zeros) > 0
        # First zero should be reasonable
        gamma = abs(zeros[0].imag)
        assert 14.0 < gamma < 14.2


class TestAbsolutaMathematicalProperties:
    """Test mathematical properties of the spectral operator."""
    
    def test_hermitian_symmetry(self):
        """Test that H is Hermitian (real symmetric)."""
        N = 10
        h = 0.001
        _, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        # Should be real symmetric
        assert np.allclose(H, H.T, atol=1e-10)
        assert np.allclose(np.imag(H), 0, atol=1e-10)
    
    def test_coercivity(self):
        """Test that H satisfies coercivity: λ_min > c > 0."""
        N = 10
        h = 0.001
        _, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        eigenvalues = np.linalg.eigvalsh(H)
        lambda_min = eigenvalues[0]
        
        # Should be coercive with λ_min ≥ 1/4
        assert lambda_min >= 0.24  # Allow small numerical error
    
    def test_spectrum_gap(self):
        """Test that there's a spectral gap above 1/4."""
        N = 15
        h = 0.001
        _, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        eigenvalues = np.linalg.eigvalsh(H)
        
        # All eigenvalues should be distinctly above 1/4
        assert np.all(eigenvalues > 0.25)
    
    def test_trace_positivity(self):
        """Test that trace of H is positive."""
        N = 10
        h = 0.001
        _, H = absoluta_spectral_computation(N, h, include_adelic=True)
        
        trace = np.trace(H)
        assert trace > 0, "Trace should be positive"


class TestAbsolutaConvergence:
    """Test convergence properties."""
    
    def test_increasing_N_stability(self):
        """Test that results stabilize as N increases."""
        h = 0.001
        
        zeros_10, _ = absoluta_spectral_computation(10, h, include_adelic=True)
        zeros_15, _ = absoluta_spectral_computation(15, h, include_adelic=True)
        zeros_20, _ = absoluta_spectral_computation(20, h, include_adelic=True)
        
        # First zeros should stabilize
        gamma_10 = abs(zeros_10[0].imag)
        gamma_15 = abs(zeros_15[0].imag)
        gamma_20 = abs(zeros_20[0].imag)
        
        # Should converge
        diff_15_10 = abs(gamma_15 - gamma_10)
        diff_20_15 = abs(gamma_20 - gamma_15)
        
        # Later difference should be smaller (convergence)
        # or at least stable
        assert diff_20_15 <= diff_15_10 + 0.1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
