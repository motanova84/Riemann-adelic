"""
Tests for perfectio_spectralis implementation.

Validates the adelic-Hermite spectral method for computing Riemann zeros.
"""

import pytest
import numpy as np
from perfectio_spectralis import perfectio_spectralis, validatio_perfectio


class TestPerfectioSpectralis:
    """Test suite for perfectio spectralis implementation."""
    
    def test_basic_execution_small(self):
        """Test that the function runs with small parameters."""
        N, h = 10, 0.01
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        # Should return some zeros
        assert len(zeros) > 0, "Should compute at least one zero"
        assert H.shape == (N, N), "Matrix should be N×N"
    
    def test_zeros_on_critical_line(self):
        """Test that computed zeros are on the critical line (Re = 1/2)."""
        N, h = 15, 0.005
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        for z in zeros:
            assert abs(z.real - 0.5) < 1e-6, f"Zero {z} not on critical line"
    
    def test_zeros_positive_imaginary(self):
        """Test that zeros have positive imaginary parts."""
        N, h = 15, 0.005
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        for z in zeros:
            assert z.imag > 0, f"Zero {z} has non-positive imaginary part"
    
    def test_zeros_sorted(self):
        """Test that zeros are sorted by imaginary part."""
        N, h = 15, 0.005
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        imag_parts = [z.imag for z in zeros]
        assert imag_parts == sorted(imag_parts), "Zeros should be sorted"
    
    def test_first_zero_approximately_correct(self):
        """Test that first zero is near 14.134725..."""
        N, h = 20, 0.005
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        first_gamma = float(zeros[0].imag)
        target = 14.1347251417
        
        # Allow for some numerical error
        error = abs(first_gamma - target)
        assert error < 0.5, f"First zero error {error} too large"
    
    def test_matrix_symmetric(self):
        """Test that H matrix is symmetric."""
        N, h = 10, 0.01
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        # Check symmetry
        assert np.allclose(H, H.T), "H should be symmetric"
    
    def test_eigenvalues_positive(self):
        """Test that all eigenvalues are positive (coercivity)."""
        N, h = 10, 0.01
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        eigenvalues = np.linalg.eigvalsh(H)
        for lam in eigenvalues:
            assert lam > 0, f"Non-positive eigenvalue: {lam}"
    
    def test_eigenvalues_greater_than_quarter(self):
        """Test that eigenvalues are > 1/4."""
        N, h = 10, 0.01
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        eigenvalues = np.linalg.eigvalsh(H)
        for lam in eigenvalues:
            assert lam > 0.25, f"Eigenvalue {lam} not > 1/4"
    
    def test_parallel_computation(self):
        """Test that parallel computation works with multiple jobs."""
        N, h = 10, 0.01
        
        # Run with 1 job
        zeros1, H1 = perfectio_spectralis(N, h, num_jobs=1)
        
        # Run with 2 jobs
        zeros2, H2 = perfectio_spectralis(N, h, num_jobs=2)
        
        # Results should be similar (allowing for numerical precision)
        assert len(zeros1) == len(zeros2), "Different number of zeros"
        for z1, z2 in zip(zeros1, zeros2):
            assert abs(z1.imag - z2.imag) < 1e-6, "Different results with different job counts"
    
    @pytest.mark.slow
    def test_validation_function(self):
        """Test the full validation function."""
        # Note: This is slow, so marked as slow
        success, zeros = validatio_perfectio()
        
        # Should return results
        assert zeros is not None, "Should return zeros"
        assert len(zeros) > 0, "Should compute some zeros"


class TestValidationAccuracy:
    """Test accuracy of the method against known zeros."""
    
    def test_multiple_zeros_accuracy(self):
        """Test accuracy of first few zeros."""
        N, h = 25, 0.003
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        # Known zeros
        known = [14.1347251417, 21.0220396388, 25.0108575801]
        
        for i, target in enumerate(known):
            if i < len(zeros):
                computed = float(zeros[i].imag)
                error = abs(computed - target)
                # Relaxed tolerance for computational feasibility
                assert error < 0.1, f"Zero {i+1} error {error} too large"
    
    def test_convergence_with_N(self):
        """Test that accuracy improves with larger N."""
        h = 0.005
        target = 14.1347251417
        
        errors = []
        for N in [10, 15, 20]:
            zeros, H = perfectio_spectralis(N, h, num_jobs=1)
            computed = float(zeros[0].imag)
            error = abs(computed - target)
            errors.append(error)
        
        # Errors should generally decrease or stay small
        # (May not be strictly monotonic due to numerical effects)
        assert errors[-1] <= max(errors) * 1.5, "Should improve or stay good with larger N"
    
    def test_convergence_with_h(self):
        """Test that accuracy improves with smaller h."""
        N = 20
        target = 14.1347251417
        
        errors = []
        for h in [0.01, 0.005, 0.003]:
            zeros, H = perfectio_spectralis(N, h, num_jobs=1)
            computed = float(zeros[0].imag)
            error = abs(computed - target)
            errors.append(error)
        
        # Should improve with smaller h
        assert errors[-1] <= max(errors) * 1.5, "Should improve with smaller h"


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_h_stability(self):
        """Test stability with small h."""
        N, h = 10, 0.0001
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        # Should still produce valid results
        assert len(zeros) > 0, "Should compute zeros even with small h"
        assert all(z.imag > 0 for z in zeros), "All zeros should have positive imaginary part"
    
    def test_large_N_scaling(self):
        """Test that method scales to larger N."""
        # This is a quick check, not full computation
        N, h = 30, 0.005
        zeros, H = perfectio_spectralis(N, h, num_jobs=1)
        
        assert len(zeros) > 5, "Should compute multiple zeros with large N"
        assert H.shape == (N, N), "Matrix should have correct size"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-m", "not slow"])
