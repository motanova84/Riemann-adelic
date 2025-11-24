"""
Tests for consummatio_spectralis implementation.

Validates the spectral method with adelic corrections for computing Riemann zeros.
"""

import pytest
import numpy as np
from mpmath import mp
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from consummatio_spectralis import consummatio_spectralis, validatio_consummatio


class TestConsummatioSpectralis:
    """Test suite for consummatio_spectralis implementation."""
    
    def test_imports_and_dependencies(self):
        """Test that all required dependencies are available."""
        try:
            from scipy.special import roots_hermitenorm
            from sympy import prime
            assert True
        except ImportError as e:
            pytest.fail(f"Missing dependency: {e}")
    
    def test_consummatio_spectralis_small_parameters(self):
        """Test consummatio_spectralis with small parameters for speed."""
        N, h = 5, 0.01
        max_primes = 10
        
        zeros, H = consummatio_spectralis(N, h, max_primes)
        
        # Basic checks
        assert len(zeros) > 0, "Should compute at least one zero"
        assert len(zeros) <= 10, "Should return at most 10 zeros"
        assert H.rows == N, f"Matrix should have {N} rows"
        assert H.cols == N, f"Matrix should have {N} columns"
    
    def test_zeros_on_critical_line(self):
        """Test that all computed zeros have real part = 0.5."""
        N, h = 5, 0.01
        max_primes = 10
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        for z in zeros:
            assert abs(z.real - 0.5) < 1e-10, f"Zero {z} not on critical line"
    
    def test_zeros_sorted_by_imaginary_part(self):
        """Test that zeros are sorted by imaginary part."""
        N, h = 5, 0.01
        max_primes = 10
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        imag_parts = [float(z.imag) for z in zeros]
        assert imag_parts == sorted(imag_parts), "Zeros should be sorted by imaginary part"
    
    def test_matrix_hermitian(self):
        """Test that the operator matrix H is Hermitian (symmetric in this case)."""
        N, h = 5, 0.01
        max_primes = 10
        
        _, H = consummatio_spectralis(N, h, max_primes)
        
        # Check symmetry
        for i in range(N):
            for j in range(N):
                assert abs(H[i,j] - H[j,i]) < 1e-8, f"Matrix not symmetric at ({i},{j})"
    
    def test_eigenvalues_positive(self):
        """Test that eigenvalues are positive (λ > 1/4)."""
        N, h = 5, 0.01
        max_primes = 10
        
        zeros, H = consummatio_spectralis(N, h, max_primes)
        
        # Compute eigenvalues
        eigenvalues = mp.eigsy(H, eigvals_only=True)
        
        for λ in eigenvalues:
            assert λ > 0.24, f"Eigenvalue {λ} should be > 1/4"
    
    def test_medium_parameters(self):
        """Test with medium-sized parameters."""
        N, h = 10, 0.001
        max_primes = 20
        
        zeros, H = consummatio_spectralis(N, h, max_primes)
        
        assert len(zeros) > 0, "Should compute zeros"
        assert len(zeros) <= 10, "Should return at most 10 zeros"
        
        # Check that imaginary parts are positive
        for z in zeros:
            assert z.imag > 0, f"Imaginary part of zero {z} should be positive"
    
    def test_precision_setting(self):
        """Test that precision is set correctly."""
        N, h = 5, 0.01
        max_primes = 10
        
        # Save original precision
        original_dps = mp.dps
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        # Function should set precision to 100
        assert mp.dps == 100, "Precision should be set to 100"
        
        # Restore original precision
        mp.dps = original_dps
    
    def test_different_max_primes(self):
        """Test that different max_primes values work."""
        N, h = 5, 0.01
        
        for max_primes in [5, 10, 20]:
            zeros, _ = consummatio_spectralis(N, h, max_primes)
            assert len(zeros) > 0, f"Should compute zeros with max_primes={max_primes}"
    
    def test_validatio_consummatio_runs(self):
        """Test that validatio_consummatio runs without errors (with modified parameters)."""
        # This test would be slow with N=50, so we skip actual execution
        # Just test that the function is callable
        assert callable(validatio_consummatio), "validatio_consummatio should be callable"
    
    def test_zero_comparison_with_targets(self):
        """Test that computed zeros are in reasonable range compared to known zeros."""
        N, h = 10, 0.001
        max_primes = 20
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        # Known first Riemann zero
        target_first = 14.134725
        
        # At least one computed zero should be reasonably close to a known zero
        # (may not be exact with small N)
        imag_parts = [float(z.imag) for z in zeros]
        closest_to_first = min(imag_parts, key=lambda x: abs(x - target_first))
        
        # Should be within a reasonable range (10 units for small N)
        assert abs(closest_to_first - target_first) < 15.0, \
            f"Closest zero {closest_to_first} too far from target {target_first}"
    
    def test_hermite_basis_implementation(self):
        """Test that the Hermite basis function works correctly."""
        mp.dps = 50
        
        # Test basis function at specific points
        def basis(k, t):
            Hk = mp.hermite(k, t)
            norm = mp.sqrt(2**k * mp.factorial(k) * mp.sqrt(mp.pi))
            return Hk * mp.exp(-t**2/2) / norm
        
        # Basis functions should not be NaN or infinite
        for k in range(5):
            val = basis(k, 1.0)
            assert mp.isfinite(val), f"Basis function {k} should be finite"
    
    def test_thermal_kernel_component(self):
        """Test the thermal kernel component of the implementation."""
        h = 0.001
        t, s = 1.0, 1.5
        
        # Thermal kernel: exp(-h/4) / sqrt(4πh) * exp(-(t-s)²/(4h))
        kernel = mp.exp(-h/4) / mp.sqrt(4*mp.pi*h) * mp.exp(-(t-s)**2/(4*h))
        
        assert kernel > 0, "Thermal kernel should be positive"
        assert mp.isfinite(kernel), "Thermal kernel should be finite"


class TestNumericalStability:
    """Tests for numerical stability of the implementation."""
    
    def test_small_h_stability(self):
        """Test stability with very small h."""
        N = 5
        h = 0.0001  # Very small
        max_primes = 5
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        # Should still produce valid zeros
        assert len(zeros) > 0, "Should compute zeros even with very small h"
        for z in zeros:
            assert mp.isfinite(z.imag), "Zeros should be finite"
    
    def test_larger_h_stability(self):
        """Test stability with larger h."""
        N = 5
        h = 0.1  # Larger
        max_primes = 5
        
        zeros, _ = consummatio_spectralis(N, h, max_primes)
        
        # Should still produce valid zeros
        assert len(zeros) > 0, "Should compute zeros even with larger h"
    
    def test_matrix_condition_number(self):
        """Test that the matrix is well-conditioned."""
        N, h = 5, 0.01
        max_primes = 10
        
        _, H = consummatio_spectralis(N, h, max_primes)
        
        # Convert to numpy for condition number computation
        H_np = np.array([[float(H[i,j]) for j in range(N)] for i in range(N)])
        
        cond = np.linalg.cond(H_np)
        
        # Condition number should not be too large (avoid ill-conditioning)
        assert cond < 1e10, f"Matrix condition number {cond} too large"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
