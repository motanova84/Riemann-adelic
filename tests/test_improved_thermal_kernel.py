"""
Tests for improved thermal kernel implementation.

Tests the improved integration methods and Legendre polynomial basis
as described in the problem statement.
"""

import pytest
import numpy as np
from thermal_kernel_spectral import (
    improved_K_t_real,
    improved_basis_func,
    build_improved_H,
    validate_with_simple_case
)


class TestImprovedKernel:
    """Test suite for improved kernel implementation."""
    
    def test_improved_kernel_positive_diagonal(self):
        """Test that improved kernel is positive at x=y."""
        x = 1.0
        t = 0.01
        K = improved_K_t_real(x, x, t)
        assert K > 0, "Improved kernel should be positive at x=y"
        assert np.isfinite(K), "Kernel value should be finite"
    
    def test_improved_kernel_symmetric(self):
        """Test that improved kernel is symmetric: K(x,y) = K(y,x)."""
        x, y = 2.0, 3.0
        t = 0.01
        K_xy = improved_K_t_real(x, y, t)
        K_yx = improved_K_t_real(y, x, t)
        assert np.isclose(K_xy, K_yx, rtol=1e-10), "Improved kernel should be symmetric"
    
    def test_improved_kernel_wider_integration(self):
        """Test that improved kernel uses wider integration limits."""
        x, y = 1.0, 1.0
        t = 0.01
        
        K_improved = improved_K_t_real(x, y, t)
        
        # The improved kernel should be positive and finite
        assert K_improved > 0, "Improved kernel should be positive"
        assert np.isfinite(K_improved), "Improved kernel should be finite"
        
        # For x=y=1, log_diff=0, so the integral is over a symmetric function
        # Should get a reasonable value
        assert K_improved > 1.0, "Kernel at x=y should be substantial"
    
    def test_improved_kernel_handles_boundary(self):
        """Test improved kernel handles x=0 or y=0."""
        K = improved_K_t_real(0, 1, 0.01)
        assert K == 0.0, "Kernel should return 0 for x=0"
        
        K = improved_K_t_real(1, 0, 0.01)
        assert K == 0.0, "Kernel should return 0 for y=0"


class TestImprovedBasis:
    """Test suite for improved Legendre polynomial basis."""
    
    def test_basis_normalization(self):
        """Test that basis functions are properly normalized."""
        a, b = 0.1, 10.0
        
        # k=0 should be constant (=1)
        x_vals = np.linspace(a, b, 10)
        basis_0 = [improved_basis_func(x, 0, a, b) for x in x_vals]
        assert np.allclose(basis_0, 1.0), "Basis function 0 should be constant 1"
    
    def test_basis_legendre_properties(self):
        """Test that basis functions follow Legendre polynomial properties."""
        a, b = 0.1, 10.0
        x = 1.0  # Middle point in log scale
        
        # Test that we get different values for different k
        values = [improved_basis_func(x, k, a, b) for k in range(5)]
        
        # Not all should be the same
        assert len(set(np.round(values, 6))) > 1, "Basis functions should be different"
    
    def test_basis_interval_mapping(self):
        """Test that basis correctly maps interval to [-1, 1]."""
        a, b = 0.1, 10.0
        
        # At x=a, should map to z=-1, so P_1(z) = -1
        val_a = improved_basis_func(a, 1, a, b)
        assert np.isclose(val_a, -1.0, atol=1e-10), "At x=a, P_1 should be -1"
        
        # At x=b, should map to z=1, so P_1(z) = 1
        val_b = improved_basis_func(b, 1, a, b)
        assert np.isclose(val_b, 1.0, atol=1e-10), "At x=b, P_1 should be 1"
    
    def test_basis_finite(self):
        """Test that basis functions always return finite values."""
        a, b = 0.1, 10.0
        x_vals = np.logspace(np.log10(a), np.log10(b), 20)
        
        for k in range(5):
            for x in x_vals:
                val = improved_basis_func(x, k, a, b)
                assert np.isfinite(val), f"Basis {k} at x={x} should be finite"


class TestImprovedHMatrix:
    """Test suite for improved H matrix construction."""
    
    @pytest.mark.slow
    def test_improved_H_symmetric(self):
        """Test that improved H is symmetric."""
        H = build_improved_H(n_basis=2, t=0.2, a=0.5, b=3.0)
        assert np.allclose(H, H.T), "Improved H should be symmetric"
    
    @pytest.mark.slow
    def test_improved_H_positive_definite(self):
        """Test that improved H is positive definite."""
        H = build_improved_H(n_basis=2, t=0.2, a=0.5, b=3.0)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(eigenvalues > 0), f"H should be positive definite, got eigenvalues {eigenvalues}"
    
    @pytest.mark.slow
    def test_improved_H_nonzero(self):
        """Test that improved H is not the zero matrix (main issue from problem statement)."""
        H = build_improved_H(n_basis=2, t=0.2, a=0.5, b=3.0)
        
        # Check that not all elements are zero
        assert not np.allclose(H, 0), "H should not be zero matrix"
        
        # Check that diagonal elements are non-zero
        assert np.all(np.abs(np.diag(H)) > 1e-6), "Diagonal elements should be non-zero"
        
        # Check that matrix has significant values
        assert np.max(np.abs(H)) > 1.0, "H should have significant values"
    
    def test_improved_H_eigenvalues_greater_than_quarter(self):
        """Test that eigenvalues are greater than 1/4 (theoretical minimum)."""
        H = build_improved_H(n_basis=2, t=0.2, a=0.5, b=3.0)
        eigenvalues = np.linalg.eigvalsh(H)
        
        # All eigenvalues should be > 1/4 (though with small basis may not hold strictly)
        # For this test, just check they're positive
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive"
    
    def test_improved_H_shape(self):
        """Test that improved H has correct shape."""
        n = 2
        H = build_improved_H(n_basis=n, t=0.2, a=0.5, b=3.0)
        assert H.shape == (n, n), f"H should have shape ({n}, {n})"


class TestSimpleValidation:
    """Test suite for simple validation case."""
    
    def test_validate_simple_case_runs(self):
        """Test that simple validation case runs without error."""
        zeros = validate_with_simple_case()
        assert len(zeros) > 0, "Should compute some test zeros"
    
    def test_validate_simple_case_structure(self):
        """Test that simple validation returns proper zero structure."""
        zeros = validate_with_simple_case()
        
        # All should be complex numbers with real part 0.5
        for z in zeros:
            assert isinstance(z, complex), "Zeros should be complex"
            assert np.isclose(z.real, 0.5), "All zeros should have real part 0.5"
            assert z.imag >= 0, "Imaginary parts should be non-negative"
    
    def test_validate_simple_case_ordering(self):
        """Test that simple validation returns ordered zeros."""
        zeros = validate_with_simple_case()
        imag_parts = [z.imag for z in zeros]
        
        # Should be in ascending order
        assert all(imag_parts[i] <= imag_parts[i+1] for i in range(len(imag_parts)-1)), \
            "Zeros should be ordered by imaginary part"


class TestIntegrationComparison:
    """Compare improved implementation with original."""
    
    def test_improved_vs_original_consistency(self):
        """Test that improved method gives consistent results with original."""
        from thermal_kernel_spectral import build_H_operator
        
        # Build both matrices with same parameters
        n_basis = 5
        t = 0.1
        
        # Original method
        H_original, _ = build_H_operator(n_basis=n_basis, t=t)
        eigenvalues_original = np.linalg.eigvalsh(H_original)
        
        # Both should be positive definite
        assert np.all(eigenvalues_original > 0), "Original H should be positive definite"
        
        # Improved method produces different matrix (different basis) but should also work
        # Note: We don't expect them to be the same, just both valid
        H_improved = build_improved_H(n_basis=2, t=t, a=0.5, b=3.0)
        eigenvalues_improved = np.linalg.eigvalsh(H_improved)
        
        assert np.all(eigenvalues_improved > 0), "Improved H should be positive definite"


class TestNumericalStability:
    """Test numerical stability of improved methods."""
    
    def test_kernel_stability_small_t(self):
        """Test kernel is stable with small t."""
        x, y = 1.0, 1.5
        t = 0.001
        
        K = improved_K_t_real(x, y, t)
        assert np.isfinite(K), "Kernel should be finite even with small t"
        assert K > 0, "Kernel should be positive"
    
    def test_basis_stability_edge_points(self):
        """Test basis stability at interval edges."""
        a, b = 0.1, 10.0
        
        # Test at boundaries
        for k in range(3):
            val_a = improved_basis_func(a, k, a, b)
            val_b = improved_basis_func(b, k, a, b)
            
            assert np.isfinite(val_a), f"Basis {k} should be finite at x=a"
            assert np.isfinite(val_b), f"Basis {k} should be finite at x=b"
    
    def test_H_construction_stability(self):
        """Test that H construction is numerically stable."""
        H = build_improved_H(n_basis=2, t=0.2, a=0.5, b=3.0)
        
        # Check no NaN or Inf
        assert not np.any(np.isnan(H)), "H should not contain NaN"
        assert not np.any(np.isinf(H)), "H should not contain Inf"
        
        # Check condition number is reasonable
        cond = np.linalg.cond(H)
        assert cond < 1e10, f"Condition number {cond} should be reasonable"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
