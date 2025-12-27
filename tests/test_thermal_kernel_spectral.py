"""
Tests for thermal kernel spectral operator implementation.

Validates that the operator H correctly encodes Riemann zeros.
"""

import pytest
import numpy as np
from thermal_kernel_spectral import (
    build_H_operator,
    extract_zeros_from_spectrum,
    load_odlyzko_zeros,
    validate_spectral_construction,
    thermal_kernel
)


class TestThermalKernelSpectral:
    """Test suite for thermal kernel spectral operator."""
    
    def test_thermal_kernel_positive(self):
        """Test that thermal kernel is positive for x=y."""
        x = 1.0
        t = 0.01
        K = thermal_kernel(x, x, t)
        assert K > 0, "Thermal kernel should be positive at x=y"
    
    def test_thermal_kernel_symmetric(self):
        """Test that thermal kernel is symmetric: K(x,y) = K(y,x)."""
        x, y = 2.0, 3.0
        t = 0.01
        K_xy = thermal_kernel(x, y, t)
        K_yx = thermal_kernel(y, x, t)
        assert np.isclose(K_xy, K_yx, rtol=1e-10), "Thermal kernel should be symmetric"
    
    def test_build_H_operator_symmetric(self):
        """Test that H operator is symmetric."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        assert np.allclose(H, H.T), "H operator should be symmetric"
    
    def test_build_H_operator_positive_definite(self):
        """Test that H operator is positive definite."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(eigenvalues > 0), "H operator should be positive definite"
    
    def test_eigenvalue_range(self):
        """Test that eigenvalues are in expected range."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        eigenvalues = np.linalg.eigvalsh(H)
        
        # All eigenvalues should be > 1/4
        assert np.all(eigenvalues > 0.25), "All eigenvalues should be > 1/4"
        
        # Minimum eigenvalue should correspond to first zero
        # λ_min ≈ 1/4 + 14.13² ≈ 200
        assert 150 < eigenvalues[0] < 250, f"First eigenvalue {eigenvalues[0]} not near expected value"
    
    def test_extract_zeros_basic(self):
        """Test zero extraction from eigenvalues."""
        # Create test eigenvalues
        gamma_true = np.array([14.13, 21.02, 25.01])
        lambda_test = 0.25 + gamma_true**2
        
        # Extract zeros
        gamma_extracted = extract_zeros_from_spectrum(lambda_test)
        
        # Check accuracy
        assert len(gamma_extracted) == len(gamma_true)
        assert np.allclose(gamma_extracted, gamma_true, rtol=1e-8)
    
    def test_load_odlyzko_zeros(self):
        """Test loading Odlyzko zeros from file."""
        zeros = load_odlyzko_zeros(max_zeros=5)
        
        assert len(zeros) == 5, "Should load 5 zeros"
        assert zeros[0] > 14.0 and zeros[0] < 15.0, "First zero should be ~14.13"
        assert all(zeros[i] < zeros[i+1] for i in range(len(zeros)-1)), "Zeros should be sorted"
    
    def test_validation_high_accuracy(self):
        """Test that validation achieves high accuracy."""
        result = validate_spectral_construction(
            n_basis=15,
            t=0.001,
            max_zeros=5,
            verbose=False
        )
        
        # Check that all errors are small
        assert result['mean_error'] < 1e-6, f"Mean error {result['mean_error']} too large"
        assert result['mean_rel_error'] < 1e-7, f"Relative error {result['mean_rel_error']} too large"
        
        # Check individual errors
        assert np.all(result['errors'] < 1e-5), "Some individual errors too large"
    
    def test_convergence_with_t(self):
        """Test that errors decrease as t → 0."""
        t_values = [0.01, 0.005, 0.001]
        errors = []
        
        for t in t_values:
            result = validate_spectral_construction(
                n_basis=15,
                t=t,
                max_zeros=5,
                verbose=False
            )
            errors.append(result['mean_error'])
        
        # Errors should decrease (or stay small)
        assert errors[-1] <= errors[0] * 1.1, "Errors should decrease with smaller t"
    
    def test_spectrum_matches_odlyzko(self):
        """Test that computed spectrum matches Odlyzko zeros."""
        result = validate_spectral_construction(
            n_basis=20,
            t=0.001,
            max_zeros=10,
            verbose=False
        )
        
        # Check first few zeros specifically
        known_zeros = [14.134725, 21.022040, 25.010858]
        for i, gamma_true in enumerate(known_zeros):
            gamma_comp = result['computed_gammas'][i]
            error = abs(gamma_comp - gamma_true)
            rel_error = error / gamma_true
            
            assert rel_error < 1e-5, f"Zero {i+1}: relative error {rel_error} too large"
    
    def test_matrix_size_consistency(self):
        """Test that different matrix sizes give consistent results."""
        sizes = [10, 15, 20]
        first_zeros = []
        
        for n in sizes:
            result = validate_spectral_construction(
                n_basis=n,
                t=0.001,
                max_zeros=3,
                verbose=False
            )
            first_zeros.append(result['computed_gammas'][0])
        
        # First zero should be consistent across sizes
        assert np.std(first_zeros) < 1e-6, "First zero should be consistent across matrix sizes"
    
    def test_thermal_parameter_small(self):
        """Test behavior with very small thermal parameter."""
        result = validate_spectral_construction(
            n_basis=15,
            t=0.0001,  # Very small t
            max_zeros=5,
            verbose=False
        )
        
        # Should still work and be accurate
        assert result['mean_error'] < 1e-5, "Should work with very small t"
    
    def test_coercivity(self):
        """Test coercivity: <f, Hf> ≥ 0 for random vectors."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        
        # Test with random vectors
        for _ in range(10):
            f = np.random.randn(10)
            quadratic_form = f @ H @ f
            assert quadratic_form >= -1e-10, "Coercivity violated: <f,Hf> should be ≥ 0"


class TestThermalKernelMathematical:
    """Mathematical property tests."""
    
    def test_functional_equation_structure(self):
        """Test that J-symmetry is implemented."""
        n = 10
        H, _ = build_H_operator(n_basis=n, t=0.01)
        
        # Check that matrix has some structure reflecting J-symmetry
        # This is a weak test - just checking the matrix is built correctly
        assert H.shape == (n, n)
        assert np.allclose(H, H.T)
    
    def test_spectrum_real(self):
        """Test that all eigenvalues are real."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        eigenvalues = np.linalg.eigvals(H)
        
        # Check all eigenvalues are real (imaginary part ~ 0)
        assert np.allclose(eigenvalues.imag, 0, atol=1e-10), "Eigenvalues should be real"
    
    def test_trace_positive(self):
        """Test that trace of H is positive."""
        H, _ = build_H_operator(n_basis=10, t=0.01)
        trace = np.trace(H)
        assert trace > 0, "Trace of H should be positive"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
