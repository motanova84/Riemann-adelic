#!/usr/bin/env python3
"""
Tests for Positive Definite Kernel Theorem
==========================================

Tests the implementation of the theorem connecting positive definite
kernels to the Riemann Hypothesis critical line.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL Frequency: f₀ = 141.7001 Hz
"""

import pytest
import numpy as np
import sys
import os

# Add repository root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from positive_kernel_rh_theorem import (
    PositiveDefiniteKernel,
    HilbertSchmidtOperator,
    RiemannZetaSpectralConnection
)


class TestPositiveDefiniteKernel:
    """Test suite for PositiveDefiniteKernel class."""
    
    def test_gaussian_kernel_creation(self):
        """Test Gaussian kernel creation."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        assert kernel.kernel_type == "gaussian"
        assert kernel.sigma == 1.0
        assert kernel.f0 == 141.7001
    
    def test_kernel_symmetry(self):
        """Test kernel symmetry K(x,y) = K(y,x)."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        
        test_cases = [
            (0.0, 1.0),
            (-1.5, 2.3),
            (5.0, -5.0),
            (0.5, 0.5)
        ]
        
        for x, y in test_cases:
            assert kernel.verify_symmetry(x, y), f"Symmetry failed for ({x}, {y})"
    
    def test_kernel_positivity(self):
        """Test kernel positivity K(x,y) ≥ 0."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        
        # Test various points
        for x in np.linspace(-5, 5, 10):
            for y in np.linspace(-5, 5, 10):
                k_val = kernel.K(x, y)
                assert k_val >= 0, f"Kernel negative at ({x}, {y}): {k_val}"
    
    def test_positive_definiteness(self):
        """Test positive definiteness of Gram matrix."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        
        # Test with different point sets
        for n_points in [5, 10, 20]:
            points = np.linspace(-3, 3, n_points)
            is_pos_def, quad_form, min_eig = kernel.verify_positive_definiteness(points)
            
            assert is_pos_def, f"Failed positive definiteness for {n_points} points"
            assert quad_form >= -1e-10, f"Quadratic form negative: {quad_form}"
            assert min_eig >= -1e-10, f"Min eigenvalue negative: {min_eig}"
    
    def test_different_kernel_types(self):
        """Test different kernel implementations."""
        kernel_types = ["gaussian", "heat", "exponential"]
        
        for ktype in kernel_types:
            kernel = PositiveDefiniteKernel(kernel_type=ktype, sigma=1.0)
            
            # Verify basic properties
            assert kernel.K(0, 0) > 0, f"{ktype} kernel not positive at origin"
            assert kernel.verify_symmetry(1.0, 2.0), f"{ktype} kernel not symmetric"


class TestHilbertSchmidtOperator:
    """Test suite for HilbertSchmidtOperator class."""
    
    def test_operator_creation(self):
        """Test operator creation."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        operator = HilbertSchmidtOperator(kernel, domain=(-5, 5))
        
        assert operator.kernel == kernel
        assert operator.domain == (-5, 5)
    
    def test_operator_discretization(self):
        """Test operator discretization."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        operator = HilbertSchmidtOperator(kernel, domain=(-5, 5))
        
        for n_basis in [10, 20]:
            T_matrix = operator.discretize(n_basis)
            
            # Check dimensions
            assert T_matrix.shape == (n_basis, n_basis), "Wrong matrix dimensions"
            
            # Check symmetry
            symmetry_error = np.max(np.abs(T_matrix - T_matrix.T))
            assert symmetry_error < 1e-10, f"Matrix not symmetric: {symmetry_error}"
            
            # Check real values
            assert np.all(np.isreal(T_matrix)), "Matrix has complex values"
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        operator = HilbertSchmidtOperator(kernel, domain=(-5, 5))
        
        eigenvalues, eigenvectors = operator.compute_spectrum(n_basis=20)
        
        # Check eigenvalues are real
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-10, "Eigenvalues not real"
        
        # Check eigenvalues are non-negative
        assert np.all(eigenvalues.real >= -1e-10), "Eigenvalues negative"
        
        # Check eigenvectors are orthonormal
        orthogonality = eigenvectors.T @ eigenvectors
        identity = np.eye(len(eigenvalues))
        orth_error = np.max(np.abs(orthogonality - identity))
        assert orth_error < 1e-8, f"Eigenvectors not orthonormal: {orth_error}"


class TestRiemannZetaSpectralConnection:
    """Test suite for RiemannZetaSpectralConnection class."""
    
    def test_connection_creation(self):
        """Test spectral connection creation."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        connection = RiemannZetaSpectralConnection(kernel)
        
        assert connection.kernel == kernel
        assert connection.operator is not None
    
    def test_spectral_reality_condition(self):
        """Test spectral reality conditions."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        connection = RiemannZetaSpectralConnection(kernel)
        
        all_conditions_met, details = connection.spectral_reality_condition(n_basis=20)
        
        # Verify all conditions
        assert all_conditions_met, "Spectral reality conditions not met"
        assert details['is_real_spectrum'], "Spectrum not real"
        assert details['is_nonnegative'], "Spectrum has negative values"
        assert details['is_symmetric'], "Operator not symmetric"
        assert details['max_imaginary_part'] < 1e-10, "Eigenvalues have imaginary part"
        assert details['min_eigenvalue'] >= -1e-10, "Negative eigenvalue found"
    
    def test_critical_line_implication(self):
        """Test critical line implication logic."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        connection = RiemannZetaSpectralConnection(kernel)
        
        result = connection.critical_line_implication()
        
        # Verify logical chain
        assert result['step1_kernel_positive_definite'], "Kernel not positive definite"
        assert result['step2_spectrum_real'], "Spectrum not real"
        assert result['step3_functional_equation'], "Functional equation not satisfied"
        assert result['conclusion_critical_line_re_1_2'], "Critical line not forced"
        assert result['logical_chain_complete'], "Logical chain incomplete"
    
    def test_qcal_frequency(self):
        """Test QCAL frequency marker."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        
        expected_f0 = 141.7001
        assert abs(kernel.f0 - expected_f0) < 1e-6, f"Wrong QCAL frequency: {kernel.f0}"


class TestIntegration:
    """Integration tests for the complete theorem."""
    
    def test_complete_theorem_validation(self):
        """Test complete theorem validation."""
        # This mirrors the validation script
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        connection = RiemannZetaSpectralConnection(kernel)
        
        # Step 1: Verify kernel positivity
        points = np.linspace(-4, 4, 25)
        is_pos_def, _, _ = kernel.verify_positive_definiteness(points)
        assert is_pos_def, "Kernel not positive definite"
        
        # Step 2: Verify self-adjointness
        operator = connection.operator
        T_matrix = operator.discretize(n_basis=20)
        symmetry_error = np.max(np.abs(T_matrix - T_matrix.T))
        assert symmetry_error < 1e-10, "Operator not self-adjoint"
        
        # Step 3: Verify spectrum
        eigenvalues, _ = operator.compute_spectrum(n_basis=20)
        assert np.all(eigenvalues.real >= -1e-10), "Negative eigenvalues"
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-10, "Complex eigenvalues"
        
        # Step 4: Verify critical line implication
        result = connection.critical_line_implication()
        assert result['conclusion_critical_line_re_1_2'], "Critical line not proven"
    
    def test_multiple_kernel_types(self):
        """Test theorem with multiple kernel types."""
        kernel_types = ["gaussian", "heat", "exponential"]
        
        for ktype in kernel_types:
            kernel = PositiveDefiniteKernel(kernel_type=ktype, sigma=1.0)
            
            # Verify positivity
            points = np.linspace(-3, 3, 15)
            is_pos_def, _, _ = kernel.verify_positive_definiteness(points)
            assert is_pos_def, f"{ktype} kernel not positive definite"
            
            # Verify spectral properties
            connection = RiemannZetaSpectralConnection(kernel)
            all_ok, _ = connection.spectral_reality_condition(n_basis=15)
            assert all_ok, f"{ktype} kernel spectral conditions failed"


# Pytest markers
@pytest.mark.slow
class TestComputationalIntensive:
    """Computationally intensive tests (marked as slow)."""
    
    def test_high_dimensional_spectrum(self):
        """Test spectrum with higher dimensional basis."""
        kernel = PositiveDefiniteKernel(kernel_type="gaussian", sigma=1.0)
        operator = HilbertSchmidtOperator(kernel, domain=(-5, 5))
        
        # This might be slow
        eigenvalues, _ = operator.compute_spectrum(n_basis=50)
        
        assert np.all(eigenvalues.real >= -1e-10), "Negative eigenvalues in high dimension"
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-10, "Complex eigenvalues"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
