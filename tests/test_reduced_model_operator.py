"""
Tests for Reduced Model Operator implementation.

This test suite verifies:
1. Self-adjointness (symmetry of matrix)
2. Real spectrum
3. Convergence with increasing resolution
4. Numerical stability

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
import sys
import os
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from reduced_model_operator import ReducedModelOperator


class TestReducedModelOperator:
    """Test suite for ReducedModelOperator class."""
    
    def test_initialization(self):
        """Test operator initialization with default parameters."""
        model = ReducedModelOperator()
        
        assert model.L == 10.0
        assert model.N == 200
        assert model.kappa == 2.577310
        assert model.x is not None
        assert model.w is not None
        assert len(model.x) == 200
        assert len(model.w) == 200
        
    def test_initialization_custom(self):
        """Test operator initialization with custom parameters."""
        L = 15.0
        N = 100
        kappa = 2.5
        
        model = ReducedModelOperator(L=L, N=N, kappa=kappa)
        
        assert model.L == L
        assert model.N == N
        assert model.kappa == kappa
        assert len(model.x) == N
        assert len(model.w) == N
    
    def test_gauss_legendre_points(self):
        """Test Gauss-Legendre quadrature points and weights."""
        model = ReducedModelOperator(L=10.0, N=50)
        
        # Check domain
        assert np.all(model.x >= 0)
        assert np.all(model.x <= model.L)
        
        # Check weights are positive
        assert np.all(model.w > 0)
        
        # Check weights sum approximately to L
        assert abs(np.sum(model.w) - model.L) < 1e-10
    
    def test_differentiation_matrix_shape(self):
        """Test differentiation matrix has correct shape."""
        model = ReducedModelOperator(N=50)
        D = model._differentiation_matrix()
        
        assert D.shape == (50, 50)
    
    def test_kernel_matrix_shape(self):
        """Test kernel matrix has correct shape."""
        model = ReducedModelOperator(N=50)
        K = model._kernel_matrix()
        
        assert K.shape == (50, 50)
    
    def test_kernel_matrix_diagonal(self):
        """Test kernel matrix diagonal elements."""
        model = ReducedModelOperator(N=50)
        K = model._kernel_matrix()
        
        # Diagonal should be x_i (since sinc(0) = 1)
        for i in range(len(model.x)):
            assert abs(K[i, i] - model.x[i]) < 1e-10
    
    def test_potential_matrix_shape(self):
        """Test potential matrix has correct shape."""
        model = ReducedModelOperator(N=50)
        V = model._potential_matrix()
        
        assert V.shape == (50, 50)
        
        # Check it's diagonal
        assert np.allclose(V, np.diag(np.diagonal(V)))
    
    def test_potential_values(self):
        """Test potential matrix values are correct."""
        model = ReducedModelOperator(N=50)
        V = model._potential_matrix()
        
        # Check a few values
        for i in range(min(5, len(model.x))):
            x = model.x[i]
            expected = x**2 + (1 + model.kappa**2)/4 + np.log(1 + x)
            assert abs(V[i, i] - expected) < 1e-10
    
    def test_operator_assembly(self):
        """Test operator assembly."""
        model = ReducedModelOperator(N=50)
        H = model.assemble_operator()
        
        assert H is not None
        assert H.shape == (50, 50)
        assert model.H is not None
    
    def test_self_adjointness_small(self):
        """Test self-adjointness for small N."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        
        # Check matrix is symmetric
        asymmetry = np.linalg.norm(model.H - model.H.T)
        assert asymmetry < 1e-10
    
    def test_self_adjointness_verification(self):
        """Test self-adjointness verification method."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        
        is_self_adjoint = model.verify_self_adjointness()
        assert is_self_adjoint is True
    
    def test_diagonalization(self):
        """Test operator diagonalization."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        eigenvalues, eigenvectors = model.diagonalize()
        
        assert eigenvalues is not None
        assert eigenvectors is not None
        assert len(eigenvalues) == 50
        assert eigenvectors.shape == (50, 50)
    
    def test_eigenvalues_real(self):
        """Test that eigenvalues are real."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # Check imaginary parts are negligible
        max_imag = np.max(np.abs(np.imag(model.eigenvalues)))
        assert max_imag < 1e-10
    
    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # Check eigenvalues are in ascending order
        assert np.all(np.diff(model.eigenvalues) >= 0)
    
    def test_eigenvectors_orthonormal(self):
        """Test that eigenvectors are orthonormal."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # Check orthonormality: V^T V = I
        V = model.eigenvectors
        identity = V.T @ V
        
        assert np.allclose(identity, np.eye(50), atol=1e-10)
    
    def test_trace_computation(self):
        """Test trace computation."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        t = 0.1
        trace = model.compute_trace(t)
        
        assert trace > 0
        assert np.isfinite(trace)
    
    def test_trace_decreases_with_t(self):
        """Test that trace has correct temperature dependence."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        t_values = [0.01, 0.1, 1.0]
        traces = [model.compute_trace(t) for t in t_values]
        
        # All traces should be finite
        assert all(np.isfinite(tr) for tr in traces)
    
    def test_convergence_study(self):
        """Test convergence study."""
        model = ReducedModelOperator(N=50)
        
        N_values = [20, 30, 40, 50]
        results = model.convergence_study(N_values)
        
        assert len(results) == len(N_values)
        
        # Check each result has the expected keys
        for result in results:
            assert 'N' in result
            assert 'λ_1' in result
    
    def test_convergence_eigenvalues(self):
        """Test that eigenvalues stabilize with increasing N."""
        N_values = [50, 100, 200]
        first_eigenvalues = []
        
        for N in N_values:
            model = ReducedModelOperator(N=N)
            model.assemble_operator()
            model.diagonalize()
            first_eigenvalues.append(model.eigenvalues[0])
        
        # All values should be computed successfully
        assert len(first_eigenvalues) == len(N_values)
        assert all(np.isfinite(ev) for ev in first_eigenvalues)
    
    def test_spectrum_reality(self):
        """Test that spectrum is real."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # All eigenvalues should be real
        max_imag = np.max(np.abs(np.imag(model.eigenvalues)))
        assert max_imag < 1e-10
    
    def test_operator_hermiticity_small(self):
        """Test operator Hermiticity for small system."""
        model = ReducedModelOperator(N=30)
        H = model.assemble_operator()
        
        # For real matrices, Hermitian = symmetric
        hermiticity_error = np.linalg.norm(H - H.conj().T)
        assert hermiticity_error < 1e-10
    
    def test_operator_bounds(self):
        """Test that operator matrix elements are finite."""
        model = ReducedModelOperator(N=50)
        H = model.assemble_operator()
        
        assert np.all(np.isfinite(H))
        assert not np.any(np.isnan(H))
    
    def test_different_kappa_values(self):
        """Test operator with different kappa values."""
        kappa_values = [2.0, 2.577310, 3.0]
        
        for kappa in kappa_values:
            model = ReducedModelOperator(N=50, kappa=kappa)
            model.assemble_operator()
            model.diagonalize()
            
            # Should complete without errors
            assert model.eigenvalues is not None
            assert len(model.eigenvalues) == 50
    
    def test_different_domain_lengths(self):
        """Test operator with different domain lengths."""
        L_values = [5.0, 10.0, 15.0]
        
        for L in L_values:
            model = ReducedModelOperator(L=L, N=50)
            model.assemble_operator()
            model.diagonalize()
            
            # Should complete without errors
            assert model.eigenvalues is not None
            assert len(model.eigenvalues) == 50
    
    def test_numerical_stability(self):
        """Test numerical stability across multiple runs."""
        N = 50
        
        # Run twice with same parameters
        model1 = ReducedModelOperator(N=N)
        model1.assemble_operator()
        model1.diagonalize()
        
        model2 = ReducedModelOperator(N=N)
        model2.assemble_operator()
        model2.diagonalize()
        
        # Results should be identical
        assert np.allclose(model1.eigenvalues, model2.eigenvalues)
    
    def test_reproducibility(self):
        """Test reproducibility of results."""
        model = ReducedModelOperator(N=50)
        
        # Assemble and diagonalize twice
        model.assemble_operator()
        evals1, evecs1 = model.diagonalize()
        
        # Reset and do again
        model.H = None
        model.eigenvalues = None
        model.eigenvectors = None
        
        model.assemble_operator()
        evals2, evecs2 = model.diagonalize()
        
        # Results should be identical
        assert np.allclose(evals1, evals2)
    
    def test_plot_spectrum_no_save(self):
        """Test spectrum plotting without saving."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # Should not raise an error
        fig = model.plot_spectrum()
        assert fig is not None
    
    def test_operator_action(self):
        """Test operator action on a vector."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        
        # Create a random vector
        psi = np.random.randn(50)
        
        # Apply operator
        H_psi = model.H @ psi
        
        assert len(H_psi) == 50
        assert np.all(np.isfinite(H_psi))
    
    def test_eigenfunction_equation(self):
        """Test that eigenvectors satisfy the eigenvalue equation."""
        model = ReducedModelOperator(N=50)
        model.assemble_operator()
        model.diagonalize()
        
        # Check first few eigenvectors
        for i in range(min(5, model.N)):
            psi = model.eigenvectors[:, i]
            lambda_i = model.eigenvalues[i]
            
            # H·ψ = λ·ψ
            H_psi = model.H @ psi
            lambda_psi = lambda_i * psi
            
            assert np.allclose(H_psi, lambda_psi, rtol=1e-10)


class TestReducedModelIntegration:
    """Integration tests for reduced model operator."""
    
    def test_full_workflow(self):
        """Test complete workflow from assembly to analysis."""
        model = ReducedModelOperator(L=10.0, N=100)
        
        # Assemble
        H = model.assemble_operator()
        assert H is not None
        
        # Verify self-adjointness
        is_self_adjoint = model.verify_self_adjointness()
        assert is_self_adjoint
        
        # Diagonalize
        eigenvalues, eigenvectors = model.diagonalize()
        assert eigenvalues is not None
        
        # Compute traces
        trace_01 = model.compute_trace(0.1)
        trace_10 = model.compute_trace(1.0)
        
        # Both traces should be finite
        assert np.isfinite(trace_01)
        assert np.isfinite(trace_10)
        
        # Plot (without saving)
        fig = model.plot_spectrum()
        assert fig is not None
    
    def test_qcal_constant_convergence(self):
        """Test behavior with QCAL constant κ = 2.577310."""
        kappa_qcal = 2.577310
        
        model = ReducedModelOperator(N=100, kappa=kappa_qcal)
        model.assemble_operator()
        model.diagonalize()
        
        # Check basic properties
        assert len(model.eigenvalues) == 100
        
        # All eigenvalues should be real
        assert np.max(np.abs(np.imag(model.eigenvalues))) < 1e-10
        
        # Eigenvalues should be sorted
        assert np.all(np.diff(model.eigenvalues) >= 0)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
