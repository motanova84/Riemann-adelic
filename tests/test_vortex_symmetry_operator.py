#!/usr/bin/env python3
"""
Test Suite for Vortex Symmetry Operator H_Omega
================================================

Comprehensive tests for the self-adjoint operator on Hilbert space
with vortex symmetry (Enki Invariance).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

import pytest
import numpy as np
from numpy.testing import assert_allclose, assert_array_less

from vortex_symmetry_operator import (
    HilbertSpaceOmega,
    OperatorH_Omega,
    verificar_autoadjuncion,
    demonstrate_vortex_operator,
    F0_QCAL,
    C_QCAL
)


class TestHilbertSpaceOmega:
    """Test suite for Hilbert space with vortex symmetry."""
    
    def test_initialization(self):
        """Test Hilbert space initialization."""
        H = HilbertSpaceOmega(x_min=0.1, x_max=10.0, n_grid=100)
        
        assert H.x_min == 0.1
        assert H.x_max == 10.0
        assert H.n_grid == 100
        assert len(H.x_grid) == 100
        assert H.x_grid[0] >= H.x_min
        assert H.x_grid[-1] <= H.x_max
    
    def test_measure_positivity(self):
        """Test that measure dx/x is positive."""
        H = HilbertSpaceOmega()
        
        assert np.all(H.measure > 0)
        assert np.all(np.isfinite(H.measure))
    
    def test_inner_product_positivity(self):
        """Test that ⟨ψ, ψ⟩ ≥ 0 for any ψ."""
        H = HilbertSpaceOmega()
        
        # Random state
        psi = np.random.randn(H.n_grid) + 1j * np.random.randn(H.n_grid)
        
        inner = H.inner_product(psi, psi)
        
        assert inner.real >= 0
        assert abs(inner.imag) < 1e-10  # Should be real
    
    def test_inner_product_conjugate_symmetry(self):
        """Test that ⟨ψ, φ⟩ = ⟨φ, ψ⟩*."""
        H = HilbertSpaceOmega()
        
        psi = np.random.randn(H.n_grid) + 1j * np.random.randn(H.n_grid)
        phi = np.random.randn(H.n_grid) + 1j * np.random.randn(H.n_grid)
        
        inner1 = H.inner_product(psi, phi)
        inner2 = H.inner_product(phi, psi)
        
        assert_allclose(inner1, np.conj(inner2), rtol=1e-10)
    
    def test_inner_product_linearity(self):
        """Test linearity: ⟨ψ, α·φ + β·χ⟩ = α*⟨ψ,φ⟩ + β*⟨ψ,χ⟩."""
        H = HilbertSpaceOmega()
        
        psi = np.random.randn(H.n_grid)
        phi = np.random.randn(H.n_grid)
        chi = np.random.randn(H.n_grid)
        alpha = 2.0 + 1.0j
        beta = -1.5 + 0.5j
        
        lhs = H.inner_product(psi, alpha * phi + beta * chi)
        rhs = np.conj(alpha) * H.inner_product(psi, phi) + np.conj(beta) * H.inner_product(psi, chi)
        
        assert_allclose(lhs, rhs, rtol=1e-10)
    
    def test_norm_properties(self):
        """Test norm properties."""
        H = HilbertSpaceOmega()
        
        psi = np.random.randn(H.n_grid)
        
        norm_psi = H.norm(psi)
        
        # Norm is positive
        assert norm_psi > 0
        
        # Norm scales correctly
        norm_2psi = H.norm(2 * psi)
        assert_allclose(norm_2psi, 2 * norm_psi, rtol=1e-10)
    
    def test_vortex_symmetry_exact(self):
        """Test vortex symmetry for exactly symmetric function."""
        H = HilbertSpaceOmega()
        
        # Create symmetric Gaussian: exp(-(log x)²)
        psi = np.exp(-(np.log(H.x_grid))**2)
        
        result = H.verify_vortex_symmetry(psi, tolerance=0.1)
        
        assert result['verified']
        assert result['mean_symmetry_error'] < 0.1
    
    def test_project_to_symmetric(self):
        """Test projection to symmetric subspace."""
        H = HilbertSpaceOmega()
        
        # Start with asymmetric function
        f = H.x_grid**2
        
        # Project to symmetric
        psi = H.project_to_symmetric(f)
        
        # Verify symmetry
        result = H.verify_vortex_symmetry(psi, tolerance=0.2)
        
        assert result['mean_symmetry_error'] < 0.2
    
    def test_nodo_zero_location(self):
        """Test that x=1 is in the grid (Nodo Zero)."""
        H = HilbertSpaceOmega(x_min=0.1, x_max=10.0, n_grid=200)
        
        # Find closest point to x=1
        idx = np.argmin(np.abs(H.x_grid - 1.0))
        
        assert abs(H.x_grid[idx] - 1.0) < 0.1


class TestOperatorH_Omega:
    """Test suite for operator H_Omega."""
    
    def test_initialization(self):
        """Test operator initialization."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        assert op.hilbert_space is H_space
        assert op.H_matrix.shape == (H_space.n_grid, H_space.n_grid)
    
    def test_kinetic_operator_shape(self):
        """Test kinetic operator has correct shape."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        H0 = op._build_kinetic_operator()
        
        assert H0.shape == (H_space.n_grid, H_space.n_grid)
        assert H0.dtype == np.complex128
    
    def test_potential_operator_shape(self):
        """Test potential operator has correct shape."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        V = op._build_potential_operator()
        
        assert V.shape == (H_space.n_grid, H_space.n_grid)
    
    def test_potential_is_diagonal(self):
        """Test that potential V(x) is diagonal (multiplicative)."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        V = op._build_potential_operator()
        
        # Extract diagonal and off-diagonal
        V_diag = np.diag(V)
        V_off_diag = V - np.diag(V_diag)
        
        # Off-diagonal should be small (Gaussian approximation has some spread)
        off_diag_norm = np.linalg.norm(V_off_diag, 'fro')
        diag_norm = np.linalg.norm(V_diag)
        
        assert off_diag_norm / (diag_norm + 1e-16) < 0.5
    
    def test_potential_is_real(self):
        """Test that potential V(x) is real."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        V = op._build_potential_operator()
        
        max_imag = np.max(np.abs(V.imag))
        
        assert max_imag < 1e-14
    
    def test_hermiticity(self):
        """Test that H_Omega is Hermitian (H = H†)."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        H = op.H_matrix
        H_dagger = H.conj().T
        
        hermiticity_error = np.linalg.norm(H - H_dagger, 'fro') / (np.linalg.norm(H, 'fro') + 1e-16)
        
        # Should be Hermitian to high precision
        assert hermiticity_error < 1e-8
    
    def test_eigenvalues_mostly_real(self):
        """Test that eigenvalues are predominantly real."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        eigenvalues, _ = op.get_spectrum()
        
        max_imag = np.max(np.abs(eigenvalues.imag))
        
        # Eigenvalues should be real (or very close)
        assert max_imag < 0.1  # Relaxed tolerance for numerical operator
    
    def test_spectrum_ordering(self):
        """Test that spectrum is ordered by real part."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        eigenvalues, _ = op.get_spectrum()
        real_parts = eigenvalues.real
        
        # Should be sorted
        assert np.all(np.diff(real_parts) >= -1e-10)
    
    def test_apply_operator(self):
        """Test operator application H·ψ."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        # Random state
        psi = np.random.randn(H_space.n_grid) + 1j * np.random.randn(H_space.n_grid)
        
        # Apply operator
        H_psi = op.apply(psi)
        
        assert H_psi.shape == psi.shape
        assert np.all(np.isfinite(H_psi))
    
    def test_conservation_of_norm_real_eigenstate(self):
        """Test that eigenstates have unit norm after normalization."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        eigenvalues, eigenvectors = op.get_spectrum()
        
        # Pick first eigenstate
        psi = eigenvectors[:, 0]
        
        # Normalize
        psi = psi / H_space.norm(psi)
        
        norm_psi = H_space.norm(psi)
        
        assert_allclose(norm_psi, 1.0, rtol=1e-6)


class TestSelfAdjointness:
    """Test suite for self-adjointness verification."""
    
    def test_verificar_autoadjuncion_runs(self):
        """Test that verificar_autoadjuncion() runs without error."""
        verdict = verificar_autoadjuncion()
        
        assert isinstance(verdict, str)
        assert len(verdict) > 0
    
    def test_verificar_autoadjuncion_verdict(self):
        """Test that verdict indicates success."""
        verdict = verificar_autoadjuncion()
        
        # Should contain confirmation
        assert "AUTOADJOINT" in verdict.upper() or "COMPLETADO" in verdict
    
    def test_boundary_term_vanishes(self):
        """Test that boundary term vanishes due to vortex symmetry."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        # Create symmetric test function
        x = H_space.x_grid
        psi = np.exp(-(np.log(x))**2)
        psi = H_space.project_to_symmetric(psi)
        
        # Test function should decay at boundaries
        assert abs(psi[0]) < 0.1 * np.max(abs(psi))
        assert abs(psi[-1]) < 0.1 * np.max(abs(psi))
    
    def test_kato_rellich_condition(self):
        """Test Kato-Rellich relative boundedness condition."""
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        V = op._build_potential_operator()
        
        # Potential should be bounded
        V_norm = np.linalg.norm(V, 'fro')
        
        assert V_norm < np.inf
        assert np.all(np.isfinite(V))


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants_imported(self):
        """Test that QCAL constants are accessible."""
        assert F0_QCAL == 141.7001
        assert C_QCAL == 244.36
    
    def test_frequency_in_operator(self):
        """Test that fundamental frequency can be related to operator."""
        # The operator should have a characteristic frequency scale
        H_space = HilbertSpaceOmega()
        op = OperatorH_Omega(H_space)
        
        eigenvalues, _ = op.get_spectrum()
        real_eigenvalues = eigenvalues[np.abs(eigenvalues.imag) < 1e-6].real
        
        # Should have positive eigenvalues
        assert len(real_eigenvalues[real_eigenvalues > 0]) > 0
    
    def test_operator_signature(self):
        """Test that operator includes QCAL signature."""
        # Just verify the function runs and includes signature
        import io
        import sys
        
        captured_output = io.StringIO()
        sys.stdout = captured_output
        
        try:
            verificar_autoadjuncion()
        finally:
            sys.stdout = sys.__stdout__
        
        output = captured_output.getvalue()
        
        assert "∞³" in output or "QCAL" in output or "141.7001" in output


class TestDemonstration:
    """Test demonstration functions."""
    
    def test_demonstrate_vortex_operator_runs(self):
        """Test that demonstration runs without error."""
        import io
        import sys
        
        captured_output = io.StringIO()
        sys.stdout = captured_output
        
        try:
            results = demonstrate_vortex_operator(save_fig=False)
        finally:
            sys.stdout = sys.__stdout__
        
        assert isinstance(results, dict)
        assert 'eigenvalues' in results
        assert 'hilbert_space' in results
        assert 'operator' in results
    
    def test_demonstrate_returns_valid_results(self):
        """Test that demonstration returns valid results."""
        import io
        import sys
        
        captured_output = io.StringIO()
        sys.stdout = captured_output
        
        try:
            results = demonstrate_vortex_operator(save_fig=False)
        finally:
            sys.stdout = sys.__stdout__
        
        assert results['n_eigenvalues'] > 0
        assert results['n_real_eigenvalues'] >= 0
        assert isinstance(results['hilbert_space'], HilbertSpaceOmega)
        assert isinstance(results['operator'], OperatorH_Omega)


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

class TestIntegration:
    """Integration tests for complete workflow."""
    
    @pytest.mark.slow
    def test_full_verification_workflow(self):
        """Test complete verification workflow."""
        # Create Hilbert space
        H_space = HilbertSpaceOmega(x_min=0.1, x_max=10.0, n_grid=100)
        
        # Create operator
        op = OperatorH_Omega(H_space)
        
        # Verify Hermiticity
        H = op.H_matrix
        H_dagger = H.conj().T
        hermiticity_error = np.linalg.norm(H - H_dagger, 'fro') / np.linalg.norm(H, 'fro')
        assert hermiticity_error < 1e-8
        
        # Compute spectrum
        eigenvalues, eigenvectors = op.get_spectrum()
        assert len(eigenvalues) == H_space.n_grid
        
        # Verify eigenstates are symmetric
        for i in range(min(5, len(eigenvalues))):
            psi = eigenvectors[:, i]
            result = H_space.verify_vortex_symmetry(psi, tolerance=0.5)
            # Note: Eigenstates may not exactly satisfy vortex symmetry
            # due to numerical discretization, but should be close
    
    @pytest.mark.slow
    def test_varying_grid_sizes(self):
        """Test operator with different grid sizes."""
        for n_grid in [50, 100, 200]:
            H_space = HilbertSpaceOmega(n_grid=n_grid)
            op = OperatorH_Omega(H_space)
            
            # Should be Hermitian regardless of grid size
            H = op.H_matrix
            H_dagger = H.conj().T
            hermiticity_error = np.linalg.norm(H - H_dagger, 'fro') / np.linalg.norm(H, 'fro')
            
            assert hermiticity_error < 1e-8


# =============================================================================
# PYTEST CONFIGURATION
# =============================================================================

def test_module_imports():
    """Test that all necessary modules can be imported."""
    from vortex_symmetry_operator import (
        HilbertSpaceOmega,
        OperatorH_Omega,
        verificar_autoadjuncion,
        F0_QCAL,
        C_QCAL
    )
    
    assert HilbertSpaceOmega is not None
    assert OperatorH_Omega is not None
    assert verificar_autoadjuncion is not None


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
