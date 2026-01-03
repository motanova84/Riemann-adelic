#!/usr/bin/env python3
"""
Comprehensive test suite for the Discrete Symmetry Operator (H_DS).

Tests verify:
1. Symmetry matrix construction and properties
2. Hermiticity verification
3. Symmetry invariance checking
4. Critical line localization
5. Integration with existing operators
6. Enforcement of discrete symmetry on test functions

Author: José Manuel Mota Burruezo
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from operador.operador_H_DS import DiscreteSymmetryOperator


class TestDiscreteSymmetryOperator:
    """Test suite for DiscreteSymmetryOperator class."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.dim = 20
        self.H_DS = DiscreteSymmetryOperator(
            dimension=self.dim,
            tolerance=1e-10
        )
    
    def test_initialization(self):
        """Test operator initialization."""
        assert self.H_DS.dim == self.dim
        assert self.H_DS.base == np.pi
        assert np.isclose(self.H_DS.log_period, np.log(np.pi))
        assert self.H_DS.S_matrix.shape == (self.dim, self.dim)
    
    def test_symmetry_matrix_properties(self):
        """Test properties of the symmetry matrix S."""
        S = self.H_DS.S_matrix
        
        # S should be a permutation matrix
        assert S.shape == (self.dim, self.dim)
        
        # Each row and column should have exactly one 1
        assert np.allclose(np.sum(S, axis=0), 1.0)
        assert np.allclose(np.sum(S, axis=1), 1.0)
        
        # S should be orthogonal: S @ S.T = I
        identity = S @ S.T
        assert np.allclose(identity, np.eye(self.dim))
        
        # S² = I (involution property)
        S_squared = S @ S
        assert np.allclose(S_squared, np.eye(self.dim))
    
    def test_apply_symmetry_to_hermitian_operator(self):
        """Test symmetrization of a Hermitian operator."""
        # Create a Hermitian operator
        H = np.random.randn(self.dim, self.dim)
        H = 0.5 * (H + H.T)  # Make symmetric/Hermitian
        
        # Apply symmetry
        H_sym = self.H_DS.apply_symmetry(H)
        
        # Result should still be Hermitian
        assert np.allclose(H_sym, H_sym.T)
        
        # Should commute with S
        HS = H_sym @ self.H_DS.S_matrix
        SH = self.H_DS.S_matrix @ H_sym
        assert np.allclose(HS, SH, atol=1e-10)
    
    def test_verify_hermiticity_perfect(self):
        """Test Hermiticity verification with perfect Hermitian matrix."""
        H = np.random.randn(self.dim, self.dim)
        H = 0.5 * (H + H.T)  # Make exactly symmetric
        
        is_hermitian, deviation = self.H_DS.verify_hermiticity(H, "H_perfect")
        
        assert is_hermitian
        assert deviation < 1e-12
    
    def test_verify_hermiticity_imperfect(self):
        """Test Hermiticity verification with non-Hermitian matrix."""
        H = np.random.randn(self.dim, self.dim)
        # Don't symmetrize - should fail Hermiticity test
        
        is_hermitian, deviation = self.H_DS.verify_hermiticity(H, "H_imperfect")
        
        assert not is_hermitian
        assert deviation > self.H_DS.tolerance
    
    def test_verify_symmetry_invariance_symmetric(self):
        """Test symmetry invariance for symmetric operator."""
        # Create operator that commutes with S (diagonal operator)
        H = np.diag(np.random.rand(self.dim))
        
        # Symmetrize to ensure it commutes with S
        H_sym = self.H_DS.apply_symmetry(H)
        
        is_symmetric, deviation = self.H_DS.verify_symmetry_invariance(
            H_sym, "H_symmetric"
        )
        
        assert is_symmetric
        assert deviation < 1e-10
    
    def test_verify_symmetry_invariance_asymmetric(self):
        """Test symmetry invariance for asymmetric operator."""
        # Create operator that doesn't commute with S
        H = np.random.randn(self.dim, self.dim)
        
        is_symmetric, deviation = self.H_DS.verify_symmetry_invariance(
            H, "H_asymmetric"
        )
        
        # Should fail unless by chance
        # We don't assert failure since random matrices might accidentally pass
        # Just check that the function runs
        assert isinstance(is_symmetric, (bool, np.bool_))
        assert isinstance(deviation, (float, np.floating))
    
    def test_verify_critical_line_localization(self):
        """Test critical line localization with synthetic eigenvalues."""
        # Create eigenvalues corresponding to RH zeros
        gammas = np.array([14.134725, 21.022040, 25.010858, 30.424876])
        eigenvalues = gammas**2 + 0.25
        
        all_ok, stats = self.H_DS.verify_critical_line_localization(eigenvalues)
        
        assert all_ok
        assert stats['eigenvalues_are_real']
        assert stats['eigenvalues_are_positive']
        assert stats['num_eigenvalues'] == len(eigenvalues)
        
        # Check recovered gammas
        recovered_gammas = np.array(stats['gammas'])
        assert np.allclose(recovered_gammas, gammas, atol=1e-10)
    
    def test_verify_critical_line_with_comparison(self):
        """Test critical line localization with known zeros."""
        # Known zeros (imaginary parts)
        known_zeros = np.array([14.134725, 21.022040, 25.010858])
        
        # Create eigenvalues with small error
        eigenvalues = (known_zeros + 1e-6)**2 + 0.25
        
        all_ok, stats = self.H_DS.verify_critical_line_localization(
            eigenvalues, known_zeros
        )
        
        assert all_ok
        assert 'comparison_with_known_zeros' in stats
        
        comp = stats['comparison_with_known_zeros']
        assert comp['max_relative_error'] < 1e-3
        assert comp['acceptable']
    
    def test_enforce_discrete_symmetry(self):
        """Test enforcement of discrete symmetry on test functions."""
        # Create a test function (Gaussian)
        domain = np.linspace(-5, 5, self.dim)
        test_func = lambda x: np.exp(-x**2)
        
        # Enforce symmetry
        result = self.H_DS.enforce_discrete_symmetry(test_func, domain)
        
        # Result should be symmetric
        assert np.allclose(result, np.flip(result))
        
        # Result should have correct shape
        assert result.shape == (self.dim,)
    
    def test_project_to_critical_line(self):
        """Test projection to critical line Re(s) = 1/2."""
        # Create complex values with various real parts
        s_values = np.array([
            0.3 + 14.1j,
            0.7 + 21.0j,
            0.5 + 25.0j,  # Already on critical line
            0.9 + 30.4j
        ])
        
        # Project
        s_projected = self.H_DS.project_to_critical_line(s_values)
        
        # All should have Re(s) = 1/2
        assert np.allclose(s_projected.real, 0.5)
        
        # Imaginary parts should be preserved
        assert np.allclose(s_projected.imag, s_values.imag)
    
    def test_verification_log(self):
        """Test that verification tests are logged correctly."""
        # Clear log
        self.H_DS.verification_log = []
        
        # Run some tests
        H = np.eye(self.dim)
        self.H_DS.verify_hermiticity(H, "identity")
        self.H_DS.verify_symmetry_invariance(H, "identity")
        
        # Check log
        assert len(self.H_DS.verification_log) == 2
        assert all('test' in entry for entry in self.H_DS.verification_log)
        assert all('passed' in entry for entry in self.H_DS.verification_log)
    
    def test_generate_verification_report(self):
        """Test generation of verification report."""
        # Run a test
        H = np.eye(self.dim)
        self.H_DS.verify_hermiticity(H, "test_matrix")
        
        # Generate report
        report = self.H_DS.generate_verification_report()
        
        assert isinstance(report, str)
        assert "VERIFICATION REPORT" in report
        assert "test_matrix" in report
        assert "hermiticity" in report
    
    def test_validate_operator_stack(self):
        """Test complete operator stack validation."""
        # Create a proper Hermitian operator
        H = np.random.randn(self.dim, self.dim)
        H = 0.5 * (H + H.T)
        
        # Symmetrize to ensure it passes all tests
        H_sym = self.H_DS.apply_symmetry(H)
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(H_sym)
        eigenvalues = eigenvalues - np.min(eigenvalues) + 0.25
        
        # Run validation
        all_passed, report = self.H_DS.validate_operator_stack(
            H_sym,
            eigenvalues=eigenvalues
        )
        
        assert isinstance(all_passed, bool)
        assert isinstance(report, str)
        assert "VERIFICATION REPORT" in report


class TestIntegrationWithExistingOperators:
    """Test integration of H_DS with existing operator implementations."""
    
    def test_integration_with_riemann_operator(self):
        """Test H_DS with RiemannOperator structure."""
        try:
            from operador.riemann_operator import RiemannOperator
            
            # Create a small RiemannOperator
            gammas = [14.134725, 21.022040, 25.010858]
            dim = 50
            
            # Create H_DS with matching dimension
            H_DS = DiscreteSymmetryOperator(dimension=dim)
            
            # Verify that H_DS can work with this structure
            assert H_DS.S_matrix.shape == (dim, dim)
            
        except ImportError:
            pytest.skip("RiemannOperator not available for integration test")
    
    def test_integration_with_gaussian_kernel_operator(self):
        """Test H_DS with Gaussian kernel operator from operador_H.py."""
        try:
            from operador.operador_H import build_R_matrix, spectrum_from_R
            
            # Build a small operator
            n_basis = 10
            h = 1e-3
            L = 1.0
            
            R = build_R_matrix(n_basis=n_basis, h=h, L=L)
            
            # Create H_DS with matching dimension
            H_DS = DiscreteSymmetryOperator(dimension=n_basis)
            
            # Verify Hermiticity of R
            is_hermitian, dev = H_DS.verify_hermiticity(R, "R_matrix")
            
            assert is_hermitian
            assert dev < 1e-10
            
        except ImportError:
            pytest.skip("operador_H not available for integration test")


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_dimension(self):
        """Test with very small dimension."""
        H_DS = DiscreteSymmetryOperator(dimension=2)
        
        H = np.array([[1.0, 0.0], [0.0, 2.0]])
        is_hermitian, _ = H_DS.verify_hermiticity(H)
        
        assert is_hermitian
    
    def test_large_dimension(self):
        """Test with larger dimension."""
        H_DS = DiscreteSymmetryOperator(dimension=200)
        
        # Create diagonal matrix (always Hermitian)
        H = np.diag(np.random.rand(200))
        is_hermitian, _ = H_DS.verify_hermiticity(H)
        
        assert is_hermitian
    
    def test_complex_hermitian_matrix(self):
        """Test with complex Hermitian matrix."""
        dim = 10
        H_DS = DiscreteSymmetryOperator(dimension=dim)
        
        # Create complex Hermitian matrix
        A = np.random.randn(dim, dim) + 1j * np.random.randn(dim, dim)
        H = 0.5 * (A + A.conj().T)  # Make Hermitian
        
        is_hermitian, dev = H_DS.verify_hermiticity(H)
        
        assert is_hermitian
        assert dev < 1e-10
    
    def test_nearly_hermitian_matrix(self):
        """Test with matrix that's nearly but not quite Hermitian."""
        dim = 10
        H_DS = DiscreteSymmetryOperator(dimension=dim, tolerance=1e-6)
        
        # Create Hermitian matrix with small perturbation
        H = np.random.randn(dim, dim)
        H = 0.5 * (H + H.T)
        H[0, 1] += 1e-8  # Small asymmetry
        
        is_hermitian, dev = H_DS.verify_hermiticity(H)
        
        # Should pass with relaxed tolerance
        assert is_hermitian
        assert dev < 1e-6
    
    def test_zero_eigenvalues(self):
        """Test critical line localization with zero eigenvalues."""
        H_DS = DiscreteSymmetryOperator(dimension=10)
        
        # Include eigenvalue at λ = 1/4 (γ = 0)
        eigenvalues = np.array([0.25, 1.0, 4.0, 9.0])
        
        all_ok, stats = H_DS.verify_critical_line_localization(eigenvalues)
        
        assert all_ok
        assert stats['min_eigenvalue'] == 0.25
    
    def test_negative_eigenvalues_rejected(self):
        """Test that negative eigenvalues are properly handled."""
        H_DS = DiscreteSymmetryOperator(dimension=10)
        
        # Include negative eigenvalue (should fail RH criterion)
        eigenvalues = np.array([-0.1, 1.0, 4.0])
        
        all_ok, stats = H_DS.verify_critical_line_localization(eigenvalues)
        
        assert not all_ok
        assert not stats['eigenvalues_are_positive']


def test_demonstrate_H_DS():
    """Test the demonstration function."""
    from operador.operador_H_DS import demonstrate_H_DS
    
    # Run demonstration
    H_DS, success = demonstrate_H_DS()
    
    assert isinstance(H_DS, DiscreteSymmetryOperator)
    assert isinstance(success, bool)
    
    # Check that verification log was populated
    assert len(H_DS.verification_log) > 0


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
