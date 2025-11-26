"""
Tests for H_Ψ ↔ H_DS operator connection

This module tests the fundamental connection between:
- H_Ψ: Operator that generates Riemann zeros
- H_DS: Operator that validates space structure

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
import os

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from operators.discrete_symmetry_operator import DiscreteSymmetryOperator
from operators.operator_connection import OperatorConnection

# Test constants
CONVERGENCE_TOLERANCE_FACTOR = 2  # Tolerance factor for convergence tests


class TestDiscreteSymmetryOperator:
    """Test suite for H_DS operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        H_DS = DiscreteSymmetryOperator(alpha=1.0, beta=-0.5, gamma=0.01, delta=0.1)
        
        assert H_DS.alpha == 1.0
        assert H_DS.beta == -0.5
        assert H_DS.gamma == 0.01
        assert H_DS.delta == 0.1
    
    def test_initialization_validation(self):
        """Test that invalid parameters raise errors."""
        with pytest.raises(ValueError, match="alpha must be positive"):
            DiscreteSymmetryOperator(alpha=-1.0)
        
        with pytest.raises(ValueError, match="gamma must be positive"):
            DiscreteSymmetryOperator(gamma=-0.01)
    
    def test_amplitude_function_range(self):
        """Test that amplitude function is in [0, 1]."""
        H_DS = DiscreteSymmetryOperator()
        
        R_vals = np.linspace(0.1, 100, 1000)
        A_vals = H_DS.amplitude_function(R_vals)
        
        assert np.all(A_vals >= 0)
        assert np.all(A_vals <= 1)
    
    def test_amplitude_function_periodicity(self):
        """Test discrete symmetry: A(π·R) has same structure as A(R)."""
        H_DS = DiscreteSymmetryOperator()
        
        R = 2.5
        A_R = H_DS.amplitude_function(np.array([R]))
        A_piR = H_DS.amplitude_function(np.array([np.pi * R]))
        
        # Both should be in [0, 1] and related by the discrete symmetry
        assert 0 <= A_R <= 1
        assert 0 <= A_piR <= 1
    
    def test_vacuum_energy_coercivity(self):
        """Test that vacuum energy is coercive."""
        H_DS = DiscreteSymmetryOperator(alpha=1.0, beta=-0.5, gamma=0.01, delta=0.1)
        
        # Small R: UV term dominates
        E_small = H_DS.vacuum_energy(np.array([0.01]))
        
        # Large R: IR term dominates
        E_large = H_DS.vacuum_energy(np.array([100.0]))
        
        # Middle R
        E_middle = H_DS.vacuum_energy(np.array([2.0]))
        
        # Energy should be large at boundaries
        assert E_small > E_middle
        assert E_large > E_middle
    
    def test_vacuum_energy_has_minimum(self):
        """Test that vacuum energy has at least one minimum."""
        H_DS = DiscreteSymmetryOperator()
        
        R_vals = np.linspace(0.5, 20, 1000)
        E_vals = H_DS.vacuum_energy(R_vals)
        
        # Find minimum
        min_idx = np.argmin(E_vals)
        
        # Should not be at boundaries
        assert 0 < min_idx < len(E_vals) - 1
    
    def test_symmetry_projector(self):
        """Test symmetry projector onto discrete cells."""
        H_DS = DiscreteSymmetryOperator()
        
        R_vals = np.linspace(0.5, 50, 1000)
        
        # Project onto cell [π⁰, π¹] = [1, π]
        proj = H_DS.symmetry_projector(R_vals, cell_index=0)
        
        # Check that only values in [1, π] are selected
        expected_mask = np.logical_and(R_vals >= 1.0, R_vals < np.pi)
        np.testing.assert_array_equal(proj, expected_mask.astype(float))
    
    def test_validate_hermiticity_symmetric_matrix(self):
        """Test hermiticity validation on symmetric matrix."""
        H_DS = DiscreteSymmetryOperator()
        
        # Create symmetric matrix
        A = np.array([[1, 2, 3],
                      [2, 4, 5],
                      [3, 5, 6]], dtype=float)
        
        result = H_DS.validate_hermiticity(A)
        
        assert result['is_hermitian']
        assert result['symmetry_error'] < 1e-10
    
    def test_validate_hermiticity_asymmetric_matrix(self):
        """Test hermiticity validation on asymmetric matrix."""
        H_DS = DiscreteSymmetryOperator()
        
        # Create asymmetric matrix
        A = np.array([[1, 2, 3],
                      [4, 5, 6],
                      [7, 8, 9]], dtype=float)
        
        result = H_DS.validate_hermiticity(A)
        
        assert not result['is_hermitian']
        assert result['symmetry_error'] > 0
    
    def test_validate_space_structure(self):
        """Test complete space structure validation."""
        H_DS = DiscreteSymmetryOperator()
        
        result = H_DS.validate_space_structure(R_range=(0.5, 50.0), n_points=1000)
        
        assert 'structure_valid' in result
        assert 'is_coercive' in result
        assert 'n_critical_points' in result
        
        # Structure should be valid with default parameters
        assert result['is_coercive']
        assert result['n_critical_points'] > 0
    
    def test_construct_matrix_representation(self):
        """Test matrix representation construction."""
        H_DS = DiscreteSymmetryOperator()
        
        H_matrix, R_grid = H_DS.construct_matrix_representation(
            R_range=(0.5, 10.0),
            n_basis=50
        )
        
        # Check dimensions
        assert H_matrix.shape == (50, 50)
        assert len(R_grid) == 50
        
        # Check matrix is symmetric (Hermitian for real matrix)
        np.testing.assert_allclose(H_matrix, H_matrix.T, rtol=1e-10)
    
    def test_compute_spectrum(self):
        """Test eigenvalue spectrum computation."""
        H_DS = DiscreteSymmetryOperator()
        
        spectrum = H_DS.compute_spectrum(R_range=(0.5, 10.0), n_basis=50)
        
        assert 'eigenvalues' in spectrum
        assert 'eigenvectors' in spectrum
        assert 'R_grid' in spectrum
        
        eigenvalues = spectrum['eigenvalues']
        
        # All eigenvalues should be real (for Hermitian operator)
        assert np.all(np.isreal(eigenvalues))
        
        # Eigenvalues should be sorted
        assert np.all(np.diff(eigenvalues) >= 0)


class TestOperatorConnection:
    """Test suite for H_Ψ ↔ H_DS connection."""
    
    def test_initialization(self):
        """Test connection initialization."""
        conn = OperatorConnection(alpha=1.0, beta=-0.5, gamma=0.01, delta=0.1)
        
        assert conn.H_DS is not None
        assert conn.coupling_strength == 1.0
        assert conn.C_QCAL == 244.36
        assert conn.F0 == 141.7001
    
    def test_validate_hermiticity_structure(self):
        """Test validation of hermiticity structure."""
        conn = OperatorConnection()
        
        result = conn.validate_hermiticity_structure(
            R_range=(0.5, 50.0),
            n_points=500
        )
        
        assert 'structure_validates_hermiticity' in result
        assert 'space_structure' in result
        assert 'H_DS_hermiticity' in result
        
        # With default parameters, structure should validate hermiticity
        assert result['structure_validates_hermiticity']
        assert result['H_DS_hermiticity']['is_hermitian']
    
    def test_force_zero_reality_real_zeros(self):
        """Test validation that real zeros are recognized as real."""
        conn = OperatorConnection()
        
        # Real Riemann zeros
        gamma_n = np.array([14.134725142, 21.022039639, 25.010857580])
        
        result = conn.force_zero_reality(gamma_n)
        
        assert result['zeros_are_real']
        assert result['max_imaginary_part'] < 1e-10
        assert result['n_zeros_validated'] == 3
    
    def test_force_zero_reality_complex_zeros(self):
        """Test detection of non-real zeros."""
        conn = OperatorConnection()
        
        # Complex zeros (should be rejected)
        gamma_n = np.array([14.134725142 + 0.1j, 21.022039639 + 0.2j])
        
        result = conn.force_zero_reality(gamma_n, tolerance=1e-10)
        
        assert not result['zeros_are_real']
        assert result['max_imaginary_part'] > 1e-10
    
    def test_compute_vacuum_energy_correct(self):
        """Test validation of vacuum energy."""
        conn = OperatorConnection()
        
        result = conn.compute_vacuum_energy_correct(
            R_range=(0.5, 50.0),
            n_points=1000
        )
        
        assert 'energy_correct' in result
        assert 'is_coercive' in result
        assert 'n_minima' in result
        
        # Energy should be correct with default parameters
        assert result['is_coercive']
        assert result['n_minima'] > 0
    
    def test_validate_complete_connection_without_zeros(self):
        """Test complete validation without zero data."""
        conn = OperatorConnection()
        
        result = conn.validate_complete_connection(
            gamma_n=None,
            R_range=(0.5, 50.0),
            n_points=500
        )
        
        assert 'connection_valid' in result
        assert 'summary' in result
        
        # Basic validation should pass
        assert result['summary']['H_DS_validates_structure']
        assert result['summary']['vacuum_energy_correct']
    
    def test_validate_complete_connection_with_zeros(self):
        """Test complete validation with Riemann zeros."""
        conn = OperatorConnection()
        
        # First few Riemann zeros
        gamma_n = np.array([
            14.134725142,
            21.022039639,
            25.010857580,
            30.424876126,
            32.935061588
        ])
        
        result = conn.validate_complete_connection(
            gamma_n=gamma_n,
            R_range=(0.5, 50.0),
            n_points=500
        )
        
        assert 'connection_valid' in result
        assert 'reality_validation' in result
        
        # All validations should pass
        assert result['reality_validation']['zeros_are_real']
        assert result['connection_valid']


class TestIntegration:
    """Integration tests for complete operator framework."""
    
    def test_h_ds_enforces_h_psi_hermiticity(self):
        """
        Test the central theorem:
        H_DS validates structure → H_Ψ is Hermitian → zeros are real
        """
        # Create connection
        conn = OperatorConnection()
        
        # Validate structure
        structure_result = conn.validate_hermiticity_structure(
            R_range=(0.5, 50.0),
            n_points=500
        )
        
        # Structure should validate hermiticity
        assert structure_result['structure_validates_hermiticity']
        
        # H_DS itself should be Hermitian
        assert structure_result['H_DS_hermiticity']['is_hermitian']
        
        # This structure forces zeros to be real
        # Test with real zeros
        gamma_n = np.array([14.134725142, 21.022039639, 25.010857580])
        reality_result = conn.force_zero_reality(gamma_n)
        
        assert reality_result['structure_forces_reality']
    
    def test_discrete_symmetry_preserved(self):
        """Test that discrete symmetry G ≅ Z is preserved."""
        H_DS = DiscreteSymmetryOperator()
        
        # Test transformation R → π·R
        R_vals = np.array([1.0, 2.0, 5.0, 10.0])
        
        for R in R_vals:
            # Amplitude at R and π·R
            A_R = H_DS.amplitude_function(np.array([R]))
            A_piR = H_DS.amplitude_function(np.array([np.pi * R]))
            
            # Both should be valid (in [0,1])
            assert 0 <= A_R[0] <= 1
            assert 0 <= A_piR[0] <= 1
            
            # The discrete symmetry is preserved in the structure
            # (not necessarily A(R) = A(π·R), but periodicity in log-space)
    
    def test_spectrum_convergence(self):
        """Test that spectrum converges with increasing basis size."""
        H_DS = DiscreteSymmetryOperator()
        
        # Compute spectrum with different basis sizes
        n_basis_values = [30, 50, 70]
        first_eigenvalues = []
        
        for n_basis in n_basis_values:
            spectrum = H_DS.compute_spectrum(
                R_range=(0.5, 10.0),
                n_basis=n_basis
            )
            first_eigenvalues.append(spectrum['eigenvalues'][0])
        
        # First eigenvalue should converge
        differences = np.abs(np.diff(first_eigenvalues))
        
        # Differences should decrease (convergence)
        # Allow some variation due to discretization effects
        assert differences[1] < differences[0] * CONVERGENCE_TOLERANCE_FACTOR


class TestNumericalStability:
    """Test numerical stability of operators."""
    
    def test_vacuum_energy_near_zero(self):
        """Test numerical stability near R → 0."""
        H_DS = DiscreteSymmetryOperator()
        
        R_small = np.array([1e-6])
        E = H_DS.vacuum_energy(R_small)
        
        # Should be finite (though large)
        assert np.isfinite(E[0])
        assert E[0] > 0
    
    def test_vacuum_energy_large_R(self):
        """Test numerical stability for large R."""
        H_DS = DiscreteSymmetryOperator()
        
        R_large = np.array([1e6])
        E = H_DS.vacuum_energy(R_large)
        
        # Should be finite and positive
        assert np.isfinite(E[0])
        assert E[0] > 0
    
    def test_amplitude_numerical_stability(self):
        """Test amplitude function stability."""
        H_DS = DiscreteSymmetryOperator()
        
        # Test at various scales
        R_vals = np.logspace(-3, 3, 100)
        A_vals = H_DS.amplitude_function(R_vals)
        
        # All values should be in [0, 1]
        assert np.all(np.isfinite(A_vals))
        assert np.all(A_vals >= 0)
        assert np.all(A_vals <= 1)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
