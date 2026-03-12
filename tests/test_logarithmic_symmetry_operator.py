"""
Tests for Logarithmic Symmetry Operator
========================================

Comprehensive test suite for the logarithmic symmetry operator with
u ↔ -u central node and connection to Ξ(t) = Ξ(-t).

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(repo_root))

from operators.logarithmic_symmetry_operator import (
    LogarithmicSymmetryOperator,
    SymmetryResult,
    LogarithmicFlowResult,
    verify_xi_symmetry,
    demonstrate_symmetry_connection,
    F0_QCAL, C_COHERENCE, PHI
)


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_value(self):
        """Verify master frequency."""
        assert abs(F0_QCAL - 141.7001) < 1e-6
    
    def test_coherence_constant(self):
        """Verify coherence constant."""
        assert abs(C_COHERENCE - 244.36) < 1e-2
    
    def test_phi_value(self):
        """Verify golden ratio."""
        assert abs(PHI - 1.618033988749895) < 1e-12


class TestOperatorInitialization:
    """Test operator initialization."""
    
    def test_default_initialization(self):
        """Test default parameters."""
        op = LogarithmicSymmetryOperator()
        
        assert op.n == 512
        assert op.u_max == 10.0
        assert len(op.u_grid) == 512
    
    def test_custom_dimensions(self):
        """Test custom dimensions."""
        op = LogarithmicSymmetryOperator(n_dim=256, u_max=5.0)
        
        assert op.n == 256
        assert op.u_max == 5.0
        assert len(op.u_grid) == 256
    
    def test_even_dimension_enforcement(self):
        """Test that odd dimensions are made even for symmetry."""
        op = LogarithmicSymmetryOperator(n_dim=255)
        
        # Should be rounded up to 256
        assert op.n % 2 == 0
        assert op.n >= 255
    
    def test_grid_symmetry(self):
        """Test grid is symmetric around zero."""
        op = LogarithmicSymmetryOperator(n_dim=100, u_max=10.0)
        
        # First and last should be symmetric
        assert abs(op.u_grid[0] + op.u_grid[-1]) < 1e-10
        
        # Middle should be near zero
        mid = op.n // 2
        assert abs(op.u_grid[mid-1] + op.u_grid[mid]) < 0.5


class TestLogarithmicPotential:
    """Test logarithmic potential."""
    
    def test_potential_symmetry(self):
        """Test V(u) = V(-u)."""
        op = LogarithmicSymmetryOperator(n_dim=100, u_max=8.0)
        
        V = op.logarithmic_potential(op.u_grid)
        
        n = op.n
        for i in range(n // 2):
            # V[i] should equal V[n-1-i] (u and -u)
            assert abs(V[i] - V[n-1-i]) < 1e-12
    
    def test_potential_at_zero(self):
        """Test potential is finite at u=0."""
        op = LogarithmicSymmetryOperator()
        
        V_zero = op.logarithmic_potential(np.array([0.0]))
        
        assert np.isfinite(V_zero[0])
        assert V_zero[0] == 0.0  # log(1) = 0
    
    def test_potential_monotonicity(self):
        """Test potential increases with |u|."""
        op = LogarithmicSymmetryOperator()
        
        u_test = np.array([0.0, 1.0, 2.0, 3.0])
        V = op.logarithmic_potential(u_test)
        
        # Should be monotonically increasing
        for i in range(len(V) - 1):
            assert V[i+1] > V[i]


class TestHamiltonianConstruction:
    """Test Hamiltonian construction."""
    
    def test_hamiltonian_hermiticity(self):
        """Test H = H†."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        H = op.construct_hamiltonian()
        
        hermiticity_error = np.max(np.abs(H - H.conj().T))
        assert hermiticity_error < 1e-12
    
    def test_hamiltonian_shape(self):
        """Test Hamiltonian has correct shape."""
        op = LogarithmicSymmetryOperator(n_dim=128)
        
        H = op.construct_hamiltonian()
        
        assert H.shape == (128, 128)
    
    def test_hamiltonian_finite(self):
        """Test all Hamiltonian elements are finite."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        H = op.construct_hamiltonian()
        
        assert np.all(np.isfinite(H))


class TestUSymmetry:
    """Test u ↔ -u symmetry."""
    
    def test_verify_u_symmetry_perfect(self):
        """Test u symmetry verification returns small error."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        H = op.construct_hamiltonian()
        u_error = op.verify_u_symmetry(H)
        
        # Should be very small (numerical precision)
        assert u_error < 1e-10
    
    def test_u_symmetry_structure(self):
        """Test structural u ↔ -u symmetry."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        H = op.construct_hamiltonian()
        n = op.n
        
        # Check specific elements for symmetry
        # H[i,j] should relate to H[n-1-i, n-1-j]
        for i in range(n // 4):
            for j in range(n // 4):
                val1 = H[i, j]
                val2 = H[n-1-i, n-1-j]
                assert abs(val1 - val2) < 1e-10


class TestSpectrum:
    """Test spectrum computation."""
    
    def test_eigenvalues_real(self):
        """Test eigenvalues are real (Hermitian operator)."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        spec = op.compute_spectrum()
        
        # Eigenvalues of Hermitian should be real
        reality_error = spec['eigenvalue_reality']
        assert reality_error < 1e-10
    
    def test_eigenvalues_ordered(self):
        """Test eigenvalues are ordered."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        spec = op.compute_spectrum()
        eigenvalues = spec['eigenvalues']
        
        # eigh returns sorted eigenvalues
        assert np.all(eigenvalues[:-1] <= eigenvalues[1:])
    
    def test_eigenvectors_orthonormal(self):
        """Test eigenvectors are orthonormal."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        spec = op.compute_spectrum()
        V = spec['eigenvectors']
        
        # Check orthonormality: V†V = I
        identity = V.conj().T @ V
        identity_error = np.max(np.abs(identity - np.eye(64)))
        
        assert identity_error < 1e-10


class TestSymmetryVerification:
    """Test comprehensive symmetry verification."""
    
    def test_verify_symmetry_returns_result(self):
        """Test symmetry verification returns SymmetryResult."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        result = op.verify_symmetry()
        
        assert isinstance(result, SymmetryResult)
        assert 0.0 <= result.psi <= 1.0
    
    def test_symmetry_psi_high(self):
        """Test coherence Ψ is high (near 1)."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        result = op.verify_symmetry()
        
        # Should be very close to 1 for perfect symmetry
        assert result.psi > 0.95
    
    def test_symmetry_errors_small(self):
        """Test all symmetry errors are small."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        result = op.verify_symmetry()
        
        assert result.u_symmetry_error < 1e-8
        assert result.hermiticity_error < 1e-10
        assert result.eigenvalue_reality < 1e-10
    
    def test_symmetry_parameters_stored(self):
        """Test parameters are stored in result."""
        op = LogarithmicSymmetryOperator(n_dim=64, u_max=8.0)
        
        result = op.verify_symmetry()
        
        assert result.parameters['n_dim'] == 64
        assert result.parameters['u_max'] == 8.0
        assert 'f0' in result.parameters


class TestLogarithmicFlow:
    """Test logarithmic flow computation."""
    
    def test_flow_computation(self):
        """Test flow can be computed."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        psi_t = op.logarithmic_flow(t=0.5)
        
        assert len(psi_t) == 64
        assert np.all(np.isfinite(psi_t))
    
    def test_flow_normalized(self):
        """Test flow state is approximately normalized."""
        op = LogarithmicSymmetryOperator(n_dim=128)
        
        psi_t = op.logarithmic_flow(t=0.5)
        
        # Compute norm
        norm = np.sqrt(np.sum(np.abs(psi_t)**2) * op.du)
        
        # Should be close to 1
        assert 0.8 < norm < 1.2
    
    def test_flow_at_t_zero(self):
        """Test flow at t=0 is initial state."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        psi_0 = op.logarithmic_flow(t=0.0)
        
        # Should look like Gaussian
        assert np.max(np.abs(psi_0)) > 0
        assert np.all(np.isfinite(psi_0))


class TestFlowSymmetry:
    """Test flow symmetry verification."""
    
    def test_verify_flow_symmetry_returns_result(self):
        """Test flow symmetry returns LogarithmicFlowResult."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        result = op.verify_flow_symmetry(t=0.5)
        
        assert isinstance(result, LogarithmicFlowResult)
        assert 0.0 <= result.psi <= 1.0
    
    def test_flow_symmetry_high(self):
        """Test flow preserves symmetry (Ψ near 1)."""
        op = LogarithmicSymmetryOperator(n_dim=128)
        
        result = op.verify_flow_symmetry(t=0.5)
        
        # Flow should preserve symmetry
        assert result.flow_symmetry > 0.8
    
    def test_central_node_nonzero(self):
        """Test central node has nonzero value."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        result = op.verify_flow_symmetry(t=0.5)
        
        # Should have amplitude at center
        assert result.central_node_value > 0


class TestXiSymmetry:
    """Test Xi function symmetry verification."""
    
    def test_verify_xi_symmetric_function(self):
        """Test verification for symmetric Xi function."""
        t_grid = np.linspace(-5, 5, 100)
        # Create symmetric function
        xi = np.exp(-t_grid**2 / 2)
        
        result = verify_xi_symmetry(xi, t_grid)
        
        assert result['symmetric_grid'] is True
        assert result['psi'] > 0.95
    
    def test_verify_xi_asymmetric_function(self):
        """Test verification detects asymmetry."""
        t_grid = np.linspace(-5, 5, 100)
        # Create asymmetric function
        xi = np.exp(-t_grid**2 / 2) * (1 + 0.5 * t_grid)
        
        result = verify_xi_symmetry(xi, t_grid)
        
        # Should detect asymmetry
        assert result['psi'] < 0.9
    
    def test_verify_xi_asymmetric_grid(self):
        """Test detection of asymmetric grid."""
        t_grid = np.linspace(-5, 6, 100)  # Asymmetric
        xi = np.exp(-t_grid**2 / 2)
        
        result = verify_xi_symmetry(xi, t_grid)
        
        assert result['symmetric_grid'] is False


class TestSymmetryConnection:
    """Test connection demonstration."""
    
    def test_demonstrate_symmetry_connection_runs(self):
        """Test demonstration runs without errors."""
        result = demonstrate_symmetry_connection()
        
        assert 'operator_symmetry' in result
        assert 'flow_symmetry' in result
        assert 'xi_symmetry' in result
        assert 'connection_verified' in result
    
    def test_connection_high_coherence(self):
        """Test demonstration shows high coherence."""
        result = demonstrate_symmetry_connection()
        
        # All components should have high Ψ
        assert result['operator_symmetry'].psi > 0.9
        assert result['flow_symmetry'].psi > 0.8
        assert result['xi_symmetry']['psi'] > 0.9
    
    def test_connection_verified(self):
        """Test connection is verified."""
        result = demonstrate_symmetry_connection()
        
        # Overall connection should be verified
        assert result['connection_verified'] is True


class TestIntegration:
    """Integration tests."""
    
    def test_full_workflow(self):
        """Test complete workflow."""
        # Create operator
        op = LogarithmicSymmetryOperator(n_dim=64, u_max=8.0)
        
        # Verify symmetry
        sym_result = op.verify_symmetry()
        assert sym_result.psi > 0.9
        
        # Compute spectrum
        spec = op.compute_spectrum()
        assert len(spec['eigenvalues']) == 64
        
        # Verify flow
        flow_result = op.verify_flow_symmetry(t=1.0)
        assert flow_result.psi > 0.7
    
    def test_scaling_with_dimension(self):
        """Test operator works with different dimensions."""
        for n in [32, 64, 128]:
            op = LogarithmicSymmetryOperator(n_dim=n)
            result = op.verify_symmetry()
            
            # Should maintain high coherence
            assert result.psi > 0.9
    
    def test_different_u_ranges(self):
        """Test operator works with different u ranges."""
        for u_max in [5.0, 10.0, 15.0]:
            op = LogarithmicSymmetryOperator(n_dim=64, u_max=u_max)
            result = op.verify_symmetry()
            
            # Should maintain symmetry
            assert result.psi > 0.9


class TestDataclasses:
    """Test result dataclasses."""
    
    def test_symmetry_result_fields(self):
        """Test SymmetryResult has required fields."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        result = op.verify_symmetry()
        
        assert hasattr(result, 'psi')
        assert hasattr(result, 'u_symmetry_error')
        assert hasattr(result, 'hermiticity_error')
        assert hasattr(result, 'eigenvalue_reality')
        assert hasattr(result, 'timestamp')
        assert hasattr(result, 'computation_time_ms')
        assert hasattr(result, 'parameters')
    
    def test_flow_result_fields(self):
        """Test LogarithmicFlowResult has required fields."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        result = op.verify_flow_symmetry()
        
        assert hasattr(result, 'psi')
        assert hasattr(result, 'flow_symmetry')
        assert hasattr(result, 'central_node_value')
        assert hasattr(result, 'eigenvalues')
        assert hasattr(result, 'timestamp')
        assert hasattr(result, 'computation_time_ms')
        assert hasattr(result, 'parameters')
    
    def test_psi_field_in_range(self):
        """Test psi field is always in [0, 1]."""
        op = LogarithmicSymmetryOperator(n_dim=64)
        
        sym_result = op.verify_symmetry()
        flow_result = op.verify_flow_symmetry()
        
        assert 0.0 <= sym_result.psi <= 1.0
        assert 0.0 <= flow_result.psi <= 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
