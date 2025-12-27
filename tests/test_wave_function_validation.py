#!/usr/bin/env python3
"""
Tests for Wave Function Validation Module

Tests the dynamic and structural validation of wave functions ψn(x),
the eigenfunctions of the Hamiltonian H = -d²/dx² + V(x).

Author: José Manuel Mota Burruezo
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from wave_function_validation import (
    load_riemann_zeros,
    marchenko_potential,
    construct_hamiltonian,
    compute_eigenstates,
    verify_orthonormality,
    verify_localization,
    count_nodes,
    verify_node_theorem,
    expand_in_eigenbasis,
    reconstruct_from_coefficients,
    verify_expansion_convergence,
    create_delta_function,
    run_complete_validation,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE
)

# Test constants
NUMERICAL_TOLERANCE = 1e-10  # Tolerance for numerical comparisons
MIN_SYMMETRY_CORRELATION = 0.5  # Minimum correlation for approximate symmetry


class TestRiemannZerosLoading:
    """Tests for loading Riemann zeros."""
    
    def test_load_zeros_default(self):
        """Test loading default number of zeros."""
        zeros = load_riemann_zeros()
        assert len(zeros) == 30
        assert zeros[0] > 14  # First zero ≈ 14.13
        assert zeros[0] < 15
    
    def test_load_zeros_custom_count(self):
        """Test loading custom number of zeros."""
        zeros = load_riemann_zeros(n_zeros=10)
        assert len(zeros) == 10
    
    def test_zeros_are_sorted(self):
        """Test that zeros are sorted in ascending order."""
        zeros = load_riemann_zeros(n_zeros=30)
        for i in range(len(zeros) - 1):
            assert zeros[i] <= zeros[i + 1]
    
    def test_first_zeros_values(self):
        """Test that first few zeros have known values."""
        zeros = load_riemann_zeros(n_zeros=5)
        # First 5 Riemann zeros (imaginary parts)
        expected = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        for i, (z, e) in enumerate(zip(zeros, expected)):
            assert abs(z - e) < 0.001, f"Zero {i}: expected {e}, got {z}"


class TestMarchenkoPotential:
    """Tests for Marchenko potential reconstruction."""
    
    def test_potential_shape(self):
        """Test that potential has correct shape."""
        x = np.linspace(-10, 10, 100)
        gamma_n = np.array([14.1, 21.0, 25.0])
        V = marchenko_potential(x, gamma_n)
        assert V.shape == x.shape
    
    def test_potential_is_finite(self):
        """Test that potential values are finite."""
        x = np.linspace(-10, 10, 100)
        gamma_n = load_riemann_zeros(n_zeros=10)
        V = marchenko_potential(x, gamma_n)
        assert np.all(np.isfinite(V))
    
    def test_potential_symmetry(self):
        """Test that potential is approximately symmetric."""
        x = np.linspace(-10, 10, 101)  # Odd number for center at 0
        gamma_n = load_riemann_zeros(n_zeros=10)
        V = marchenko_potential(x, gamma_n)
        
        # Potential should be roughly symmetric around x=0
        # (not exactly, due to log terms)
        V_left = V[:50]
        V_right = V[-50:][::-1]
        # Check that structure is similar
        assert np.corrcoef(V_left, V_right)[0, 1] > MIN_SYMMETRY_CORRELATION


class TestHamiltonianConstruction:
    """Tests for Hamiltonian construction."""
    
    def test_hamiltonian_shape(self):
        """Test that Hamiltonian has correct shape."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(100, (-10, 10), gamma_n)
        assert H.shape == (100, 100)
        assert len(x) == 100
        assert dx > 0
    
    def test_hamiltonian_is_hermitian(self):
        """Test that Hamiltonian is Hermitian (symmetric for real)."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(100, (-10, 10), gamma_n)
        
        hermiticity_error = np.max(np.abs(H - H.T))
        assert hermiticity_error < 1e-14
    
    def test_hamiltonian_eigenvalues_are_real(self):
        """Test that all eigenvalues are real."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(100, (-10, 10), gamma_n)
        
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.isreal(eigenvalues))


class TestEigenstateComputation:
    """Tests for eigenstate computation."""
    
    def test_eigenstate_shape(self):
        """Test that eigenstates have correct shape."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(200, (-15, 15), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        assert len(eigenvalues) == 5
        assert psi.shape == (200, 5)
    
    def test_eigenvalues_are_sorted(self):
        """Test that eigenvalues are sorted ascending."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(200, (-15, 15), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=10)
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] <= eigenvalues[i + 1]
    
    def test_eigenfunctions_are_normalized(self):
        """Test that eigenfunctions are normalized."""
        gamma_n = load_riemann_zeros(n_zeros=10)
        H, x, dx = construct_hamiltonian(200, (-15, 15), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        
        for n in range(psi.shape[1]):
            norm = np.sqrt(np.sum(psi[:, n]**2) * dx)
            assert abs(norm - 1.0) < NUMERICAL_TOLERANCE


class TestOrthonormality:
    """Tests for orthonormality verification."""
    
    def test_orthonormality_simple(self):
        """Test orthonormality with simple case."""
        gamma_n = load_riemann_zeros(n_zeros=20)
        H, x, dx = construct_hamiltonian(500, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        results = verify_orthonormality(psi, dx)
        
        assert results['is_orthonormal']
        assert results['max_error'] < NUMERICAL_TOLERANCE
    
    def test_orthonormality_diagonal(self):
        """Test that diagonal of overlap matrix is 1."""
        gamma_n = load_riemann_zeros(n_zeros=20)
        H, x, dx = construct_hamiltonian(500, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        results = verify_orthonormality(psi, dx)
        
        for err in results['diagonal_errors']:
            assert err < NUMERICAL_TOLERANCE
    
    def test_orthonormality_off_diagonal(self):
        """Test that off-diagonal elements are near zero."""
        gamma_n = load_riemann_zeros(n_zeros=20)
        H, x, dx = construct_hamiltonian(500, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        results = verify_orthonormality(psi, dx)
        
        assert results['off_diagonal_max'] < NUMERICAL_TOLERANCE


class TestLocalization:
    """Tests for localization verification."""
    
    def test_localization_bound_states(self):
        """Test that low-energy states are localized."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        results = verify_localization(psi, x)
        
        # At least the first few states should be localized
        assert results['details'][0]['is_localized']
        assert results['details'][1]['is_localized']
    
    def test_localization_boundary_decay(self):
        """Test that boundary ratios are small for bound states."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=3)
        results = verify_localization(psi, x)
        
        # Ground state should have very small boundary ratio
        assert results['boundary_ratios'][0] < NUMERICAL_TOLERANCE


class TestNodeTheorem:
    """Tests for Sturm-Liouville node theorem."""
    
    def test_node_count_ground_state(self):
        """Test that ground state has 0 nodes."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        
        nodes = count_nodes(psi[:, 0], x)
        assert nodes == 0
    
    def test_node_count_first_excited(self):
        """Test that first excited state has 1 node."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        
        nodes = count_nodes(psi[:, 1], x)
        assert nodes == 1
    
    def test_node_theorem_verification(self):
        """Test full node theorem verification."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        results = verify_node_theorem(psi, x)
        
        assert results['all_correct']
        for i, detail in enumerate(results['details']):
            assert detail['expected'] == i
            assert detail['actual'] == i


class TestEigenfunctionExpansion:
    """Tests for eigenfunction expansion."""
    
    def test_expansion_coefficients(self):
        """Test that expansion coefficients are computed correctly."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        
        # Use first eigenfunction as test function
        f = psi[:, 0]
        coeffs = expand_in_eigenbasis(f, psi, dx)
        
        # First coefficient should be 1, rest should be 0
        assert abs(coeffs[0] - 1.0) < NUMERICAL_TOLERANCE
        for c in coeffs[1:]:
            assert abs(c) < NUMERICAL_TOLERANCE
    
    def test_reconstruction(self):
        """Test that reconstruction works."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=5)
        
        # Use a combination of eigenfunctions
        f = 0.6 * psi[:, 0] + 0.8 * psi[:, 2]
        
        coeffs = expand_in_eigenbasis(f, psi, dx)
        f_reconstructed = reconstruct_from_coefficients(coeffs, psi)
        
        error = np.sqrt(np.sum((f - f_reconstructed)**2) * dx)
        assert error < NUMERICAL_TOLERANCE
    
    def test_delta_function_expansion(self):
        """Test expansion of delta function."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(1000, (-20, 20), gamma_n)
        
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=10)
        
        delta = create_delta_function(x, x0=0.0, dx=dx)
        results = verify_expansion_convergence(delta, psi, dx, x)
        
        # Should have finite coefficients
        assert all(np.isfinite(results['coefficients']))
        
        # Error should decrease with more terms
        errors = results['relative_errors']
        assert errors[-1] <= errors[0]


class TestCompleteValidation:
    """Tests for complete validation run."""
    
    def test_complete_validation_runs(self):
        """Test that complete validation runs without error."""
        results = run_complete_validation(
            n_zeros=10,
            n_points=200,
            x_range=(-15, 15),
            num_states=5,
            verbose=False
        )
        
        assert 'success' in results
        assert 'orthonormality' in results
        assert 'localization' in results
        assert 'node_theorem' in results
        assert 'expansion' in results
    
    def test_complete_validation_passes(self):
        """Test that complete validation passes with standard parameters."""
        results = run_complete_validation(
            n_zeros=30,
            n_points=1000,
            x_range=(-20, 20),
            num_states=10,
            verbose=False
        )
        
        assert results['success']
        assert results['orthonormality']['is_orthonormal']
        assert results['localization']['is_localized']
        assert results['node_theorem']['all_correct']
    
    def test_parameters_in_results(self):
        """Test that parameters are stored in results."""
        results = run_complete_validation(
            n_zeros=15,
            n_points=300,
            num_states=8,
            verbose=False
        )
        
        assert results['parameters']['n_zeros'] == 15
        assert results['parameters']['n_points'] == 300
        assert results['parameters']['num_states'] == 8
        assert results['parameters']['qcal_frequency'] == QCAL_BASE_FREQUENCY
        assert results['parameters']['qcal_coherence'] == QCAL_COHERENCE


class TestQCALIntegration:
    """Tests for QCAL integration."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are correct."""
        assert QCAL_BASE_FREQUENCY == 141.7001
        assert QCAL_COHERENCE == 244.36


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_no_nan_values(self):
        """Test that no NaN values are produced."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(500, (-15, 15), gamma_n)
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=10)
        
        assert not np.any(np.isnan(eigenvalues))
        assert not np.any(np.isnan(psi))
    
    def test_no_inf_values(self):
        """Test that no infinite values are produced."""
        gamma_n = load_riemann_zeros(n_zeros=30)
        H, x, dx = construct_hamiltonian(500, (-15, 15), gamma_n)
        eigenvalues, psi = compute_eigenstates(H, dx, num_states=10)
        
        assert not np.any(np.isinf(eigenvalues))
        assert not np.any(np.isinf(psi))
    
    def test_consistent_results(self):
        """Test that results are consistent across runs."""
        gamma_n = load_riemann_zeros(n_zeros=20)
        
        # Run twice
        H1, x1, dx1 = construct_hamiltonian(300, (-15, 15), gamma_n)
        ev1, psi1 = compute_eigenstates(H1, dx1, num_states=5)
        
        H2, x2, dx2 = construct_hamiltonian(300, (-15, 15), gamma_n)
        ev2, psi2 = compute_eigenstates(H2, dx2, num_states=5)
        
        # Eigenvalues should be identical
        np.testing.assert_allclose(ev1, ev2, rtol=NUMERICAL_TOLERANCE)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
