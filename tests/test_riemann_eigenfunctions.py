"""
Test module for Riemann eigenfunctions visualization.

This module tests the implementation of the 10 wavefunctions ψₙ(x)
corresponding to the first 10 non-trivial Riemann zeta zeros.

Validated properties:
1. Node counting: ψₙ has exactly (n-1) nodes
2. Parity: ψₙ(-x) = (-1)^(n+1) ψₙ(x)
3. Localization: Exponential decay at boundaries
4. Orthonormality: ⟨ψₘ|ψₙ⟩ = δₘₙ with error < 10⁻¹⁰

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from riemann_eigenfunctions_visualization import (
    get_first_riemann_zeros,
    build_schrodinger_hamiltonian,
    compute_eigenfunctions,
    count_nodes,
    check_parity,
    check_orthonormality,
    check_localization,
    validate_all_properties,
    run_riemann_eigenfunction_validation,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
)


class TestRiemannZeros:
    """Test the Riemann zeros data."""

    def test_get_first_10_zeros(self):
        """Test that we can retrieve 10 Riemann zeros."""
        zeros = get_first_riemann_zeros(10)
        assert len(zeros) == 10
        assert all(z > 0 for z in zeros)

    def test_zeros_are_ordered(self):
        """Test that zeros are in ascending order."""
        zeros = get_first_riemann_zeros(10)
        assert all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))

    def test_first_zero_value(self):
        """Test the value of the first Riemann zero."""
        zeros = get_first_riemann_zeros(1)
        # γ₁ ≈ 14.134725...
        assert abs(zeros[0] - 14.134725141734693) < 1e-10

    def test_tenth_zero_value(self):
        """Test the value of the tenth Riemann zero."""
        zeros = get_first_riemann_zeros(10)
        # γ₁₀ ≈ 49.773832...
        assert abs(zeros[9] - 49.773832477672302) < 1e-10


class TestHamiltonian:
    """Test the Hamiltonian construction."""

    def test_hamiltonian_is_symmetric(self):
        """Test that H is symmetric (Hermitian for real matrices)."""
        gamma_n = get_first_riemann_zeros(10)
        H, x = build_schrodinger_hamiltonian(N=200, L=20.0, gamma_n=gamma_n)

        asymmetry = np.max(np.abs(H - H.T))
        assert asymmetry < 1e-14

    def test_hamiltonian_shape(self):
        """Test that H has correct dimensions."""
        H, x = build_schrodinger_hamiltonian(N=100, L=10.0)
        assert H.shape == (100, 100)
        assert len(x) == 100

    def test_domain_range(self):
        """Test that x covers [-L, L]."""
        L = 30.0
        H, x = build_schrodinger_hamiltonian(N=1000, L=L)
        assert x[0] == pytest.approx(-L, rel=1e-10)
        assert x[-1] == pytest.approx(L, rel=1e-10)


class TestEigenfunctions:
    """Test eigenfunction properties."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions once for all tests in this class."""
        gamma_n = get_first_riemann_zeros(10)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=10)
        return x, eigenvalues, eigenvectors, gamma_n

    def test_eigenvalues_are_real(self, eigensystem):
        """Test that all eigenvalues are real."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        # For real symmetric matrices, eigenvalues must be real
        assert np.all(np.isreal(eigenvalues))

    def test_eigenvalues_are_ordered(self, eigensystem):
        """Test that eigenvalues are in ascending order."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        assert all(eigenvalues[i] <= eigenvalues[i + 1]
                   for i in range(len(eigenvalues) - 1))

    def test_ground_state_has_no_nodes(self, eigensystem):
        """Test that ψ₁(x) has 0 nodes (ground state)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_1 = eigenvectors[:, 0]
        nodes = count_nodes(psi_1, x)
        assert nodes == 0

    def test_second_state_has_one_node(self, eigensystem):
        """Test that ψ₂(x) has 1 node."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_2 = eigenvectors[:, 1]
        nodes = count_nodes(psi_2, x)
        assert nodes == 1

    def test_node_counting_all_states(self, eigensystem):
        """Test that ψₙ has (n-1) nodes for all n from 1 to 10."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        for n in range(1, 11):
            psi_n = eigenvectors[:, n - 1]
            nodes = count_nodes(psi_n, x)
            assert nodes == n - 1, f"State ψ_{n} should have {n-1} nodes, got {nodes}"

    def test_ground_state_even_parity(self, eigensystem):
        """Test that ψ₁ is even: ψ₁(-x) = ψ₁(x)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_1 = eigenvectors[:, 0]
        is_correct, deviation = check_parity(psi_1, x, n=1)
        assert is_correct, f"ψ₁ should have even parity, deviation = {deviation}"

    def test_second_state_odd_parity(self, eigensystem):
        """Test that ψ₂ is odd: ψ₂(-x) = -ψ₂(x)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_2 = eigenvectors[:, 1]
        is_correct, deviation = check_parity(psi_2, x, n=2)
        assert is_correct, f"ψ₂ should have odd parity, deviation = {deviation}"

    def test_alternating_parity(self, eigensystem):
        """Test that parity alternates: ψₙ(-x) = (-1)^(n+1) ψₙ(x)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        for n in range(1, 11):
            psi_n = eigenvectors[:, n - 1]
            is_correct, deviation = check_parity(psi_n, x, n=n)
            assert is_correct, f"ψ_{n} has incorrect parity, deviation = {deviation}"


class TestOrthonormality:
    """Test orthonormality of eigenfunctions."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions once for all tests in this class."""
        gamma_n = get_first_riemann_zeros(10)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=10)
        return x, eigenvectors

    def test_orthonormality(self, eigensystem):
        """Test that ⟨ψₘ|ψₙ⟩ = δₘₙ with high precision."""
        x, eigenvectors = eigensystem
        is_orthonormal, max_error = check_orthonormality(eigenvectors, x)

        # Require very high precision
        assert is_orthonormal, f"Eigenfunctions not orthonormal, max error = {max_error}"
        assert max_error < 1e-10, f"Orthonormality error {max_error} exceeds 1e-10"

    def test_individual_normalizations(self, eigensystem):
        """Test that each eigenfunction is normalized to 1."""
        x, eigenvectors = eigensystem
        dx = x[1] - x[0]
        from scipy.integrate import simpson

        for i in range(10):
            psi = eigenvectors[:, i]
            norm_sq = simpson(psi**2, x=x, dx=dx)
            assert abs(norm_sq - 1.0) < 1e-10, f"||ψ_{i+1}||² = {norm_sq}, expected 1.0"


class TestLocalization:
    """Test exponential localization of eigenfunctions."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions once for all tests in this class."""
        gamma_n = get_first_riemann_zeros(10)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=10)
        return x, eigenvectors

    def test_localization_all_states(self, eigensystem):
        """Test that all eigenfunctions are exponentially localized."""
        x, eigenvectors = eigensystem
        for n in range(1, 11):
            psi_n = eigenvectors[:, n - 1]
            is_localized, decay_rate = check_localization(psi_n, x)
            assert is_localized, f"ψ_{n} is not localized"

    def test_ground_state_gaussian_like(self, eigensystem):
        """Test that ground state is approximately Gaussian."""
        x, eigenvectors = eigensystem
        psi_1 = eigenvectors[:, 0]

        # Ground state of harmonic oscillator should be Gaussian-like
        # Check that maximum is near x=0
        max_idx = np.argmax(np.abs(psi_1))
        assert abs(x[max_idx]) < 1.0, "Ground state maximum should be near x=0"


class TestValidationSummary:
    """Test the complete validation workflow."""

    def test_run_validation_returns_results(self):
        """Test that validation returns proper results dictionary."""
        results = run_riemann_eigenfunction_validation(
            N=500, L=20.0, n_states=10, save_figures=False, verbose=False
        )

        assert 'n_states' in results
        assert 'nodes' in results
        assert 'parity' in results
        assert 'localization' in results
        assert 'orthonormality' in results
        assert results['n_states'] == 10

    def test_all_validations_pass(self):
        """Test that all validations pass with standard parameters."""
        results = run_riemann_eigenfunction_validation(
            N=1000, L=30.0, n_states=10, save_figures=False, verbose=False
        )

        assert results['all_passed'], "Not all validations passed"

    def test_orthonormality_precision(self):
        """Test that orthonormality error is less than 10⁻¹⁰."""
        results = run_riemann_eigenfunction_validation(
            N=1000, L=30.0, n_states=10, save_figures=False, verbose=False
        )

        max_error = results['orthonormality']['max_error']
        assert max_error < 1e-10, f"Orthonormality error {max_error} exceeds 10⁻¹⁰"


class TestQCALIntegration:
    """Test QCAL ∞³ integration."""

    def test_qcal_base_frequency(self):
        """Test QCAL base frequency constant."""
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
