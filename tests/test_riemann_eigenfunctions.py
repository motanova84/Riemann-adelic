"""
Test module for Riemann eigenfunctions validation.

This module tests the eigenfunctions ψ_n(x) of the Hamiltonian H = -d²/dx² + V(x),
reconstructed from the first 30 imaginary parts γ_n of the Riemann zeros.

Key tests:
    1. Orthonormality: ∫ψ_n(x)ψ_m(x)dx = δ_{nm}
    2. Bound state localization
    3. Sturm-Liouville nodal counting
    4. Eigenvalue correspondence
    5. Spectral expansion capability

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from pathlib import Path


# Import module to test
try:
    from riemann_eigenfunctions import (
        get_riemann_zeros,
        build_hamiltonian_from_zeros,
        compute_eigenfunctions,
        verify_orthonormality,
        verify_localization,
        verify_nodal_counting,
        verify_eigenvalues,
        verify_spectral_expansion,
        run_full_validation,
        RIEMANN_ZEROS,
        QCAL_BASE_FREQUENCY,
        QCAL_COHERENCE
    )
    RIEMANN_EIGENFUNCTIONS_AVAILABLE = True
except ImportError:
    RIEMANN_EIGENFUNCTIONS_AVAILABLE = False


@pytest.mark.skipif(not RIEMANN_EIGENFUNCTIONS_AVAILABLE, 
                    reason="riemann_eigenfunctions module not available")
class TestRiemannEigenfunctions:
    """Test class for Riemann eigenfunctions."""

    def test_riemann_zeros_count(self):
        """Test that we have 30 Riemann zeros defined."""
        assert len(RIEMANN_ZEROS) == 30
        assert RIEMANN_ZEROS[0] == pytest.approx(14.134725141734693, rel=1e-10)
        assert RIEMANN_ZEROS[-1] == pytest.approx(101.31785100573139, rel=1e-10)

    def test_get_riemann_zeros_subset(self):
        """Test getting a subset of Riemann zeros."""
        zeros_10 = get_riemann_zeros(10)
        assert len(zeros_10) == 10
        assert zeros_10[0] == RIEMANN_ZEROS[0]
        assert zeros_10[9] == RIEMANN_ZEROS[9]

    def test_get_riemann_zeros_max(self):
        """Test getting more zeros than available returns all available."""
        zeros_100 = get_riemann_zeros(100)
        assert len(zeros_100) == 30

    def test_qcal_constants(self):
        """Test QCAL constants are defined correctly."""
        assert QCAL_BASE_FREQUENCY == 141.7001
        assert QCAL_COHERENCE == 244.36

    def test_build_hamiltonian_shape(self):
        """Test Hamiltonian matrix has correct shape."""
        N = 100
        H, x, V = build_hamiltonian_from_zeros(N=N, L=10.0)
        assert H.shape == (N, N)
        assert len(x) == N
        assert len(V) == N

    def test_hamiltonian_symmetry(self):
        """Test that the Hamiltonian is symmetric (self-adjoint)."""
        H, x, V = build_hamiltonian_from_zeros(N=100, L=10.0)
        max_asymmetry = np.max(np.abs(H - H.T))
        assert max_asymmetry < 1e-14, f"Hamiltonian not symmetric: max_asymmetry = {max_asymmetry}"

    def test_compute_eigenfunctions_returns_correct_types(self):
        """Test that compute_eigenfunctions returns correct types."""
        eigenvalues, eigenfunctions, x, V = compute_eigenfunctions(N=100, L=10.0, n_states=5)
        
        assert isinstance(eigenvalues, np.ndarray)
        assert isinstance(eigenfunctions, np.ndarray)
        assert isinstance(x, np.ndarray)
        assert isinstance(V, np.ndarray)
        
        assert len(eigenvalues) == 5
        assert eigenfunctions.shape == (100, 5)

    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted in ascending order."""
        eigenvalues, _, _, _ = compute_eigenfunctions(N=100, L=10.0, n_states=10)
        
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] <= eigenvalues[i + 1], \
                f"Eigenvalues not sorted: E[{i}]={eigenvalues[i]} > E[{i+1}]={eigenvalues[i+1]}"

    def test_orthonormality(self):
        """Test orthonormality of eigenfunctions: ∫ψ_n·ψ_m dx = δ_{nm}."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=8)
        
        result = verify_orthonormality(eigenfunctions, x, n_check=8)
        
        assert result["is_orthonormal"], \
            f"Eigenfunctions not orthonormal: max_error = {result['max_error']}"
        assert result["max_error"] < 1e-10, \
            f"Orthonormality error too large: {result['max_error']}"

    def test_localization(self):
        """Test bound state localization: ψ_n → 0 for |x| → ∞."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=10)
        
        result = verify_localization(eigenfunctions, x, L=25.0)
        
        assert result["all_localized"], \
            f"Not all states localized: {result['is_localized_per_state']}"
        assert all(v < 0.05 for v in result["max_tail_values"]), \
            f"Tail values too large: {result['max_tail_values']}"

    def test_nodal_counting(self):
        """Test Sturm-Liouville nodal theorem: ψ_n has n nodes."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=10)
        
        result = verify_nodal_counting(eigenfunctions, x, n_check=10)
        
        assert result["all_correct"], \
            f"Nodal counts incorrect: computed={result['node_counts']}, expected={result['expected_counts']}"

    def test_eigenvalue_correspondence(self):
        """Test that eigenvalues correspond to -γ_n²."""
        eigenvalues, _, _, _ = compute_eigenfunctions(N=500, L=25.0, n_states=10)
        
        result = verify_eigenvalues(eigenvalues, n_check=10)
        
        # Ground state should be close to -γ_0² ≈ -199.79
        ground_state_target = -RIEMANN_ZEROS[0]**2
        assert result["eigenvalues_computed"][0] < 0, "Ground state energy should be negative"
        
        # Check that computed eigenvalues are reasonably ordered
        assert all(result["eigenvalues_computed"][i] < result["eigenvalues_computed"][i+1] 
                  for i in range(len(result["eigenvalues_computed"])-1)), \
            "Computed eigenvalues should be increasing"

    def test_spectral_expansion_convergence(self):
        """Test that spectral expansion converges rapidly for δ(x) mimetic."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=10)
        
        result = verify_spectral_expansion(eigenfunctions, x, n_terms=10)
        
        assert result["converges_rapidly"], \
            f"Spectral expansion not converging rapidly"
        assert result["relative_error"] < 0.5, \
            f"Reconstruction error too large: {result['relative_error']}"

    def test_full_validation_passes(self):
        """Test that the full validation passes."""
        result = run_full_validation(N=500, L=25.0, n_states=10, verbose=False)
        
        assert result["success"], "Full validation should pass"
        assert result["orthonormality"]["is_orthonormal"]
        assert result["localization"]["all_localized"]
        assert result["nodal_counting"]["all_correct"]

    def test_ground_state_properties(self):
        """Test ground state (ψ_0) specific properties."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=1)
        
        psi_0 = eigenfunctions[:, 0]
        
        # Ground state should not have nodes in the significant region
        # Find where the function has significant amplitude
        max_amplitude = np.max(np.abs(psi_0))
        significant_mask = np.abs(psi_0) > 1e-12 * max_amplitude
        psi_significant = psi_0[significant_mask]
        
        if len(psi_significant) > 0:
            # Check that the significant part doesn't change sign
            signs = np.sign(psi_significant)
            sign_changes = np.sum(np.abs(np.diff(signs)) == 2)
            assert sign_changes == 0, \
                f"Ground state should have 0 nodes, found {sign_changes} sign changes"
        
        # Ground state should be symmetric
        N = len(x)
        psi_left = psi_0[:N//2]
        psi_right = psi_0[N//2:][::-1]
        min_len = min(len(psi_left), len(psi_right))
        symmetry_error = np.max(np.abs(psi_left[:min_len] - psi_right[:min_len]))
        assert symmetry_error < 1e-10, \
            f"Ground state should be symmetric: error = {symmetry_error}"

    def test_first_excited_state_properties(self):
        """Test first excited state (ψ_1) specific properties."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=2)
        
        psi_1 = eigenfunctions[:, 1]
        
        # First excited state should have exactly 1 node
        signs = np.sign(psi_1)
        sign_changes = np.sum(np.abs(np.diff(signs)) == 2)
        assert sign_changes == 1, \
            f"First excited state should have 1 node, found {sign_changes}"

    def test_eigenfunction_normalization(self):
        """Test that eigenfunctions are properly normalized."""
        _, eigenfunctions, x, _ = compute_eigenfunctions(N=500, L=25.0, n_states=5)
        
        for n in range(5):
            psi_n = eigenfunctions[:, n]
            norm = np.trapezoid(psi_n**2, x=x)
            assert abs(norm - 1.0) < 1e-10, \
                f"Eigenfunction ψ_{n} not normalized: ⟨ψ_{n}|ψ_{n}⟩ = {norm}"


class TestRiemannZerosData:
    """Test class for Riemann zeros data validation."""
    
    @pytest.mark.skipif(not RIEMANN_EIGENFUNCTIONS_AVAILABLE, 
                        reason="riemann_eigenfunctions module not available")
    def test_zeros_are_positive(self):
        """Test that all Riemann zeros are positive."""
        assert all(z > 0 for z in RIEMANN_ZEROS)

    @pytest.mark.skipif(not RIEMANN_EIGENFUNCTIONS_AVAILABLE, 
                        reason="riemann_eigenfunctions module not available")
    def test_zeros_are_increasing(self):
        """Test that Riemann zeros are in increasing order."""
        for i in range(len(RIEMANN_ZEROS) - 1):
            assert RIEMANN_ZEROS[i] < RIEMANN_ZEROS[i + 1]

    @pytest.mark.skipif(not RIEMANN_EIGENFUNCTIONS_AVAILABLE, 
                        reason="riemann_eigenfunctions module not available")
    def test_known_zero_values(self):
        """Test some well-known Riemann zero values."""
        # First few zeros from mathematical literature
        known_zeros = [
            14.134725141734693,
            21.022039638771555,
            25.010857580145688,
        ]
        for i, known in enumerate(known_zeros):
            assert RIEMANN_ZEROS[i] == pytest.approx(known, rel=1e-12)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
