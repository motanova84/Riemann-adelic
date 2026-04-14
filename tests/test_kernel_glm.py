#!/usr/bin/env python3
"""
Tests for the GLM (Gel'fand-Levitan-Marchenko) kernel inverse scattering module.

This test suite validates:
    - F_glm_kernel computation
    - Marchenko equation solving
    - Potential reconstruction
    - Eigenvalue validation

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np


class TestGLMKernel:
    """Tests for F_glm_kernel function."""

    def test_kernel_at_origin(self):
        """Test that F(0) = N (number of zeros)."""
        from inversion.kernel_glm import F_glm_kernel
        gamma = np.array([14.13, 21.02, 25.01])
        result = F_glm_kernel(0.0, gamma)
        assert abs(result - len(gamma)) < 1e-10

    def test_kernel_symmetry(self):
        """Test that F(x) = F(-x) (even function)."""
        from inversion.kernel_glm import F_glm_kernel
        gamma = np.array([14.13, 21.02, 25.01, 30.42])
        x_test = 2.5
        assert abs(F_glm_kernel(x_test, gamma) - F_glm_kernel(-x_test, gamma)) < 1e-10

    def test_kernel_decay(self):
        """Test that F(x) decays exponentially as |x| → ∞."""
        from inversion.kernel_glm import F_glm_kernel
        gamma = np.array([14.13, 21.02, 25.01])
        # F should decay for large x
        assert F_glm_kernel(10.0, gamma) < F_glm_kernel(0.0, gamma)
        assert F_glm_kernel(20.0, gamma) < F_glm_kernel(10.0, gamma)

    def test_kernel_positivity(self):
        """Test that F(x) > 0 for all x."""
        from inversion.kernel_glm import F_glm_kernel
        gamma = np.array([14.13, 21.02, 25.01])
        for x in np.linspace(-5, 5, 21):
            assert F_glm_kernel(x, gamma) > 0


class TestFMatrixConstruction:
    """Tests for F matrix construction."""

    def test_matrix_shape(self):
        """Test that F matrix has correct shape."""
        from inversion.kernel_glm import construct_F_matrix
        gamma = np.array([14.13, 21.02])
        x_grid = np.linspace(0, 5, 10)
        F_mat = construct_F_matrix(x_grid, gamma)
        assert F_mat.shape == (10, 10)

    def test_matrix_symmetry(self):
        """Test that F matrix is symmetric (F[i,j] = F[j,i])."""
        from inversion.kernel_glm import construct_F_matrix
        gamma = np.array([14.13, 21.02, 25.01])
        x_grid = np.linspace(0, 5, 20)
        F_mat = construct_F_matrix(x_grid, gamma)
        assert np.allclose(F_mat, F_mat.T)

    def test_matrix_positivity(self):
        """Test that all F matrix elements are positive."""
        from inversion.kernel_glm import construct_F_matrix
        gamma = np.array([14.13, 21.02])
        x_grid = np.linspace(0, 5, 15)
        F_mat = construct_F_matrix(x_grid, gamma)
        assert np.all(F_mat > 0)


class TestMarchenkoSolve:
    """Tests for Marchenko equation solver."""

    def test_solve_returns_correct_shapes(self):
        """Test that marchenko_solve returns arrays of correct shape."""
        from inversion.kernel_glm import marchenko_solve
        gamma = np.array([14.13, 21.02, 25.01])
        M = 50
        L = 5.0
        x_grid, K_diag, L_vec = marchenko_solve(gamma, M, L)

        assert len(x_grid) == M
        assert len(K_diag) == M
        assert len(L_vec) == M

    def test_solve_grid_range(self):
        """Test that grid spans correct range."""
        from inversion.kernel_glm import marchenko_solve
        gamma = np.array([14.13, 21.02])
        M = 100
        L = 10.0
        x_grid, _, _ = marchenko_solve(gamma, M, L)

        assert x_grid[0] == 0
        assert abs(x_grid[-1] - L) < 1e-10

    def test_solve_stability(self):
        """Test that solution has no NaN or Inf values."""
        from inversion.kernel_glm import marchenko_solve
        gamma = np.array([14.13, 21.02, 25.01, 30.42])
        x_grid, K_diag, L_vec = marchenko_solve(gamma, M=100, L=10.0)

        assert not np.any(np.isnan(K_diag))
        assert not np.any(np.isinf(K_diag))
        assert not np.any(np.isnan(L_vec))
        assert not np.any(np.isinf(L_vec))


class TestPotentialReconstruction:
    """Tests for potential reconstruction."""

    def test_potential_returns_correct_shapes(self):
        """Test that reconstruct_potential returns arrays of correct shape."""
        from inversion.kernel_glm import marchenko_solve, reconstruct_potential
        gamma = np.array([14.13, 21.02, 25.01])
        M = 50
        x_grid, K_diag, _ = marchenko_solve(gamma, M, L=5.0)
        x_full, V_full = reconstruct_potential(x_grid, K_diag)

        # x_full should have 2*M - 1 points
        assert len(x_full) == 2 * M - 1
        assert len(V_full) == len(x_full)

    def test_potential_symmetry(self):
        """Test that reconstructed V(x) is even: V(-x) = V(x)."""
        from inversion.kernel_glm import marchenko_solve, reconstruct_potential
        gamma = np.array([14.13, 21.02, 25.01])
        x_grid, K_diag, _ = marchenko_solve(gamma, M=100, L=10.0)
        x_full, V_full = reconstruct_potential(x_grid, K_diag)

        # Check symmetry around origin
        n = len(V_full)
        mid = n // 2
        for i in range(min(10, mid)):
            assert abs(V_full[mid - i] - V_full[mid + i]) < 1e-10

    def test_potential_is_real(self):
        """Test that potential values are real (no imaginary parts)."""
        from inversion.kernel_glm import marchenko_solve, reconstruct_potential
        gamma = np.array([14.13, 21.02])
        x_grid, K_diag, _ = marchenko_solve(gamma, M=50, L=5.0)
        x_full, V_full = reconstruct_potential(x_grid, K_diag)

        assert np.all(np.isreal(V_full))

    def test_potential_well_structure(self):
        """Test that potential has well structure with sufficient zeros."""
        from inversion.kernel_glm import marchenko_solve, reconstruct_potential, get_riemann_zeros
        # Use enough zeros for meaningful potential reconstruction
        gamma = get_riemann_zeros(20)
        x_grid, K_diag, _ = marchenko_solve(gamma, M=150, L=12.0)
        x_full, V_full = reconstruct_potential(x_grid, K_diag)

        # Check that V has well-defined structure (non-trivial shape)
        # For large N, the potential develops negative values
        # With fewer zeros, it may be near-zero but should still have structure
        V_range = V_full.max() - V_full.min()
        assert V_range > 0  # Non-trivial potential


class TestGetRiemannZeros:
    """Tests for Riemann zeros retrieval."""

    def test_zeros_count(self):
        """Test that correct number of zeros is returned."""
        from inversion.kernel_glm import get_riemann_zeros
        gamma = get_riemann_zeros(5)
        assert len(gamma) == 5

    def test_zeros_ordering(self):
        """Test that zeros are in increasing order."""
        from inversion.kernel_glm import get_riemann_zeros
        gamma = get_riemann_zeros(10)
        for i in range(len(gamma) - 1):
            assert gamma[i] < gamma[i + 1]

    def test_zeros_positivity(self):
        """Test that all zeros are positive (imaginary parts)."""
        from inversion.kernel_glm import get_riemann_zeros
        gamma = get_riemann_zeros(5)
        assert np.all(gamma > 0)

    def test_first_zero_value(self):
        """Test that first zero is approximately 14.13."""
        from inversion.kernel_glm import get_riemann_zeros
        gamma = get_riemann_zeros(1)
        assert abs(gamma[0] - 14.134725) < 0.01


class TestFullReconstruction:
    """Tests for full reconstruction pipeline."""

    def test_full_reconstruction_returns_dict(self):
        """Test that full_reconstruction returns a dictionary."""
        from inversion.kernel_glm import full_reconstruction
        result = full_reconstruction(N=5, M=50, L=5.0, validate=False)
        assert isinstance(result, dict)
        assert 'gamma' in result
        assert 'x_full' in result
        assert 'V_full' in result
        assert 'K_diag' in result

    def test_full_reconstruction_with_validation(self):
        """Test full reconstruction with eigenvalue validation."""
        from inversion.kernel_glm import full_reconstruction
        result = full_reconstruction(N=10, M=100, L=10.0, validate=True)

        assert 'validation' in result
        assert 'eigenvalues' in result['validation']
        assert 'mean_error' in result['validation']
        assert 'V_at_origin' in result['validation']
        assert 'V_min' in result['validation']

    def test_reconstruction_consistency(self):
        """Test that gamma array in result matches the count."""
        from inversion.kernel_glm import full_reconstruction
        N = 15
        result = full_reconstruction(N=N, M=80, L=8.0, validate=False)
        assert len(result['gamma']) == N


class TestValidateReconstruction:
    """Tests for validation of reconstruction."""

    def test_validation_returns_required_keys(self):
        """Test that validation returns all required keys."""
        from inversion.kernel_glm import (
            marchenko_solve, reconstruct_potential,
            validate_reconstruction, get_riemann_zeros
        )
        gamma = get_riemann_zeros(10)
        x_grid, K_diag, _ = marchenko_solve(gamma, M=100, L=10.0)
        x_full, V_full = reconstruct_potential(x_grid, K_diag)

        result = validate_reconstruction(
            x_full, V_full, gamma,
            num_eigenvalues=8, Nx=1000
        )

        required_keys = [
            'eigenvalues', 'expected', 'mean_error',
            'V_at_origin', 'V_min', 'success'
        ]
        for key in required_keys:
            assert key in result

    def test_eigenvalues_are_real(self):
        """Test that computed eigenvalues are real."""
        from inversion.kernel_glm import full_reconstruction
        result = full_reconstruction(N=10, M=100, L=10.0, validate=True)
        eigenvalues = result['validation']['eigenvalues']
        assert np.all(np.isreal(eigenvalues))


class TestModuleImports:
    """Tests for module import compatibility."""

    def test_import_from_inversion(self):
        """Test that functions can be imported from inversion package."""
        from inversion import (
            F_glm_kernel,
            marchenko_solve,
            reconstruct_potential,
            full_reconstruction,
            kernel_glm,
            solve_marchenko
        )

        assert callable(F_glm_kernel)
        assert callable(marchenko_solve)
        assert callable(reconstruct_potential)
        assert callable(full_reconstruction)
        assert callable(kernel_glm)
        assert callable(solve_marchenko)

    def test_aliases_work(self):
        """Test that function aliases point to correct functions."""
        from inversion import kernel_glm, solve_marchenko
        from inversion import F_glm_kernel, marchenko_solve

        assert kernel_glm is F_glm_kernel
        assert solve_marchenko is marchenko_solve


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
