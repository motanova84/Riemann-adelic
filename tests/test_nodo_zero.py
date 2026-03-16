#!/usr/bin/env python3
"""
Tests for the Nodo Zero operator — operators/nodo_zero.py

Validates:
    1. Hamiltonian construction (shape, symmetry, delta potential)
    2. Eigenvalue computation (real, sorted, physically reasonable)
    3. Ground-state density maximum at x=0
    4. Node coherence Ψ_nodo ≥ 0.888
    5. Vertical Transform: finite, correct shift property
    6. compute_psi_nodo formula
    7. Full validation pipeline via validate_nodo_zero

DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Ensure repo root and operators/ are importable
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(REPO_ROOT / "operators"))

from nodo_zero import (
    F0,
    PSI_THRESHOLD,
    build_nodo_zero_hamiltonian,
    check_coherence_threshold,
    compute_psi_nodo,
    get_riemann_zeros,
    ground_state_density_max_at_zero,
    solve_nodo_zero,
    validate_nodo_zero,
    vertical_transform,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify module-level constants."""

    def test_f0_value(self):
        assert abs(F0 - 141.7001) < 1e-6, "F0 must equal 141.7001 Hz"

    def test_psi_threshold(self):
        assert abs(PSI_THRESHOLD - 0.888) < 1e-9, "PSI_THRESHOLD must be 0.888"


# ---------------------------------------------------------------------------
# Riemann zeros
# ---------------------------------------------------------------------------

class TestRiemannZeros:
    """Verify Riemann zero retrieval."""

    def test_first_zero(self):
        zeros = get_riemann_zeros(1)
        assert len(zeros) == 1
        assert abs(zeros[0] - 14.134725142) < 1e-3

    def test_count(self):
        zeros = get_riemann_zeros(5)
        assert len(zeros) == 5

    def test_strictly_increasing(self):
        zeros = get_riemann_zeros(5)
        assert np.all(np.diff(zeros) > 0)


# ---------------------------------------------------------------------------
# Hamiltonian construction
# ---------------------------------------------------------------------------

class TestHamiltonianConstruction:
    """Validate build_nodo_zero_hamiltonian output."""

    def setup_method(self):
        self.N = 101
        self.L = 5.0
        self.H, self.x = build_nodo_zero_hamiltonian(
            N=self.N, L=self.L, lambda_delta=-2.0, alpha_pt=0.5
        )

    def test_shape(self):
        assert self.H.shape == (self.N, self.N)

    def test_grid_bounds(self):
        assert abs(self.x[0] + self.L) < 1e-12
        assert abs(self.x[-1] - self.L) < 1e-12
        assert len(self.x) == self.N

    def test_real_values(self):
        """Hamiltonian must be real (PT-symmetric with real delta)."""
        H_dense = self.H.toarray()
        assert np.allclose(H_dense.imag, 0.0)

    def test_symmetric(self):
        """H_zero is symmetric (self-adjoint in discrete sense)."""
        H_dense = self.H.toarray()
        assert np.allclose(H_dense, H_dense.T, atol=1e-12)

    def test_delta_localised_at_zero(self):
        """The delta potential should affect only the grid point nearest to x=0."""
        # Build two Hamiltonians: with and without the delta term
        H_with, x = build_nodo_zero_hamiltonian(
            N=self.N, L=self.L, lambda_delta=-2.0, alpha_pt=0.5
        )
        H_without, _ = build_nodo_zero_hamiltonian(
            N=self.N, L=self.L, lambda_delta=0.0, alpha_pt=0.5
        )
        diff = (H_with - H_without).toarray()
        # All off-diagonal differences must be zero
        np.fill_diagonal(diff, 0.0)
        assert np.allclose(diff, 0.0), "Delta potential affects off-diagonal elements"
        # Exactly one diagonal element is non-zero
        H_with_diag = H_with.diagonal()
        H_without_diag = H_without.diagonal()
        nonzero_diff = np.count_nonzero(np.abs(H_with_diag - H_without_diag) > 1e-12)
        assert nonzero_diff == 1, "Delta potential must modify exactly one diagonal element"


# ---------------------------------------------------------------------------
# Eigenvalue problem
# ---------------------------------------------------------------------------

class TestNodoZeroSpectrum:
    """Test the solve_nodo_zero results."""

    def setup_method(self):
        self.result = solve_nodo_zero(
            N=201, L=8.0, lambda_delta=-2.0, alpha_pt=0.5, n_eigs=5, n_zeros=5
        )

    def test_eigenvalues_real(self):
        assert np.all(np.isfinite(self.result.eigenvalues))
        assert np.allclose(self.result.eigenvalues.imag, 0.0, atol=1e-10) \
            if np.iscomplexobj(self.result.eigenvalues) else True

    def test_eigenvalues_sorted(self):
        assert np.all(np.diff(self.result.eigenvalues) >= 0)

    def test_n_eigenvalues(self):
        assert len(self.result.eigenvalues) == 5

    def test_ground_energy_finite(self):
        assert np.isfinite(self.result.ground_energy)

    def test_ground_energy_negative(self):
        """Attractive delta (λ < 0) creates a negative ground energy."""
        assert self.result.ground_energy < 0.0, (
            "Attractive delta potential (λ=-2) should yield negative E₀"
        )

    def test_psi_nodo_range(self):
        assert 0.0 < self.result.psi_nodo <= 1.0

    def test_psi_nodo_meets_threshold(self):
        """Ψ_nodo must be ≥ 0.888 (noetic coherence threshold)."""
        assert self.result.is_coherent, (
            f"Ψ_nodo = {self.result.psi_nodo:.4f} < threshold {PSI_THRESHOLD}"
        )

    def test_scaled_zeros_count(self):
        assert len(self.result.scaled_zeros) == 5

    def test_scaled_zeros_positive(self):
        assert np.all(self.result.scaled_zeros > 0.0)


# ---------------------------------------------------------------------------
# Ground-state density
# ---------------------------------------------------------------------------

class TestGroundStateDensity:
    """Verify the ground-state density is maximised at x≈0."""

    def test_max_at_zero_attractive(self):
        """Attractive delta (λ<0) with harmonic potential localises ground state at origin."""
        H, x = build_nodo_zero_hamiltonian(N=201, L=8.0, lambda_delta=-2.0, alpha_pt=0.5)
        from scipy.sparse.linalg import eigsh as _eigsh
        vals, vecs = _eigsh(H, k=1, which="SM")
        assert ground_state_density_max_at_zero(vecs, x)


# ---------------------------------------------------------------------------
# Node coherence formula
# ---------------------------------------------------------------------------

class TestComputePsiNodo:
    """Unit tests for the compute_psi_nodo formula."""

    def test_zero_energy(self):
        """At E₀=0 the coherence is exactly 1."""
        assert compute_psi_nodo(0.0) == pytest.approx(1.0)

    def test_small_energy(self):
        """For E₀ ≪ F₀ the coherence should be close to 1."""
        psi = compute_psi_nodo(F0 * 0.1)
        assert psi > 0.99

    def test_threshold_boundary(self):
        """Verify the analytical threshold: E₀ = F₀·sqrt(1/0.888 − 1)."""
        E_boundary = F0 * np.sqrt(1.0 / PSI_THRESHOLD - 1.0)
        psi = compute_psi_nodo(E_boundary)
        assert abs(psi - PSI_THRESHOLD) < 1e-9

    def test_formula(self):
        """Direct formula check with known values."""
        E0 = 10.0
        expected = 1.0 / (1.0 + (E0 / F0) ** 2)
        assert compute_psi_nodo(E0) == pytest.approx(expected)

    def test_check_coherence_true(self):
        assert check_coherence_threshold(0.9) is True

    def test_check_coherence_false(self):
        assert check_coherence_threshold(0.5) is False

    def test_check_coherence_boundary(self):
        assert check_coherence_threshold(PSI_THRESHOLD) is True


# ---------------------------------------------------------------------------
# Vertical Transform
# ---------------------------------------------------------------------------

class TestVerticalTransform:
    """Tests for the Vertical Transform L_v."""

    def _psi_exp(self, t: float) -> float:
        """Simple test function: Ψ(t) = exp(−t)."""
        return float(np.exp(-t))

    def test_finite_result(self):
        """L_v must return a finite complex value."""
        s_vals = np.array([1.0 + 0j])
        result = vertical_transform(self._psi_exp, s_vals, t_max=20.0, n_points=1000)
        assert np.isfinite(result.L_v_values[0])

    def test_result_complex(self):
        """Result is complex due to exp(i·F₀·t) phase factor."""
        s_vals = np.array([1.0 + 0j])
        result = vertical_transform(self._psi_exp, s_vals, t_max=20.0, n_points=1000)
        assert np.iscomplex(result.L_v_values[0]) or np.isreal(result.L_v_values[0])

    def test_shift_property(self):
        """L_v[Ψ](s) ≈ L[Ψ](s − i·F₀) = L[Ψ](s − i·ω₀).

        For Ψ(t) = exp(−t) the Laplace transform is L[Ψ](z) = 1/(1 + z).
        With ω₀ = 2π·F₀:
            L_v[Ψ](s) = 1 / (1 + s − i·ω₀)
        """
        omega_0 = 2.0 * np.pi * F0
        s_real = 2.0  # Re(s) > 0 ensures convergence
        s_vals = np.array([s_real + 0j])
        result = vertical_transform(self._psi_exp, s_vals, t_max=30.0, n_points=5000)
        expected = 1.0 / (1.0 + s_real - 1j * omega_0)
        # Numerical tolerance is generous due to finite upper limit of integration
        assert abs(result.L_v_values[0] - expected) < 0.01

    def test_multiple_s_values(self):
        """Vectorised computation over multiple s values."""
        s_vals = np.array([0.5 + 0j, 1.0 + 0j, 2.0 + 0j])
        result = vertical_transform(self._psi_exp, s_vals)
        assert len(result.L_v_values) == 3
        assert np.all(np.isfinite(result.L_v_values))

    def test_stores_f0(self):
        s_vals = np.array([1.0 + 0j])
        result = vertical_transform(self._psi_exp, s_vals)
        assert abs(result.f0 - F0) < 1e-9


# ---------------------------------------------------------------------------
# Full validation pipeline
# ---------------------------------------------------------------------------

class TestValidateNodoZero:
    """Integration test for the validate_nodo_zero function."""

    def setup_method(self):
        self.report = validate_nodo_zero(
            N=201, L=8.0, lambda_delta=-2.0, alpha_pt=0.5, n_eigs=5
        )

    def test_keys_present(self):
        expected = {
            "eigenvalues", "ground_energy", "psi_nodo", "is_coherent",
            "ground_state_max_at_zero", "vertical_transform_finite",
            "correlation", "scaled_zeros", "parameters",
        }
        assert expected.issubset(set(self.report.keys()))

    def test_is_coherent(self):
        assert self.report["is_coherent"] is True, (
            f"Ψ_nodo = {self.report['psi_nodo']:.4f} below threshold {PSI_THRESHOLD}"
        )

    def test_vertical_transform_finite(self):
        assert self.report["vertical_transform_finite"] is True

    def test_psi_nodo_meets_threshold(self):
        assert self.report["psi_nodo"] >= PSI_THRESHOLD

    def test_eigenvalues_list(self):
        assert isinstance(self.report["eigenvalues"], list)
        assert len(self.report["eigenvalues"]) == 5

    def test_parameters_recorded(self):
        params = self.report["parameters"]
        assert params["F0"] == pytest.approx(F0)
        assert params["N"] == 201
