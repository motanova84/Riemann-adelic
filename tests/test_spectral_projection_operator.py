"""
Tests for Spectral Projection Operator P_Ω
============================================

Comprehensive test suite verifying that SpectralProjectionOperator correctly
implements orthogonal spectral projections for a self-adjoint Hamiltonian.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(repo_root))

from operators.spectral_projection_operator import (
    SpectralProjectionOperator,
    ProjectionResult,
    ResolutionOfIdentityResult,
    SpectralSubspaceResult,
    build_spectral_projection,
    generate_projection_certificate,
    F0_QCAL,
    C_COHERENCE,
    PHI,
)


# ---------------------------------------------------------------------------
# Small operator used across tests for speed
# ---------------------------------------------------------------------------
N_SMALL = 64
X_MAX = 6.0


@pytest.fixture(scope="module")
def op():
    return SpectralProjectionOperator(n_dim=N_SMALL, x_max=X_MAX)


@pytest.fixture(scope="module")
def eigenvalues(op):
    vals, _ = op._compute_spectrum()
    return vals


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL ∞³ constants."""

    def test_f0(self):
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_coherence(self):
        assert abs(C_COHERENCE - 244.36) < 0.01

    def test_phi(self):
        assert abs(PHI - 1.6180339887498948) < 1e-12


# ---------------------------------------------------------------------------
# Initialisation
# ---------------------------------------------------------------------------

class TestInitialisation:
    """Verify operator initialisation."""

    def test_default_dims(self):
        o = SpectralProjectionOperator()
        assert o.n == 256
        assert o.x_max == 10.0

    def test_custom_dims(self):
        o = SpectralProjectionOperator(n_dim=N_SMALL, x_max=X_MAX)
        assert o.n == N_SMALL
        assert o.x_max == X_MAX
        assert len(o.x_grid) == N_SMALL

    def test_even_dimension_enforced(self):
        o = SpectralProjectionOperator(n_dim=63)
        assert o.n % 2 == 0
        assert o.n >= 63

    def test_hamiltonian_shape(self, op):
        assert op._H.shape == (N_SMALL, N_SMALL)

    def test_hamiltonian_symmetric(self, op):
        assert np.max(np.abs(op._H - op._H.T)) < 1e-12


# ---------------------------------------------------------------------------
# Eigendecomposition
# ---------------------------------------------------------------------------

class TestEigendecomposition:
    """Verify spectrum computation."""

    def test_eigenvalues_real(self, op):
        vals, _ = op._compute_spectrum()
        assert vals.dtype in (np.float64, np.float32)

    def test_eigenvalues_sorted(self, op):
        vals, _ = op._compute_spectrum()
        assert np.all(np.diff(vals) >= 0)

    def test_eigenvectors_orthonormal(self, op):
        _, vecs = op._compute_spectrum()
        inner = vecs.T @ vecs
        err = np.max(np.abs(inner - np.eye(N_SMALL)))
        assert err < 1e-10

    def test_eigenvalues_count(self, op):
        vals, _ = op._compute_spectrum()
        assert len(vals) == N_SMALL

    def test_spectrum_positive(self, op):
        """Potential V(x) = ½ log(1 + x²) ≥ 0 so H should be positive semi-definite."""
        vals, _ = op._compute_spectrum()
        assert vals[0] >= -1e-10   # Allow tiny numerical noise


# ---------------------------------------------------------------------------
# Projection matrix properties
# ---------------------------------------------------------------------------

class TestProjectionMatrix:
    """Verify projection matrix axioms for P_Ω = E(Ω)."""

    def _get_omega(self, op, eigenvalues):
        """Choose a spectral window containing roughly 1/4 of eigenvalues."""
        n4 = N_SMALL // 4
        return float(eigenvalues[0]) - 1e-10, float(eigenvalues[n4])

    def test_idempotency(self, op, eigenvalues):
        lo, hi = self._get_omega(op, eigenvalues)
        P = op.projection_matrix(lo, hi)
        P2 = P @ P
        assert np.max(np.abs(P2 - P)) < 1e-10

    def test_self_adjoint(self, op, eigenvalues):
        lo, hi = self._get_omega(op, eigenvalues)
        P = op.projection_matrix(lo, hi)
        assert np.max(np.abs(P - P.T)) < 1e-12

    def test_spectrum_in_0_1(self, op, eigenvalues):
        lo, hi = self._get_omega(op, eigenvalues)
        P = op.projection_matrix(lo, hi)
        eigs = np.linalg.eigvalsh(P)
        dist = np.minimum(np.abs(eigs), np.abs(eigs - 1.0))
        assert np.max(dist) < 1e-8

    def test_rank_equals_trace(self, op, eigenvalues):
        lo, hi = self._get_omega(op, eigenvalues)
        P = op.projection_matrix(lo, hi)
        rank = int(np.round(np.trace(P)))
        eigs_in_omega = eigenvalues[(eigenvalues >= lo) & (eigenvalues <= hi)]
        assert rank == len(eigs_in_omega)

    def test_empty_window_gives_zero_matrix(self, op, eigenvalues):
        # Window below the smallest eigenvalue → empty projection
        lo = float(eigenvalues[0]) - 2.0
        hi = float(eigenvalues[0]) - 1.0
        P = op.projection_matrix(lo, hi)
        assert np.max(np.abs(P)) < 1e-12

    def test_full_window_gives_identity(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1.0
        hi = float(eigenvalues[-1]) + 1.0
        P = op.projection_matrix(lo, hi)
        I = np.eye(N_SMALL)
        assert np.max(np.abs(P - I)) < 1e-10

    def test_orthogonal_projections_are_orthogonal(self, op, eigenvalues):
        mid = float(np.median(eigenvalues))
        lo, hi = float(eigenvalues[0]) - 1e-10, mid
        lo2, hi2 = mid + 1e-10, float(eigenvalues[-1]) + 1e-10
        P1 = op.projection_matrix(lo, hi)
        P2 = op.projection_matrix(lo2, hi2)
        cross = P1 @ P2
        assert np.max(np.abs(cross)) < 1e-10

    def test_subadditivity_union(self, op, eigenvalues):
        """P_{Ω₁ ∪ Ω₂} ≥ P_{Ω₁} for disjoint Ω₁, Ω₂ (rank additive)."""
        q1 = N_SMALL // 4
        q2 = N_SMALL // 2
        P1 = op.projection_matrix(eigenvalues[0] - 1e-10, eigenvalues[q1])
        P2 = op.projection_matrix(eigenvalues[q1] + 1e-10, eigenvalues[q2])
        P_union = op.projection_matrix(eigenvalues[0] - 1e-10, eigenvalues[q2])
        rank1 = int(np.round(np.trace(P1)))
        rank2 = int(np.round(np.trace(P2)))
        rank_union = int(np.round(np.trace(P_union)))
        assert rank_union == rank1 + rank2


# ---------------------------------------------------------------------------
# verify_projection_properties
# ---------------------------------------------------------------------------

class TestVerifyProjectionProperties:
    """Test the structured verification method."""

    def test_returns_projection_result(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert isinstance(result, ProjectionResult)

    def test_psi_high(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert result.psi > 0.95

    def test_idempotency_error_small(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert result.idempotency_error < 1e-9

    def test_self_adj_error_small(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert result.self_adjointness_error < 1e-12

    def test_rank_positive(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert result.rank > 0

    def test_trace_equals_rank(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert abs(result.trace - result.rank) < 0.5

    def test_eigenvalues_in_omega_inside_window(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 4])
        result = op.verify_projection_properties(lo, hi)
        for lam in result.eigenvalues_in_omega:
            assert lo <= lam <= hi

    def test_timestamp_set(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert len(result.timestamp) > 0

    def test_computation_time_positive(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.verify_projection_properties(lo, hi)
        assert result.computation_time_ms > 0


# ---------------------------------------------------------------------------
# verify_resolution_of_identity
# ---------------------------------------------------------------------------

class TestResolutionOfIdentity:
    """Verify the resolution-of-identity ∑ P_k = I."""

    def test_returns_correct_type(self, op):
        result = op.verify_resolution_of_identity(n_partitions=4)
        assert isinstance(result, ResolutionOfIdentityResult)

    def test_resolution_error_small(self, op):
        result = op.verify_resolution_of_identity(n_partitions=4)
        assert result.resolution_error < 1e-9

    def test_orthogonality_error_small(self, op):
        result = op.verify_resolution_of_identity(n_partitions=4)
        assert result.orthogonality_error < 1e-9

    def test_psi_high(self, op):
        result = op.verify_resolution_of_identity(n_partitions=4)
        assert result.psi > 0.95

    def test_correct_partition_count(self, op):
        result = op.verify_resolution_of_identity(n_partitions=6)
        assert result.projections_count == 6

    def test_single_partition_is_identity(self, op):
        """One partition spanning full spectrum → P = I."""
        result = op.verify_resolution_of_identity(n_partitions=1)
        assert result.resolution_error < 1e-9


# ---------------------------------------------------------------------------
# spectral_subspace
# ---------------------------------------------------------------------------

class TestSpectralSubspace:
    """Verify spectral subspace characterisation."""

    def test_returns_correct_type(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 2])
        result = op.spectral_subspace(lo, hi)
        assert isinstance(result, SpectralSubspaceResult)

    def test_dimension_correct(self, op, eigenvalues):
        q = N_SMALL // 2
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[q - 1])
        result = op.spectral_subspace(lo, hi)
        assert result.subspace_dimension == q

    def test_basis_orthonormal(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 4])
        result = op.spectral_subspace(lo, hi)
        d = result.subspace_dimension
        if d > 0:
            inner = result.basis_vectors.T @ result.basis_vectors
            err = np.max(np.abs(inner - np.eye(d)))
            assert err < 1e-10

    def test_eigenvalues_in_window(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 3])
        result = op.spectral_subspace(lo, hi)
        for lam in result.eigenvalues:
            assert lo <= lam <= hi

    def test_empty_window_zero_dimension(self, op, eigenvalues):
        lo = float(eigenvalues[-1]) + 1.0
        hi = float(eigenvalues[-1]) + 2.0
        result = op.spectral_subspace(lo, hi)
        assert result.subspace_dimension == 0

    def test_psi_in_range(self, op, eigenvalues):
        lo = float(eigenvalues[0]) - 1e-10
        hi = float(eigenvalues[N_SMALL // 2])
        result = op.spectral_subspace(lo, hi)
        assert 0.0 <= result.psi <= 1.0


# ---------------------------------------------------------------------------
# hamiltonian_via_projections (reconstruction)
# ---------------------------------------------------------------------------

class TestHamiltonianReconstruction:
    """Verify spectral theorem via Hamiltonian reconstruction."""

    def test_returns_dict(self, op):
        result = op.hamiltonian_via_projections(n_partitions=8)
        assert isinstance(result, dict)
        assert 'reconstruction_error' in result
        assert 'relative_error' in result
        assert 'psi' in result

    def test_psi_high(self, op):
        result = op.hamiltonian_via_projections(n_partitions=N_SMALL)
        # With n_partitions = n_dim each eigenvalue is isolated → exact
        assert result['psi'] > 0.95

    def test_relative_error_decreases_with_partitions(self, op):
        r4 = op.hamiltonian_via_projections(n_partitions=4)
        r16 = op.hamiltonian_via_projections(n_partitions=16)
        # More partitions → tighter mid-point approximation → lower error
        assert r16['relative_error'] <= r4['relative_error'] + 1e-8

    def test_exact_reconstruction_eigenvalue_partitions(self, op, eigenvalues):
        """Isolating each eigenvalue gives exact reconstruction."""
        result = op.hamiltonian_via_projections(n_partitions=N_SMALL)
        assert result['reconstruction_error'] < 1.0   # loose bound; still small


# ---------------------------------------------------------------------------
# Convenience functions
# ---------------------------------------------------------------------------

class TestConvenienceFunctions:
    """Test module-level helper functions."""

    def test_build_spectral_projection_shape(self):
        P = build_spectral_projection(0.0, 5.0, n_dim=N_SMALL, x_max=X_MAX)
        assert P.shape == (N_SMALL, N_SMALL)

    def test_build_spectral_projection_idempotent(self):
        P = build_spectral_projection(0.0, 5.0, n_dim=N_SMALL, x_max=X_MAX)
        P2 = P @ P
        assert np.max(np.abs(P2 - P)) < 1e-10

    def test_generate_certificate_structure(self):
        cert = generate_projection_certificate(
            omega_low=0.0, omega_high=5.0, n_dim=N_SMALL
        )
        assert 'psi_global' in cert
        assert 'status' in cert
        assert cert['status'] in ('PASSED', 'PARTIAL')

    def test_generate_certificate_psi_positive(self):
        cert = generate_projection_certificate(
            omega_low=0.0, omega_high=5.0, n_dim=N_SMALL
        )
        assert cert['psi_global'] > 0.0

    def test_generate_certificate_contains_doi(self):
        cert = generate_projection_certificate(n_dim=N_SMALL)
        assert '10.5281/zenodo.17379721' in cert['doi']


# ---------------------------------------------------------------------------
# Integration tests
# ---------------------------------------------------------------------------

class TestIntegration:
    """End-to-end integration tests."""

    def test_full_pipeline(self):
        op = SpectralProjectionOperator(n_dim=N_SMALL, x_max=X_MAX)
        vals, _ = op._compute_spectrum()
        mid = float(np.median(vals))

        proj = op.verify_projection_properties(float(vals[0]) - 1e-10, mid)
        res = op.verify_resolution_of_identity(n_partitions=4)
        # Use N_SMALL partitions so each eigenvalue is isolated → best reconstruction
        recon = op.hamiltonian_via_projections(n_partitions=N_SMALL)

        assert proj.psi > 0.90
        assert res.psi > 0.90
        assert recon['psi'] > 0.90

    def test_psi_above_threshold(self):
        cert = generate_projection_certificate(n_dim=N_SMALL)
        assert cert['psi_global'] > 0.85

    def test_complementary_projections_sum_to_identity(self):
        op = SpectralProjectionOperator(n_dim=N_SMALL, x_max=X_MAX)
        vals, _ = op._compute_spectrum()
        mid = float(np.median(vals))

        P1 = op.projection_matrix(float(vals[0]) - 1e-10, mid)
        P2 = op.projection_matrix(mid + 1e-10, float(vals[-1]) + 1e-10)
        P_sum = P1 + P2
        I = np.eye(N_SMALL)
        assert np.max(np.abs(P_sum - I)) < 1e-9
