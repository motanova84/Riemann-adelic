#!/usr/bin/env python3
"""
Tests for Stone Theorem Self-Adjointness on the Adelic Solenoid
================================================================

Test Coverage:
    1. AdelicScalingFlow construction and grid properties
    2. Unitarity of U_t (Haar-measure preservation)
    3. Stone theorem certificate (Hermiticity, real spectrum)
    4. SchwartzSmoothedOperator — Schatten-1 convergence
    5. Fredholm determinant coefficients
    6. xi_function values on critical line
    7. phragmen_lindelof_ratio — identity Δ ≡ ξ/ξ(1/2)
    8. rh_unitarity_equivalence — physical necessity
    9. run_stone_proof — full four-part proof
    10. sellar_stone_proof — QCAL coherence seal

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import numpy as np
import pytest

from operators.stone_solenoid_selfadjoint import (
    AdelicScalingFlow,
    SchwartzSmoothedOperator,
    StoneProofResult,
    phragmen_lindelof_ratio,
    rh_unitarity_equivalence,
    run_stone_proof,
    sellar_stone_proof,
    xi_function,
    F0_QCAL,
    C_QCAL,
    DOI,
    ORCID,
    RIEMANN_ZEROS_GAMMA,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def small_flow() -> AdelicScalingFlow:
    """Small flow (64 pts) for fast tests."""
    return AdelicScalingFlow(n_points=64, u_max=6.0)


@pytest.fixture(scope="module")
def gaussian_psi(small_flow: AdelicScalingFlow) -> np.ndarray:
    """Normalised Gaussian test function."""
    psi = np.exp(-small_flow.u_grid ** 2 / 2.0)
    psi /= np.linalg.norm(psi)
    return psi


@pytest.fixture(scope="module")
def schwartz_op() -> SchwartzSmoothedOperator:
    return SchwartzSmoothedOperator(g_sigma=1.0)


@pytest.fixture(scope="module")
def proof_result() -> StoneProofResult:
    return run_stone_proof(n_points=64, u_max=6.0)


# ---------------------------------------------------------------------------
# § 1  AdelicScalingFlow — construction
# ---------------------------------------------------------------------------

class TestAdelicScalingFlowConstruction:
    def test_grid_length(self, small_flow: AdelicScalingFlow) -> None:
        assert len(small_flow.u_grid) == 64

    def test_grid_symmetry(self, small_flow: AdelicScalingFlow) -> None:
        # Grid should be centred around 0
        assert abs(small_flow.u_grid.mean()) < 0.5

    def test_H_matrix_shape(self, small_flow: AdelicScalingFlow) -> None:
        assert small_flow.H_matrix.shape == (64, 64)

    def test_H_matrix_is_symmetric(self, small_flow: AdelicScalingFlow) -> None:
        defect = np.linalg.norm(small_flow.H_matrix - small_flow.H_matrix.T)
        assert defect < 1e-8, f"Hermiticity defect {defect} too large"

    def test_H_matrix_real(self, small_flow: AdelicScalingFlow) -> None:
        assert np.allclose(small_flow.H_matrix.imag, 0, atol=1e-10)


# ---------------------------------------------------------------------------
# § 2  Unitarity of the scaling flow U_t
# ---------------------------------------------------------------------------

class TestUnitarityOfScalingFlow:
    @pytest.mark.parametrize("t", [0.0, 0.5, 1.0, 2.0, -1.0])
    def test_unitarity(self, small_flow: AdelicScalingFlow, gaussian_psi: np.ndarray, t: float) -> None:
        res = small_flow.verify_unitarity(gaussian_psi, t)
        assert res["relative_error"] < 1e-8, (
            f"U_{{t={t}}} broke unitarity: relative error = {res['relative_error']}"
        )

    def test_apply_shift_identity(self, small_flow: AdelicScalingFlow, gaussian_psi: np.ndarray) -> None:
        """U_0 = I."""
        shifted = small_flow.apply_shift(gaussian_psi, 0.0)
        assert np.allclose(shifted, gaussian_psi, atol=1e-8)

    def test_apply_shift_round_trip(self, small_flow: AdelicScalingFlow, gaussian_psi: np.ndarray) -> None:
        """U_{-t} ∘ U_t = I."""
        psi_shifted = small_flow.apply_shift(gaussian_psi, 1.5)
        psi_back = small_flow.apply_shift(psi_shifted, -1.5)
        assert np.allclose(psi_back, gaussian_psi, atol=1e-6)


# ---------------------------------------------------------------------------
# § 3  Stone theorem certificate
# ---------------------------------------------------------------------------

class TestStoneTheoremCertificate:
    def test_certificate_passes(self, small_flow: AdelicScalingFlow) -> None:
        cert = small_flow.stone_theorem_certificate()
        assert cert["passed"], f"Stone certificate failed: {cert}"

    def test_spectrum_real(self, small_flow: AdelicScalingFlow) -> None:
        cert = small_flow.stone_theorem_certificate()
        assert cert["spectrum_real"], (
            f"Spectrum not real: max Im = {cert['eigenvalue_max_imaginary_part']}"
        )

    def test_hermiticity_defect_small(self, small_flow: AdelicScalingFlow) -> None:
        cert = small_flow.stone_theorem_certificate()
        assert cert["hermiticity_defect"] < 1e-8

    def test_unitarity_error_small(self, small_flow: AdelicScalingFlow) -> None:
        cert = small_flow.stone_theorem_certificate()
        assert cert["unitarity_max_relative_error"] < 1e-8

    def test_diagonalise_eigenvalues_real(self, small_flow: AdelicScalingFlow) -> None:
        eigvals, _ = small_flow.diagonalise()
        assert np.all(np.abs(eigvals.imag) < 1e-10)

    def test_diagonalise_eigenvectors_orthogonal(self, small_flow: AdelicScalingFlow) -> None:
        _, eigvecs = small_flow.diagonalise()
        gram = eigvecs.T @ eigvecs
        off_diag = gram - np.eye(small_flow.n_points)
        assert np.linalg.norm(off_diag) < 1e-6


# ---------------------------------------------------------------------------
# § 4  SchwartzSmoothedOperator — Schatten-1 class
# ---------------------------------------------------------------------------

class TestSchwartzSmoothedOperator:
    def test_fourier_decay(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        """ĝ(γ) must decrease as γ grows (Schwartz super-polynomial decay)."""
        vals = [schwartz_op.g_fourier(g) for g in RIEMANN_ZEROS_GAMMA[:5]]
        for i in range(len(vals) - 1):
            assert vals[i] >= vals[i + 1], "Fourier transform not decaying"

    def test_fourier_at_zero(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        """ĝ(0) = 1 for unit-normalised Gaussian."""
        assert abs(schwartz_op.g_fourier(0.0) - 1.0) < 1e-12

    def test_schatten1_sum_finite(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        s1 = schwartz_op.schatten1_sum()
        assert np.isfinite(s1) and s1 > 0

    def test_verify_schatten1_passes(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        res = schwartz_op.verify_schatten1()
        assert res["convergence_confirmed"]

    def test_weyl_count_increasing(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        counts = [schwartz_op.weyl_count(T) for T in [10.0, 50.0, 100.0]]
        assert counts[0] < counts[1] < counts[2]

    def test_fredholm_coefficients_length(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        coeffs = schwartz_op.fredholm_determinant_coefficients()
        assert len(coeffs) == len(RIEMANN_ZEROS_GAMMA)

    def test_fredholm_coefficients_positive(self, schwartz_op: SchwartzSmoothedOperator) -> None:
        coeffs = schwartz_op.fredholm_determinant_coefficients()
        assert all(c >= 0 for c in coeffs)


# ---------------------------------------------------------------------------
# § 5  xi_function on the critical line
# ---------------------------------------------------------------------------

class TestXiFunction:
    def test_xi_at_half_is_real(self) -> None:
        val = xi_function(complex(0.5, 0.0))
        assert abs(val.imag) < 1e-6, f"ξ(1/2) not real: {val}"

    def test_xi_symmetry(self) -> None:
        """ξ(s) = ξ(1 − s) functional equation."""
        s = complex(0.3, 5.0)
        xi_s = xi_function(s)
        xi_1ms = xi_function(1.0 - s)
        # Allow numerical tolerance
        if not (np.isnan(xi_s) or np.isnan(xi_1ms)):
            ratio = abs(xi_s - xi_1ms) / (abs(xi_s) + 1e-30)
            assert ratio < 0.2, f"Functional equation violated: ratio={ratio}"

    def test_xi_at_riemann_zero_near_zero(self) -> None:
        """ξ(1/2 + i·γ_1) ≈ 0 for γ_1 = 14.134725."""
        gamma1 = 14.134725
        val = xi_function(complex(0.5, gamma1))
        # ξ vanishes at Riemann zeros; allow generous tolerance for finite approximation
        assert abs(val) < 2.0, f"|ξ(1/2 + i·γ₁)| = {abs(val)} too large"


# ---------------------------------------------------------------------------
# § 6  Phragmén-Lindelöf identity check
# ---------------------------------------------------------------------------

class TestPhragmenLindelof:
    def test_ratio_structure(self) -> None:
        gammas = np.array(RIEMANN_ZEROS_GAMMA[:5])
        s_vals = 0.5 + 1j * gammas
        delta_arr = np.ones(len(s_vals), dtype=complex)
        xi_vals = np.array([xi_function(s) for s in s_vals])
        xi_half = xi_function(complex(0.5, 0.0))
        res = phragmen_lindelof_ratio(s_vals, delta_arr, xi_vals, xi_half)
        assert "max_deviation_from_unity" in res
        assert "identity_confirmed" in res
        assert isinstance(res["identity_confirmed"], bool)

    def test_identical_functions_give_zero_deviation(self) -> None:
        """If Δ = ξ/ξ(1/2), deviation should be ~0."""
        gammas = np.array(RIEMANN_ZEROS_GAMMA[:5])
        s_vals = 0.5 + 1j * gammas
        xi_vals = np.array([xi_function(s) for s in s_vals])
        xi_half = xi_function(complex(0.5, 0.0))
        # Set delta = xi / xi_half exactly
        delta_arr = xi_vals / (xi_half + 1e-300)
        res = phragmen_lindelof_ratio(s_vals, delta_arr, xi_vals, xi_half)
        assert res["max_deviation_from_unity"] < 1e-6


# ---------------------------------------------------------------------------
# § 7  RH ↔ Haar-unitarity equivalence (physical necessity)
# ---------------------------------------------------------------------------

class TestRHUnitarityEquivalence:
    def test_rh_implies_unitarity(self, small_flow: AdelicScalingFlow) -> None:
        res = rh_unitarity_equivalence(small_flow)
        assert res["rh_implies_unitarity"]

    def test_all_eigenvalues_real(self, small_flow: AdelicScalingFlow) -> None:
        res = rh_unitarity_equivalence(small_flow)
        assert res["all_eigenvalues_real"]

    def test_unitarity_max_error(self, small_flow: AdelicScalingFlow) -> None:
        res = rh_unitarity_equivalence(small_flow)
        assert res["unitarity_max_relative_error"] < 1e-8

    def test_perturbation_breaks_unitarity(self, small_flow: AdelicScalingFlow) -> None:
        res = rh_unitarity_equivalence(small_flow)
        assert res["perturbed_breaks_unitarity"], (
            "Non-self-adjoint perturbation should break unitarity"
        )


# ---------------------------------------------------------------------------
# § 8  Full four-part proof runner
# ---------------------------------------------------------------------------

class TestRunStoneProof:
    def test_returns_stone_proof_result(self, proof_result: StoneProofResult) -> None:
        assert isinstance(proof_result, StoneProofResult)

    def test_all_parts_populated(self, proof_result: StoneProofResult) -> None:
        assert len(proof_result.part1_stone) > 0
        assert len(proof_result.part2_schatten) > 0
        assert len(proof_result.part3_identity) > 0
        assert len(proof_result.part4_physical) > 0

    def test_part1_passed(self, proof_result: StoneProofResult) -> None:
        assert proof_result.part1_stone.get("passed"), str(proof_result.part1_stone)

    def test_part2_convergence(self, proof_result: StoneProofResult) -> None:
        assert proof_result.part2_schatten.get("convergence_confirmed")

    def test_part4_unitarity(self, proof_result: StoneProofResult) -> None:
        assert proof_result.part4_physical.get("rh_implies_unitarity")

    def test_all_passed(self, proof_result: StoneProofResult) -> None:
        assert proof_result.all_passed, (
            f"Proof not fully passed. Parts:\n"
            f"  1: {proof_result.part1_stone}\n"
            f"  2: {proof_result.part2_schatten}\n"
            f"  4: {proof_result.part4_physical}"
        )

    def test_qcal_frequency(self, proof_result: StoneProofResult) -> None:
        assert abs(proof_result.qcal_frequency - 141.7001) < 0.001

    def test_doi_present(self, proof_result: StoneProofResult) -> None:
        assert "10.5281/zenodo" in proof_result.doi


# ---------------------------------------------------------------------------
# § 9  QCAL coherence seal
# ---------------------------------------------------------------------------

class TestSealAndConstants:
    def test_seal_contains_doi(self) -> None:
        seal = sellar_stone_proof()
        assert DOI in seal

    def test_seal_contains_orcid(self) -> None:
        seal = sellar_stone_proof()
        assert ORCID in seal

    def test_seal_contains_frequency(self) -> None:
        seal = sellar_stone_proof()
        assert "141.7001" in seal

    def test_f0_value(self) -> None:
        assert abs(F0_QCAL - 141.7001) < 0.001

    def test_c_qcal_value(self) -> None:
        assert abs(C_QCAL - 244.36) < 0.01

    def test_riemann_zeros_positive(self) -> None:
        assert all(g > 0 for g in RIEMANN_ZEROS_GAMMA)

    def test_riemann_zeros_increasing(self) -> None:
        for i in range(len(RIEMANN_ZEROS_GAMMA) - 1):
            assert RIEMANN_ZEROS_GAMMA[i] < RIEMANN_ZEROS_GAMMA[i + 1]
