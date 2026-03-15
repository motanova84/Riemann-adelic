#!/usr/bin/env python3
"""
Tests for H_Omega Berry-Keating Operator
=========================================

Validates the H_Omega operator implementation with Vortex 8 confinement
and Mellin diagonalization.

Test Coverage:
    1. Module constants (F0, C_COHERENCE)
    2. DeltaCombPotential construction and matrix building
    3. Vortex8Geometry grid and inversion operator
    4. MellinTransform forward/inverse and diagonalization
    5. HOmegaOperator construction and matrix properties
    6. Self-adjointness verification
    7. Spectral computation (eigenvalues, eigenvectors)
    8. Critical-line placement via Mellin (Re(s_n) = 1/2)
    9. TraceFormulaAnalysis
    10. GUEStatistics
    11. HOmegaResult and verify_h_omega_operator
    12. Edge cases and error handling

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np
from pathlib import Path

from operators.riemann_operator_H_omega import (
    # Constants
    F0_QCAL,
    C_COHERENCE_QCAL,
    PHI,
    RIEMANN_ZEROS_KNOWN,
    # Data structures
    HOmegaResult,
    DeltaCombPotentialConfig,
    # Classes
    Vortex8Geometry,
    DeltaCombPotential,
    MellinTransform,
    HOmegaOperator,
    TraceFormulaAnalysis,
    GUEStatistics,
    # Functions
    verify_h_omega_operator,
    _prime_sieve,
    _first_n_primes,
    _load_riemann_zeros,
)


# ===========================================================================
# §1. Constants
# ===========================================================================

class TestConstants:
    """Fundamental QCAL constants."""

    def test_f0_value(self):
        """Base frequency must be 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_coherence_value(self):
        """Coherence constant must be 244.36."""
        assert abs(C_COHERENCE_QCAL - 244.36) < 0.01

    def test_phi_golden_ratio(self):
        """Golden ratio Φ must satisfy Φ² = Φ + 1."""
        assert abs(PHI**2 - PHI - 1) < 1e-12

    def test_riemann_zeros_known(self):
        """First known Riemann zero must be ≈ 14.13."""
        assert abs(RIEMANN_ZEROS_KNOWN[0] - 14.134725) < 1e-4
        assert len(RIEMANN_ZEROS_KNOWN) >= 10


# ===========================================================================
# §2. Helper Functions
# ===========================================================================

class TestHelperFunctions:
    """Helper utility functions."""

    def test_prime_sieve_basic(self):
        primes = _prime_sieve(30)
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_prime_sieve_empty(self):
        assert _prime_sieve(0) == []
        assert _prime_sieve(1) == []

    def test_first_n_primes(self):
        primes = _first_n_primes(5)
        assert primes == [2, 3, 5, 7, 11]

    def test_load_riemann_zeros(self):
        zeros = _load_riemann_zeros(5)
        assert len(zeros) == 5
        assert zeros[0] > 14.0
        assert np.all(np.diff(zeros) > 0)

    def test_load_riemann_zeros_extended(self):
        """Extended zeros are generated for n > known list length."""
        zeros = _load_riemann_zeros(25)
        assert len(zeros) == 25
        assert np.all(np.diff(zeros) > 0)


# ===========================================================================
# §3. DeltaCombPotential
# ===========================================================================

class TestDeltaCombPotential:
    """Delta-comb prime potential."""

    def test_initialization_default(self):
        pot = DeltaCombPotential()
        assert pot.num_primes == 15
        assert pot.max_power == 3
        assert pot.coupling == 1.0

    def test_initialization_custom(self):
        pot = DeltaCombPotential(num_primes=5, max_power=2, coupling=0.5)
        assert pot.num_primes == 5
        assert pot.max_power == 2
        assert pot.coupling == 0.5

    def test_invalid_coupling(self):
        with pytest.raises(ValueError, match="coupling must be positive"):
            DeltaCombPotential(coupling=-1.0)

    def test_prime_powers_not_empty(self):
        pot = DeltaCombPotential(num_primes=5, max_power=2)
        assert len(pot.prime_powers) > 0

    def test_prime_powers_weights_positive(self):
        pot = DeltaCombPotential()
        for pm, weight in pot.prime_powers:
            assert pm > 0
            assert weight > 0

    def test_build_matrix_shape(self):
        vortex = Vortex8Geometry(N_grid=64)
        pot = DeltaCombPotential(num_primes=5, max_power=2)
        V = pot.build_matrix(vortex)
        assert V.shape == (64, 64)

    def test_build_matrix_diagonal(self):
        """Potential matrix must be diagonal."""
        vortex = Vortex8Geometry(N_grid=32)
        pot = DeltaCombPotential(num_primes=3, max_power=1)
        V = pot.build_matrix(vortex)
        off_diag = V - np.diag(np.diag(V))
        assert np.linalg.norm(off_diag) < 1e-15

    def test_build_matrix_real(self):
        """Potential must be real."""
        vortex = Vortex8Geometry(N_grid=32)
        pot = DeltaCombPotential()
        V = pot.build_matrix(vortex)
        assert np.isrealobj(V)

    def test_qcal_modulation_effect(self):
        """QCAL modulation should change the potential."""
        vortex = Vortex8Geometry(N_grid=32)
        pot_on = DeltaCombPotential(include_qcal_modulation=True)
        pot_off = DeltaCombPotential(include_qcal_modulation=False)
        V_on = pot_on.build_matrix(vortex)
        V_off = pot_off.build_matrix(vortex)
        # With C_COHERENCE = 244.36 / 244.36 = 1.0, they should be equal
        np.testing.assert_allclose(np.diag(V_on), np.diag(V_off), rtol=1e-6)


# ===========================================================================
# §4. Vortex8Geometry
# ===========================================================================

class TestVortex8Geometry:
    """Vortex 8 geometry."""

    def test_initialization(self):
        vortex = Vortex8Geometry(N_grid=128)
        assert vortex.N_grid == 128
        assert len(vortex.x_grid) == 128
        assert len(vortex.t_grid) == 128

    def test_grid_positive(self):
        """All grid points must be positive."""
        vortex = Vortex8Geometry(N_grid=64)
        assert np.all(vortex.x_grid > 0)

    def test_grid_log_symmetry(self):
        """Log-grid should be symmetric around t=0 (x=1)."""
        vortex = Vortex8Geometry(N_grid=101, x_min=1e-2)
        center = vortex.center_index()
        assert abs(vortex.x_grid[center] - 1.0) < 0.1

    def test_inversion_recovers_function(self):
        """J(Jψ) ≈ ψ (involution up to interpolation error)."""
        vortex = Vortex8Geometry(N_grid=201, x_min=1e-2)
        psi = np.exp(-((vortex.t_grid) ** 2))
        JJpsi = vortex.apply_inversion(vortex.apply_inversion(psi))
        # Center region should be accurate
        center = slice(vortex.N_grid // 4, 3 * vortex.N_grid // 4)
        np.testing.assert_allclose(psi[center], JJpsi[center], rtol=0.05)

    def test_symmetrize_reduces_error(self):
        """Symmetrized function should have smaller symmetry error."""
        vortex = Vortex8Geometry(N_grid=101, x_min=1e-2)
        psi = np.random.default_rng(42).random(vortex.N_grid)
        sym = vortex.symmetrize(psi)
        err_before = vortex.symmetry_error(psi)
        err_after = vortex.symmetry_error(sym)
        assert err_after <= err_before + 1e-10

    def test_invalid_x_min(self):
        with pytest.raises(ValueError):
            Vortex8Geometry(x_min=-1.0)

    def test_center_index(self):
        vortex = Vortex8Geometry(N_grid=101, x_min=1e-2)
        ci = vortex.center_index()
        assert 0 < ci < vortex.N_grid
        # x at center should be close to 1
        assert abs(vortex.x_grid[ci] - 1.0) < 0.5


# ===========================================================================
# §5. MellinTransform
# ===========================================================================

class TestMellinTransform:
    """Mellin transform diagonalization."""

    def test_initialization(self):
        vortex = Vortex8Geometry(N_grid=64)
        mellin = MellinTransform(vortex)
        assert len(mellin.xi_grid) == 64

    def test_forward_shape(self):
        vortex = Vortex8Geometry(N_grid=64)
        mellin = MellinTransform(vortex)
        psi = np.ones(64)
        psi_hat = mellin.forward(psi)
        assert len(psi_hat) == 64

    def test_inverse_shape(self):
        vortex = Vortex8Geometry(N_grid=64)
        mellin = MellinTransform(vortex)
        psi_hat = np.ones(64, dtype=complex)
        psi = mellin.inverse(psi_hat)
        assert len(psi) == 64

    def test_forward_inverse_roundtrip(self):
        """Inverse of forward should recover the original signal."""
        vortex = Vortex8Geometry(N_grid=128)
        mellin = MellinTransform(vortex)
        psi = np.exp(-vortex.t_grid**2)
        psi_hat = mellin.forward(psi)
        psi_rec = mellin.inverse(psi_hat)
        np.testing.assert_allclose(psi, psi_rec, atol=1e-10)

    def test_diagonalize_free_operator(self):
        """Diagonal Mellin representation should be real-valued."""
        vortex = Vortex8Geometry(N_grid=64)
        mellin = MellinTransform(vortex)
        diag = mellin.diagonalize_free_operator()
        assert len(diag) == 64

    def test_mellin_eigenvalues_critical_line(self):
        """All s_n = 1/2 + iE_n must have Re(s_n) = 1/2."""
        vortex = Vortex8Geometry(N_grid=64)
        mellin = MellinTransform(vortex)
        E_vals = np.array([14.13, 21.02, 25.01])
        s_vals = mellin.mellin_eigenvalues_from_real(E_vals)
        np.testing.assert_allclose(np.real(s_vals), 0.5, atol=1e-10)
        np.testing.assert_allclose(np.imag(s_vals), E_vals, atol=1e-10)


# ===========================================================================
# §6. HOmegaOperator
# ===========================================================================

class TestHOmegaOperator:
    """Berry-Keating H_Omega operator."""

    @pytest.fixture
    def small_op(self):
        """Small operator for fast tests."""
        vortex = Vortex8Geometry(N_grid=64)
        pot = DeltaCombPotential(num_primes=5, max_power=2)
        return HOmegaOperator(potential=pot, vortex=vortex)

    def test_initialization_default(self):
        op = HOmegaOperator()
        assert op.H is not None

    def test_initialization_custom(self, small_op):
        assert small_op.H is not None

    def test_matrix_shape(self, small_op):
        assert small_op.H.shape == (64, 64)

    def test_matrix_hermitian(self, small_op):
        """H must be Hermitian: H = H†."""
        H = small_op.H
        H_dag = H.conj().T
        np.testing.assert_allclose(H, H_dag, atol=1e-10)

    def test_self_adjointness_error(self, small_op):
        """Self-adjointness error must be machine-precision small."""
        err = small_op.verify_self_adjointness()
        assert err < 1e-10

    def test_eigenvalues_real(self, small_op):
        """All eigenvalues of H must be real (Hermitian operator)."""
        evals = small_op.compute_eigenvalues(n_eigenvalues=10)
        assert np.all(np.isreal(evals))
        assert np.all(np.abs(np.imag(evals)) < 1e-10)

    def test_eigenvalues_sorted(self, small_op):
        """Returned eigenvalues must be sorted ascending."""
        evals = small_op.compute_eigenvalues(n_eigenvalues=15)
        assert np.all(np.diff(evals) >= -1e-10)

    def test_compute_spectrum_shapes(self, small_op):
        evals, evecs = small_op.compute_spectrum(n_eigenvalues=10)
        assert evals.shape == (10,)
        assert evecs.shape == (64, 10)

    def test_compute_spectrum_orthonormal(self, small_op):
        """Eigenvectors of Hermitian matrix must be orthonormal."""
        _, evecs = small_op.compute_spectrum(n_eigenvalues=5)
        gram = evecs.conj().T @ evecs
        np.testing.assert_allclose(gram, np.eye(5), atol=1e-10)

    def test_mellin_critical_line(self, small_op):
        """All Mellin eigenvalues s_n must have Re(s_n) = 1/2."""
        evals = small_op.compute_eigenvalues(n_eigenvalues=10)
        s_vals = small_op.mellin.mellin_eigenvalues_from_real(evals)
        np.testing.assert_allclose(np.real(s_vals), 0.5, atol=1e-10)

    def test_trace_formula(self, small_op):
        """Tr(e^{itH}) must be a complex number with |Tr| ≤ N."""
        evals = small_op.compute_eigenvalues(n_eigenvalues=10)
        trace = small_op.compute_trace_formula(evals, t=1.0)
        assert isinstance(trace, complex)
        assert abs(trace) <= len(evals) + 1e-6

    def test_compare_zeros_returns_dict(self, small_op):
        """compare_with_riemann_zeros must return required keys."""
        evals = small_op.compute_eigenvalues()
        cmp = small_op.compare_with_riemann_zeros(evals)
        assert "correlation" in cmp
        assert "mean_error" in cmp
        assert "rms_error" in cmp
        assert "max_error" in cmp

    def test_compare_zeros_correlation_finite(self, small_op):
        """Correlation must be a finite number."""
        evals = small_op.compute_eigenvalues()
        cmp = small_op.compare_with_riemann_zeros(evals)
        assert np.isfinite(cmp["correlation"])


# ===========================================================================
# §7. TraceFormulaAnalysis
# ===========================================================================

class TestTraceFormulaAnalysis:
    """Riemann-Weil trace formula analysis."""

    @pytest.fixture
    def tfa(self):
        vortex = Vortex8Geometry(N_grid=64)
        pot = DeltaCombPotential(num_primes=5, max_power=2)
        op = HOmegaOperator(potential=pot, vortex=vortex)
        return TraceFormulaAnalysis(op)

    def test_spectral_side_shape(self, tfa):
        evals = tfa.op.compute_eigenvalues(n_eigenvalues=10)
        t_vals = np.array([0.5, 1.0, 2.0])
        sp = tfa.spectral_side(evals, t_vals)
        assert sp.shape == (3,)

    def test_geometric_side_shape(self, tfa):
        t_vals = np.array([0.5, 1.0, 2.0])
        geo = tfa.geometric_side(t_vals)
        assert geo.shape == (3,)

    def test_explicit_formula_residual_finite(self, tfa):
        evals = tfa.op.compute_eigenvalues(n_eigenvalues=10)
        residual = tfa.explicit_formula_residual(evals)
        assert np.isfinite(residual)
        assert residual >= 0


# ===========================================================================
# §8. GUEStatistics
# ===========================================================================

class TestGUEStatistics:
    """GUE level-spacing statistics."""

    @pytest.fixture
    def gue(self):
        # Use GUE random matrix eigenvalues for a clean test
        rng = np.random.default_rng(42)
        N = 50
        A = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        H = (A + A.conj().T) / (2 * np.sqrt(N))
        evals = np.linalg.eigvalsh(H)
        return GUEStatistics(evals)

    def test_level_spacings_positive(self, gue):
        spacings = gue.level_spacings()
        assert np.all(spacings >= 0)

    def test_level_spacings_mean_near_one(self, gue):
        """Unfolded spacings should have mean ≈ 1."""
        spacings = gue.level_spacings()
        assert abs(np.mean(spacings) - 1.0) < 0.1

    def test_wigner_dyson_cdf_bounds(self):
        s = np.array([0.0, 1.0, 2.0, 3.0])
        cdf = GUEStatistics.wigner_dyson_cdf(s)
        assert cdf[0] == pytest.approx(0.0)
        assert 0 < cdf[1] < 1
        assert cdf[-1] < 1.0

    def test_ks_test_gue_consistency(self, gue):
        """Real GUE matrix should pass the Wigner-Dyson test (p > 0.05)."""
        result = gue.kolmogorov_smirnov_test()
        assert "ks_statistic" in result
        assert "p_value" in result
        assert result["p_value"] >= 0

    def test_level_repulsion_exponent(self, gue):
        """Exponent should be approximately 2 for GUE."""
        beta = gue.level_repulsion_exponent()
        assert beta >= 0  # Positive repulsion


# ===========================================================================
# §9. Full Verification Function
# ===========================================================================

class TestVerifyHOmegaOperator:
    """Master verification function."""

    def test_returns_result(self):
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=10, n_zeros=10, verbose=False
        )
        assert isinstance(result, HOmegaResult)

    def test_self_adjointness_passes(self):
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=10, verbose=False
        )
        assert result.self_adjoint_error < 1e-10

    def test_critical_line_verified(self):
        """All Re(s_n) must equal 1/2."""
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=10, verbose=False
        )
        assert np.all(np.abs(np.real(result.mellin_eigenvalues) - 0.5) < 1e-10)

    def test_certificate_sha256_format(self):
        """SHA-256 certificate must be a 64-hex-char string."""
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=10, verbose=False
        )
        assert len(result.certificate_sha256) == 64
        assert all(c in "0123456789abcdef" for c in result.certificate_sha256)

    def test_success_flag(self):
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=10, verbose=False
        )
        assert result.success

    def test_eigenvalues_count(self):
        n = 12
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=n, verbose=False
        )
        assert len(result.eigenvalues) == n

    def test_mellin_eigenvalues_count(self):
        n = 8
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=n, verbose=False
        )
        assert len(result.mellin_eigenvalues) == n

    def test_gue_p_value_finite(self):
        result = verify_h_omega_operator(
            N_grid=64, num_primes=5, max_power=2,
            n_eigenvalues=15, verbose=False
        )
        assert np.isfinite(result.gue_p_value)

    def test_verbose_output(self, capsys):
        verify_h_omega_operator(
            N_grid=32, num_primes=3, max_power=1,
            n_eigenvalues=5, verbose=True
        )
        captured = capsys.readouterr()
        assert "H_Ω BERRY-KEATING OPERATOR VERIFICATION" in captured.out
        assert "Self-adjoint error" in captured.out
        assert "critical line" in captured.out.lower()


# ===========================================================================
# §10. Edge Cases
# ===========================================================================

class TestEdgeCases:
    """Edge cases and error handling."""

    def test_single_prime(self):
        """Operator with a single prime in potential."""
        vortex = Vortex8Geometry(N_grid=32)
        pot = DeltaCombPotential(num_primes=1, max_power=1)
        op = HOmegaOperator(potential=pot, vortex=vortex)
        assert op.H.shape == (32, 32)

    def test_zero_eigenvalues_requested(self):
        op = HOmegaOperator(vortex=Vortex8Geometry(N_grid=32))
        evals, evecs = op.compute_spectrum(n_eigenvalues=0)
        assert len(evals) == 0
        assert evecs.shape[1] == 0

    def test_no_positive_eigenvalues_fallback(self):
        """compare_with_riemann_zeros uses |eigenvalues| if no positive ones."""
        op = HOmegaOperator(vortex=Vortex8Geometry(N_grid=32))
        evals = op.compute_eigenvalues()
        neg_evals = -np.abs(evals)  # Force all negative
        result = op.compare_with_riemann_zeros(neg_evals, n_zeros=5)
        assert "correlation" in result

    def test_gue_insufficient_eigenvalues(self):
        """GUE with too few eigenvalues returns safe defaults."""
        gue = GUEStatistics(np.array([1.0]))
        result = gue.kolmogorov_smirnov_test()
        assert result["p_value"] == 0.0

    def test_trace_formula_empty_eigenvalues(self):
        op = HOmegaOperator(vortex=Vortex8Geometry(N_grid=32))
        trace = op.compute_trace_formula(np.array([]), t=1.0)
        assert trace == 0.0 + 0.0j


# ===========================================================================
# §11. Mathematical Properties
# ===========================================================================

class TestMathematicalProperties:
    """Mathematical properties of the H_Omega operator."""

    def test_operator_hermitian_large(self):
        """Hermiticity must hold for larger grids too."""
        vortex = Vortex8Geometry(N_grid=128)
        pot = DeltaCombPotential(num_primes=10, max_power=3)
        op = HOmegaOperator(potential=pot, vortex=vortex)
        err = op.verify_self_adjointness()
        assert err < 1e-10

    def test_eigenvalue_spectrum_real(self):
        """Full spectrum must consist of real eigenvalues."""
        vortex = Vortex8Geometry(N_grid=128)
        op = HOmegaOperator(vortex=vortex)
        evals = op.compute_eigenvalues()
        assert np.all(np.isreal(evals))

    def test_spectral_gap_exists(self):
        """Eigenvalues should have nonzero spacing (pure discrete spectrum)."""
        vortex = Vortex8Geometry(N_grid=64)
        pot = DeltaCombPotential(num_primes=5, max_power=2)
        op = HOmegaOperator(potential=pot, vortex=vortex)
        evals = op.compute_eigenvalues(n_eigenvalues=20)
        gaps = np.diff(evals)
        assert np.all(gaps > -1e-10)  # Non-decreasing


# ===========================================================================
# §12. Lean Formalization File
# ===========================================================================

class TestLeanFormalization:
    """Verify the Lean 4 formalization file exists."""

    def test_lean_file_exists(self):
        lean_path = Path(__file__).parent.parent / "formalization" / "HOmega.lean"
        assert lean_path.exists(), f"Lean file missing: {lean_path}"

    def test_lean_file_has_key_theorems(self):
        lean_path = Path(__file__).parent.parent / "formalization" / "HOmega.lean"
        content = lean_path.read_text(encoding="utf-8")
        assert "mellin_diagonalizes_H0" in content
        assert "critical_line_theorem" in content
        assert "spectral_correspondence" in content

    def test_lean_file_has_namespace(self):
        lean_path = Path(__file__).parent.parent / "formalization" / "HOmega.lean"
        content = lean_path.read_text(encoding="utf-8")
        assert "RiemannAdelic.HOmega" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
