#!/usr/bin/env python3
"""
Tests for QCAL String Core
===========================

60 tests covering:
- QCALStringOperator construction and validation
- modulation_potential / compute_eigenvalue / certify_critical_line
- GAMMAS list
- build_lambda_list / build_spectral_grid
- compute_psi
- string_noetic_forcing
- rk4_step incompressibility
- root-level qcal_string_core re-export surface

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import math

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Primary import path
# ---------------------------------------------------------------------------
from qcal.string_core import (
    GAMMAS,
    QCALStringOperator,
    build_lambda_list,
    build_spectral_grid,
    compute_psi,
    rk4_step,
    string_noetic_forcing,
)


# ===========================================================================
# 1. GAMMAS
# ===========================================================================

class TestGammas:
    def test_gammas_length(self):
        assert len(GAMMAS) == 20

    def test_gammas_type(self):
        for g in GAMMAS:
            assert isinstance(g, float)

    def test_gammas_positive(self):
        for g in GAMMAS:
            assert g > 0.0

    def test_gammas_first(self):
        assert abs(GAMMAS[0] - 14.134725141734693) < 1e-9

    def test_gammas_second(self):
        assert abs(GAMMAS[1] - 21.022039638771554) < 1e-9

    def test_gammas_strictly_increasing(self):
        for i in range(len(GAMMAS) - 1):
            assert GAMMAS[i] < GAMMAS[i + 1]

    def test_gammas_last_gt_70(self):
        # 20th zero is > 70
        assert GAMMAS[-1] > 70.0


# ===========================================================================
# 2. QCALStringOperator construction
# ===========================================================================

class TestQCALStringOperatorConstruction:
    def test_default_f0(self):
        op = QCALStringOperator()
        assert op.f0 == pytest.approx(141.7001, abs=1e-6)

    def test_default_C(self):
        op = QCALStringOperator()
        assert op.C == 1.0

    def test_custom_f0(self):
        op = QCALStringOperator(f0=100.0)
        assert op.f0 == 100.0

    def test_custom_C(self):
        op = QCALStringOperator(C=244.36)
        assert op.C == pytest.approx(244.36)

    def test_invalid_C_zero(self):
        with pytest.raises(ValueError):
            QCALStringOperator(C=0.0)

    def test_invalid_C_negative(self):
        with pytest.raises(ValueError):
            QCALStringOperator(C=-1.0)

    def test_invalid_f0_zero(self):
        with pytest.raises(ValueError):
            QCALStringOperator(f0=0.0)

    def test_invalid_f0_negative(self):
        with pytest.raises(ValueError):
            QCALStringOperator(f0=-1.0)


# ===========================================================================
# 3. modulation_potential
# ===========================================================================

class TestModulationPotential:
    def test_positive(self):
        op = QCALStringOperator()
        assert op.modulation_potential() > 0.0

    def test_scales_with_hbar(self):
        op1 = QCALStringOperator(hbar=1.0)
        op2 = QCALStringOperator(hbar=2.0)
        assert op2.modulation_potential() == pytest.approx(2.0 * op1.modulation_potential())

    def test_scales_with_C_inverse(self):
        op1 = QCALStringOperator(C=1.0, hbar=1.0)
        op2 = QCALStringOperator(C=2.0, hbar=1.0)
        assert op2.modulation_potential() == pytest.approx(0.5 * op1.modulation_potential())

    def test_formula(self):
        op = QCALStringOperator(C=1.0, hbar=1.0)
        expected = GAMMAS[0] * 1.0 / 1.0
        assert op.modulation_potential() == pytest.approx(expected, rel=1e-10)


# ===========================================================================
# 4. compute_eigenvalue
# ===========================================================================

class TestComputeEigenvalue:
    def test_first_eigenvalue_approx_2003(self):
        op = QCALStringOperator()
        lam1 = op.compute_eigenvalue(GAMMAS[0])
        # γ₁ · 141.7001 ≈ 14.13 × 141.7001 ≈ 2002.0, plus tiny V̂_mod
        assert 2000.0 < lam1 < 2010.0

    def test_second_eigenvalue_approx_2978(self):
        op = QCALStringOperator()
        lam2 = op.compute_eigenvalue(GAMMAS[1])
        assert 2970.0 < lam2 < 2990.0

    def test_eigenvalue_monotone(self):
        op = QCALStringOperator()
        lambdas = [op.compute_eigenvalue(g) for g in GAMMAS]
        for i in range(len(lambdas) - 1):
            assert lambdas[i] < lambdas[i + 1]

    def test_eigenvalue_formula(self):
        op = QCALStringOperator(C=1.0, hbar=1.0)
        g = 30.0
        expected = g * op.f0 + op.modulation_potential()
        assert op.compute_eigenvalue(g) == pytest.approx(expected, rel=1e-10)


# ===========================================================================
# 5. certify_critical_line
# ===========================================================================

class TestCertifyCriticalLine:
    def test_at_half_returns_one(self):
        op = QCALStringOperator()
        sigma, score = op.certify_critical_line(0.5)
        assert sigma == pytest.approx(0.5)
        assert score == pytest.approx(1.0, abs=1e-12)

    def test_score_less_than_one_off_half(self):
        op = QCALStringOperator()
        _, score = op.certify_critical_line(0.6)
        assert score < 1.0

    def test_symmetric_around_half(self):
        op = QCALStringOperator()
        _, s1 = op.certify_critical_line(0.4)
        _, s2 = op.certify_critical_line(0.6)
        assert s1 == pytest.approx(s2, rel=1e-12)

    def test_score_positive(self):
        op = QCALStringOperator()
        for sigma in np.linspace(0.0, 1.0, 11):
            _, score = op.certify_critical_line(float(sigma))
            assert score > 0.0

    def test_formula(self):
        op = QCALStringOperator(C=2.0)
        sigma = 0.7
        _, score = op.certify_critical_line(sigma)
        expected = math.exp(-abs(sigma - 0.5) / 2.0)
        assert score == pytest.approx(expected, rel=1e-10)


# ===========================================================================
# 6. build_lambda_list
# ===========================================================================

class TestBuildLambdaList:
    def test_length(self):
        op = QCALStringOperator()
        lst = build_lambda_list(op)
        assert len(lst) == 20

    def test_first_approx_2003(self):
        op = QCALStringOperator()
        lst = build_lambda_list(op)
        assert 2000.0 < lst[0] < 2010.0

    def test_all_positive(self):
        op = QCALStringOperator()
        for lam in build_lambda_list(op):
            assert lam > 0.0

    def test_consistent_with_compute_eigenvalue(self):
        op = QCALStringOperator()
        lst = build_lambda_list(op)
        for i, g in enumerate(GAMMAS):
            assert lst[i] == pytest.approx(op.compute_eigenvalue(g), rel=1e-12)


# ===========================================================================
# 7. build_spectral_grid
# ===========================================================================

class TestBuildSpectralGrid:
    def test_keys(self):
        g = build_spectral_grid(8)
        assert set(g.keys()) == {"kx", "ky", "k2", "k2_safe"}

    def test_shape(self):
        N = 16
        g = build_spectral_grid(N)
        for arr in g.values():
            assert arr.shape == (N, N)

    def test_k2_nonnegative(self):
        g = build_spectral_grid(8)
        assert np.all(g["k2"] >= 0.0)

    def test_k2_safe_no_zeros(self):
        g = build_spectral_grid(8)
        assert np.all(g["k2_safe"] > 0.0)

    def test_k2_safe_equals_k2_away_from_origin(self):
        g = build_spectral_grid(8)
        mask = g["k2"] > 0
        np.testing.assert_allclose(g["k2_safe"][mask], g["k2"][mask])

    def test_k2_at_origin_safe(self):
        g = build_spectral_grid(8)
        assert g["k2_safe"][0, 0] == pytest.approx(1.0)


# ===========================================================================
# 8. compute_psi
# ===========================================================================

class TestComputePsi:
    def setup_method(self):
        N = 32
        x1d = np.linspace(0, 1, N)
        self.xx, self.yy = np.meshgrid(x1d, x1d, indexing="ij")
        self.op = QCALStringOperator()

    def test_psi_in_unit_interval(self):
        u = np.sin(2 * np.pi * self.xx)
        v = np.cos(2 * np.pi * self.yy)
        psi = compute_psi(u, v, self.xx, self.op)
        assert 0.0 <= psi <= 1.0

    def test_zero_velocity_returns_zero_psi(self):
        u = np.zeros_like(self.xx)
        v = np.zeros_like(self.xx)
        psi = compute_psi(u, v, self.xx, self.op)
        assert psi == pytest.approx(0.0, abs=1e-10)

    def test_returns_float(self):
        u = np.random.randn(32, 32)
        v = np.random.randn(32, 32)
        psi = compute_psi(u, v, self.xx, self.op)
        assert isinstance(psi, float)


# ===========================================================================
# 9. string_noetic_forcing
# ===========================================================================

class TestStringNoeticForcing:
    def setup_method(self):
        N = 16
        x1d = np.linspace(0, 1, N)
        self.xx, self.yy = np.meshgrid(x1d, x1d, indexing="ij")
        self.op = QCALStringOperator()
        self.lambdas = build_lambda_list(self.op)

    def test_shape(self):
        H = string_noetic_forcing(0.0, self.xx, self.yy, self.op, 0.5, self.lambdas)
        assert H.shape == self.xx.shape

    def test_zero_psi_gives_zero_forcing(self):
        H = string_noetic_forcing(0.0, self.xx, self.yy, self.op, 0.0, self.lambdas)
        np.testing.assert_allclose(H, 0.0, atol=1e-15)

    def test_superradiant_gain_active_above_threshold(self):
        H_low = string_noetic_forcing(0.1, self.xx, self.yy, self.op, 0.5, self.lambdas)
        H_high = string_noetic_forcing(0.1, self.xx, self.yy, self.op, 0.95, self.lambdas)
        # High Ψ should produce larger amplitude (gain factor N²Ψ²)
        assert np.max(np.abs(H_high)) >= np.max(np.abs(H_low))

    def test_uniform_in_space(self):
        H = string_noetic_forcing(0.0, self.xx, self.yy, self.op, 0.5, self.lambdas)
        # Forcing is spatially uniform — all values should be equal
        assert np.allclose(H, H[0, 0])

    def test_time_variation(self):
        H1 = string_noetic_forcing(0.0, self.xx, self.yy, self.op, 0.5, self.lambdas)
        H2 = string_noetic_forcing(0.1, self.xx, self.yy, self.op, 0.5, self.lambdas)
        # Different times should give different forcing (generically)
        assert not np.allclose(H1, H2)

    def test_below_threshold_no_superradiant_gain(self):
        """Below Ψ=0.888, forcing should be small without gain factor."""
        H = string_noetic_forcing(0.5, self.xx, self.yy, self.op, 0.1, self.lambdas)
        H_above = string_noetic_forcing(0.5, self.xx, self.yy, self.op, 0.9, self.lambdas)
        # Above threshold carries N²Ψ² gain — amplitude must dominate
        assert np.max(np.abs(H_above)) > np.max(np.abs(H))

    def test_empty_lambda_list_gives_zero(self):
        H = string_noetic_forcing(0.0, self.xx, self.yy, self.op, 0.5, [])
        np.testing.assert_allclose(H, 0.0, atol=1e-15)


# ===========================================================================
# 10. rk4_step (incompressibility)
# ===========================================================================

class TestRk4Step:
    def setup_method(self):
        self.N = 16
        g = build_spectral_grid(self.N)
        self.kx = g["kx"]
        self.ky = g["ky"]
        self.k2 = g["k2"]
        self.k2_safe = g["k2_safe"]
        self.op = QCALStringOperator()
        self.lambdas = build_lambda_list(self.op)

        # Simple divergence-free initial field
        rng = np.random.default_rng(42)
        u0 = rng.standard_normal((self.N, self.N))
        v0 = rng.standard_normal((self.N, self.N))
        self.uhat = np.fft.fft2(u0).astype(complex)
        self.vhat = np.fft.fft2(v0).astype(complex)
        # Leray-project initial state
        from qcal.string_core import _leray_project
        self.uhat, self.vhat = _leray_project(
            self.uhat, self.vhat, self.kx, self.ky, self.k2_safe
        )

    def test_output_shape(self):
        un, vn = rk4_step(
            self.uhat, self.vhat,
            dt=0.005, rho=1.0, mu=1.0 / 141.7001,
            kx=self.kx, ky=self.ky, k2=self.k2, k2_safe=self.k2_safe,
            t=0.0, op=self.op, lambda_list=self.lambdas,
        )
        assert un.shape == (self.N, self.N)
        assert vn.shape == (self.N, self.N)

    def test_incompressibility_after_step(self):
        """Leray projection must enforce ∇·u = 0."""
        un, vn = rk4_step(
            self.uhat, self.vhat,
            dt=0.005, rho=1.0, mu=1.0 / 141.7001,
            kx=self.kx, ky=self.ky, k2=self.k2, k2_safe=self.k2_safe,
            t=0.0, op=self.op, lambda_list=self.lambdas,
        )
        divergence = np.abs(1j * self.kx * un + 1j * self.ky * vn)
        # Away from k=0, divergence should be near machine epsilon
        divergence[0, 0] = 0.0
        assert np.max(divergence) < 1e-10

    def test_zero_mean_flow(self):
        """k=0 mode should be zero after Leray projection."""
        un, vn = rk4_step(
            self.uhat, self.vhat,
            dt=0.005, rho=1.0, mu=1.0 / 141.7001,
            kx=self.kx, ky=self.ky, k2=self.k2, k2_safe=self.k2_safe,
            t=0.0, op=self.op, lambda_list=self.lambdas,
        )
        assert abs(un[0, 0]) < 1e-10
        assert abs(vn[0, 0]) < 1e-10

    def test_finite_output(self):
        un, vn = rk4_step(
            self.uhat, self.vhat,
            dt=0.005, rho=1.0, mu=1.0 / 141.7001,
            kx=self.kx, ky=self.ky, k2=self.k2, k2_safe=self.k2_safe,
            t=0.0, op=self.op, lambda_list=self.lambdas,
        )
        assert np.all(np.isfinite(un))
        assert np.all(np.isfinite(vn))


# ===========================================================================
# 11. Re-export surface — qcal_string_core root shim
# ===========================================================================

class TestReExportSurface:
    def test_import_qcal_string_core_module(self):
        import qcal_string_core
        assert hasattr(qcal_string_core, "QCALStringOperator")

    def test_gammas_reexport(self):
        import qcal_string_core
        assert qcal_string_core.GAMMAS is GAMMAS

    def test_build_lambda_list_reexport(self):
        import qcal_string_core
        op = qcal_string_core.QCALStringOperator()
        lst = qcal_string_core.build_lambda_list(op)
        assert len(lst) == 20

    def test_rk4_step_reexport(self):
        import qcal_string_core
        assert callable(qcal_string_core.rk4_step)

    def test_build_spectral_grid_reexport(self):
        import qcal_string_core
        g = qcal_string_core.build_spectral_grid(8)
        assert "k2" in g

    def test_qcal_package_exports(self):
        import qcal
        assert hasattr(qcal, "QCALStringOperator")
        assert hasattr(qcal, "GAMMAS")
        assert hasattr(qcal, "build_lambda_list")
        assert hasattr(qcal, "build_spectral_grid")
        assert hasattr(qcal, "compute_psi")
        assert hasattr(qcal, "string_noetic_forcing")
        assert hasattr(qcal, "rk4_step")

    def test_qcal_version_updated(self):
        import qcal
        assert qcal.__version__ == "2.2.0"

    def test_compute_psi_reexport(self):
        import qcal_string_core
        assert callable(qcal_string_core.compute_psi)
