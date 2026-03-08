#!/usr/bin/env python3
"""
Unit Tests for Riemann Quinto Postulado — 113 tests
=====================================================

Complete test suite covering all classes, methods, and integration points
of the three independent mathematical operators:

  1. ScaleIdentityOperator  (Ψ ≈ 0.984)
  2. SymbioticHamiltonianOperator  (Ψ ≈ 0.892)
  3. RiemannZetaSpectrum  (Ψ ≈ 1.000)

Plus geometric validation (verificar_geometria) and SHA-256 activation
(activar_quinto_postulado).

Test class summary
------------------
  TestModuleConstants           8  tests   (section 1)
  TestScaleIdentityInit         7  tests   (section 2)
  TestScaleIdentityComputation 11  tests   (section 3)
  TestScaleIdentityResult       7  tests   (section 4)
  TestHamiltonianInit           5  tests   (section 5)
  TestHamiltonianComputation   12  tests   (section 6)
  TestHamiltonianResult         7  tests   (section 7)
  TestZetaSpectrumInit          7  tests   (section 8)
  TestZetaSpectrumComputation  11  tests   (section 9)
  TestZetaSpectrumResult        8  tests   (section 10)
  TestVerificarGeometria        8  tests   (section 11)
  TestActivarQuintoPostulado   10  tests   (section 12)
  TestCertificateJSON           5  tests   (section 13)
  TestDemonstration             4  tests   (section 14)
  TestEdgeCases                 3  tests   (section 15)
  ─────────────────────────────────────────────────────
  Total                       113  tests

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    F0_QCAL,
    C_COHERENCE,
    PHI,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    ScaleIdentityOperator,
    ScaleIdentityResult,
    SymbioticHamiltonianOperator,
    HamiltonianResult,
    RiemannZetaSpectrum,
    ZetaSpectrumResult,
    QuintoPostuladoResult,
    verificar_geometria,
    activar_quinto_postulado,
    demonstrate_quinto_postulado,
)


# ===========================================================================
# Section 1 — Module-level constants (8 tests)
# ===========================================================================

class TestModuleConstants:
    """Validate module-level QCAL constants."""

    def test_f0_value(self):
        assert F0_QCAL == pytest.approx(141.7001, rel=1e-6)

    def test_c_coherence_value(self):
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)

    def test_phi_golden_ratio(self):
        assert PHI == pytest.approx(1.6180339887498948, rel=1e-10)
        # Fibonacci relation: Φ² = Φ + 1
        assert PHI ** 2 == pytest.approx(PHI + 1.0, rel=1e-10)

    def test_psi_threshold(self):
        assert PSI_THRESHOLD == pytest.approx(0.888, rel=1e-6)

    def test_riemann_zeros_length(self):
        assert len(RIEMANN_ZEROS) == 30

    def test_riemann_zeros_sorted(self):
        assert np.all(np.diff(RIEMANN_ZEROS) > 0)

    def test_riemann_zeros_first(self):
        assert RIEMANN_ZEROS[0] == pytest.approx(14.134725141734693790, rel=1e-12)

    def test_riemann_zeros_positive(self):
        assert np.all(RIEMANN_ZEROS > 0)


# ===========================================================================
# Section 2 — ScaleIdentityOperator initialisation (7 tests)
# ===========================================================================

class TestScaleIdentityInit:
    """Test ScaleIdentityOperator constructor."""

    def test_default_primes(self):
        op = ScaleIdentityOperator()
        assert op.primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_custom_primes(self):
        op = ScaleIdentityOperator(primes=[2, 3, 5])
        assert op.primes == [2, 3, 5]

    def test_default_n_test_points(self):
        op = ScaleIdentityOperator()
        assert op.n_test_points == 128

    def test_custom_n_test_points(self):
        op = ScaleIdentityOperator(n_test_points=64)
        assert op.n_test_points == 64

    def test_f0_attribute(self):
        op = ScaleIdentityOperator()
        assert op.f0 == F0_QCAL

    def test_c_attribute(self):
        op = ScaleIdentityOperator()
        assert op.C == C_COHERENCE

    def test_rng_seeded_reproducible(self):
        op1 = ScaleIdentityOperator(seed=0)
        op2 = ScaleIdentityOperator(seed=0)
        w1 = op1.haar_weights_at_primes()
        w2 = op2.haar_weights_at_primes()
        np.testing.assert_array_equal(w1, w2)


# ===========================================================================
# Section 3 — ScaleIdentityOperator computations (11 tests)
# ===========================================================================

class TestScaleIdentityComputation:
    """Test ScaleIdentityOperator mathematical methods."""

    def setup_method(self):
        self.op = ScaleIdentityOperator()

    def test_haar_measure_n0(self):
        for p in [2, 3, 5, 7]:
            assert self.op.haar_measure(p, 0) == pytest.approx(1.0)

    def test_haar_measure_n1(self):
        for p in [2, 3, 5]:
            assert self.op.haar_measure(p, 1) == pytest.approx(1.0 / p, rel=1e-10)

    def test_haar_weights_shape(self):
        w = self.op.haar_weights_at_primes()
        assert w.shape == (len(self.op.primes), 3)

    def test_haar_weights_positive(self):
        w = self.op.haar_weights_at_primes()
        assert np.all(w > 0)

    def test_haar_weights_decreasing(self):
        w = self.op.haar_weights_at_primes()
        assert np.all(w[:, 0] > w[:, 1])
        assert np.all(w[:, 1] > w[:, 2])

    def test_adelic_character_unit_modulus(self):
        for p in [3, 5, 7]:
            for x in [0.5, 1.0, 2.7]:
                chi = self.op.adelic_character(x, p)
                assert abs(abs(chi) - 1.0) < 1e-12

    def test_character_phases_shape(self):
        x = np.linspace(0.1, 3.0, 15)
        ph = self.op.character_phases(x)
        assert ph.shape == (len(self.op.primes), 15)

    def test_character_phases_range(self):
        x = np.linspace(0.1, 5.0, 20)
        ph = self.op.character_phases(x)
        assert np.all(ph >= 0.0)
        assert np.all(ph < 2.0 * np.pi + 1e-12)

    def test_fourier_inversion_error_finite(self):
        err = self.op.fourier_inversion_error()
        assert np.isfinite(err)

    def test_p_adic_truncation_error(self):
        trunc = self.op.p_adic_truncation_error()
        expected = sum(p ** (-6) for p in self.op.primes)
        assert trunc == pytest.approx(expected, rel=1e-12)

    def test_coherence_value(self):
        psi = self.op.coherence()
        assert psi == pytest.approx(0.983, abs=0.005)


# ===========================================================================
# Section 4 — ScaleIdentityResult (7 tests)
# ===========================================================================

class TestScaleIdentityResult:
    """Test ScaleIdentityOperator.compute() output."""

    def setup_method(self):
        self.result = ScaleIdentityOperator().compute()

    def test_result_type(self):
        assert isinstance(self.result, ScaleIdentityResult)

    def test_psi_above_threshold(self):
        assert self.result.psi >= PSI_THRESHOLD

    def test_psi_range(self):
        assert 0.0 < self.result.psi <= 1.0

    def test_psi_approx_expected(self):
        assert self.result.psi == pytest.approx(0.984, abs=0.005)

    def test_primes_used(self):
        assert self.result.primes_used == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_haar_weights_included(self):
        assert self.result.haar_weights.shape == (10, 3)

    def test_p_adic_truncation_error_positive(self):
        assert self.result.p_adic_truncation_error > 0.0


# ===========================================================================
# Section 5 — SymbioticHamiltonianOperator initialisation (5 tests)
# ===========================================================================

class TestHamiltonianInit:
    """Test SymbioticHamiltonianOperator constructor."""

    def test_default_matrix_size(self):
        op = SymbioticHamiltonianOperator()
        assert op.N == 64

    def test_custom_matrix_size(self):
        op = SymbioticHamiltonianOperator(matrix_size=32)
        assert op.N == 32

    def test_default_x_range(self):
        op = SymbioticHamiltonianOperator()
        assert op.x_min == pytest.approx(0.5)
        assert op.x_max == pytest.approx(8.0)

    def test_invalid_x_min_raises(self):
        with pytest.raises(ValueError, match="x_min"):
            SymbioticHamiltonianOperator(x_min=0.0)

    def test_grid_positive(self):
        op = SymbioticHamiltonianOperator()
        assert np.all(op._x > 0)


# ===========================================================================
# Section 6 — SymbioticHamiltonianOperator computations (12 tests)
# ===========================================================================

class TestHamiltonianComputation:
    """Test SymbioticHamiltonianOperator mathematical methods."""

    def setup_method(self):
        self.op = SymbioticHamiltonianOperator(matrix_size=32)

    def test_derivative_matrix_shape(self):
        D = self.op._derivative_matrix()
        assert D.shape == (32, 32)

    def test_derivative_matrix_antisymmetric(self):
        D = self.op._derivative_matrix()
        np.testing.assert_allclose(D.conj().T, -D, atol=1e-14)

    def test_hamiltonian_shape(self):
        H = self.op.build_hamiltonian()
        assert H.shape == (32, 32)

    def test_hamiltonian_hermitian(self):
        H = self.op.build_hamiltonian()
        np.testing.assert_allclose(H, H.conj().T, atol=1e-12)

    def test_hermiticity_error_near_zero(self):
        H = self.op.build_hamiltonian()
        err = self.op.hermiticity_error(H)
        assert err < 1e-12

    def test_commutator_norm_nonneg(self):
        H = self.op.build_hamiltonian()
        c = self.op.commutator_norm(H)
        assert c >= 0.0

    def test_commutator_norm_finite(self):
        H = self.op.build_hamiltonian()
        c = self.op.commutator_norm(H)
        assert np.isfinite(c)

    def test_eigenvalues_real(self):
        H = self.op.build_hamiltonian()
        eigs = np.linalg.eigvalsh(H)
        assert eigs.dtype in (np.float64, np.float32)

    def test_eigenvalues_count(self):
        H = self.op.build_hamiltonian()
        eigs = np.linalg.eigvalsh(H)
        assert len(eigs) == 32

    def test_qcal_sync_range(self):
        H = self.op.build_hamiltonian()
        eigs = np.linalg.eigvalsh(H)
        sync = self.op.qcal_sync_factor(eigs)
        assert 0.0 <= sync <= 1.0

    def test_commutator_zero_matrix(self):
        H_zero = np.zeros((32, 32), dtype=complex)
        assert self.op.commutator_norm(H_zero) == 0.0

    def test_qcal_sync_single_eigenvalue(self):
        sync = self.op.qcal_sync_factor(np.array([3.14]))
        assert sync == 0.0


# ===========================================================================
# Section 7 — HamiltonianResult (7 tests)
# ===========================================================================

class TestHamiltonianResult:
    """Test SymbioticHamiltonianOperator.compute() output."""

    def setup_method(self):
        self.result = SymbioticHamiltonianOperator().compute()

    def test_result_type(self):
        assert isinstance(self.result, HamiltonianResult)

    def test_psi_above_threshold(self):
        assert self.result.psi >= PSI_THRESHOLD

    def test_psi_range(self):
        assert 0.0 < self.result.psi <= 1.0

    def test_psi_approx_expected(self):
        assert self.result.psi == pytest.approx(0.892, abs=0.015)

    def test_hermiticity_error_tiny(self):
        assert self.result.hermiticity_error < 1e-12

    def test_matrix_size(self):
        assert self.result.matrix_size == 64

    def test_eigenvalues_finite(self):
        assert np.all(np.isfinite(self.result.eigenvalues))


# ===========================================================================
# Section 8 — RiemannZetaSpectrum initialisation (7 tests)
# ===========================================================================

class TestZetaSpectrumInit:
    """Test RiemannZetaSpectrum constructor."""

    def test_default_zeros_count(self):
        op = RiemannZetaSpectrum()
        assert len(op.zeros) == 30

    def test_custom_n_zeros(self):
        op = RiemannZetaSpectrum(use_n_zeros=15)
        assert len(op.zeros) == 15

    def test_custom_zeros_array(self):
        custom = np.array([14.135, 21.022, 25.011, 30.425])
        op = RiemannZetaSpectrum(zeros=custom)
        assert len(op.zeros) == 4

    def test_custom_zeros_sorted(self):
        custom = np.array([30.0, 14.0, 21.0])
        op = RiemannZetaSpectrum(zeros=custom)
        assert np.all(np.diff(op.zeros) > 0)

    def test_zeros_are_known(self):
        op = RiemannZetaSpectrum(use_n_zeros=5)
        np.testing.assert_allclose(op.zeros, RIEMANN_ZEROS[:5], rtol=1e-12)

    def test_f0_attribute(self):
        op = RiemannZetaSpectrum()
        assert op.f0 == F0_QCAL

    def test_capped_at_max_zeros(self):
        op = RiemannZetaSpectrum(use_n_zeros=50)
        assert len(op.zeros) == 30


# ===========================================================================
# Section 9 — RiemannZetaSpectrum computations (11 tests)
# ===========================================================================

class TestZetaSpectrumComputation:
    """Test RiemannZetaSpectrum mathematical methods."""

    def setup_method(self):
        self.op = RiemannZetaSpectrum()

    def test_normalized_spacings_length(self):
        spacings, _ = self.op.normalized_spacings()
        assert len(spacings) == len(self.op.zeros) - 1

    def test_normalized_spacings_positive(self):
        spacings, _ = self.op.normalized_spacings()
        assert np.all(spacings > 0)

    def test_mean_spacing_close_to_one(self):
        spacings, _ = self.op.normalized_spacings()
        assert float(np.mean(spacings)) == pytest.approx(1.0, abs=1e-10)

    def test_gue_cdf_at_zero(self):
        assert RiemannZetaSpectrum.gue_cdf(np.array([0.0]))[0] == pytest.approx(0.0)

    def test_gue_cdf_increasing(self):
        s = np.linspace(0, 4, 50)
        cdf = RiemannZetaSpectrum.gue_cdf(s)
        assert np.all(np.diff(cdf) > 0)

    def test_gue_cdf_range(self):
        s = np.linspace(0, 5, 100)
        cdf = RiemannZetaSpectrum.gue_cdf(s)
        assert np.all(cdf >= 0.0)
        assert np.all(cdf <= 1.0)

    def test_ks_distance_returns_four_values(self):
        result = self.op.ks_distance()
        assert len(result) == 4

    def test_ks_gue_less_than_ks_poisson(self):
        ks_gue, _, ks_poi, _ = self.op.ks_distance()
        assert ks_gue < ks_poi

    def test_p_gue_greater_than_p_poisson(self):
        _, p_gue, _, p_poi = self.op.ks_distance()
        assert p_gue > p_poi

    def test_coherence_high(self):
        psi = self.op.coherence()
        assert psi > 0.95

    def test_coherence_approx_expected(self):
        psi = self.op.coherence()
        assert psi == pytest.approx(0.997, abs=0.005)


# ===========================================================================
# Section 10 — ZetaSpectrumResult (8 tests)
# ===========================================================================

class TestZetaSpectrumResult:
    """Test RiemannZetaSpectrum.compute() output."""

    def setup_method(self):
        self.result = RiemannZetaSpectrum().compute()

    def test_result_type(self):
        assert isinstance(self.result, ZetaSpectrumResult)

    def test_psi_above_threshold(self):
        assert self.result.psi >= PSI_THRESHOLD

    def test_psi_approx_expected(self):
        assert self.result.psi == pytest.approx(0.997, abs=0.005)

    def test_gue_pvalue_reasonable(self):
        assert self.result.gue_ks_pvalue > 0.3

    def test_poisson_pvalue_low(self):
        assert self.result.poisson_ks_pvalue < 0.05

    def test_zeros_length(self):
        assert len(self.result.zeros) == 30

    def test_spacings_length(self):
        assert len(self.result.spacings) == 29

    def test_mean_spacing_positive(self):
        assert self.result.mean_spacing > 0.0


# ===========================================================================
# Section 11 — verificar_geometria (8 tests)
# ===========================================================================

class TestVerificarGeometria:
    """Test the geometric validation function."""

    def setup_method(self):
        self.scale_res = ScaleIdentityOperator().compute()
        self.ham_res = SymbioticHamiltonianOperator().compute()
        self.zeta_res = RiemannZetaSpectrum().compute()

    def test_returns_tuple(self):
        out = verificar_geometria(self.scale_res, self.ham_res, self.zeta_res)
        assert isinstance(out, tuple) and len(out) == 2

    def test_valid_with_good_operators(self):
        valid, _ = verificar_geometria(self.scale_res, self.ham_res, self.zeta_res)
        assert valid is True

    def test_canonical_message_on_success(self):
        _, msg = verificar_geometria(self.scale_res, self.ham_res, self.zeta_res)
        assert "✓ Quinto Postulado verificado" in msg
        assert "QCAL ∞³" in msg

    def test_fails_below_threshold(self):
        bad_scale = ScaleIdentityResult(
            haar_weights=self.scale_res.haar_weights,
            character_phases=self.scale_res.character_phases,
            fourier_inversion_error=0.1,
            p_adic_truncation_error=0.1,
            psi=0.5,
            primes_used=self.scale_res.primes_used,
        )
        valid, msg = verificar_geometria(bad_scale, self.ham_res, self.zeta_res)
        assert valid is False
        assert "NO verificado" in msg

    def test_message_mentions_failing_operators(self):
        bad_scale = ScaleIdentityResult(
            haar_weights=self.scale_res.haar_weights,
            character_phases=self.scale_res.character_phases,
            fourier_inversion_error=0.1,
            p_adic_truncation_error=0.1,
            psi=0.5,
            primes_used=self.scale_res.primes_used,
        )
        _, msg = verificar_geometria(bad_scale, self.ham_res, self.zeta_res)
        assert "Ψ_S" in msg

    def test_custom_threshold_zero(self):
        valid, _ = verificar_geometria(
            self.scale_res, self.ham_res, self.zeta_res, threshold=0.0
        )
        assert valid is True

    def test_global_psi_above_threshold(self):
        psi_global = (
            self.scale_res.psi * self.ham_res.psi * self.zeta_res.psi
        ) ** (1.0 / 3.0)
        assert psi_global >= PSI_THRESHOLD

    def test_global_psi_approx_expected(self):
        psi_global = (
            self.scale_res.psi * self.ham_res.psi * self.zeta_res.psi
        ) ** (1.0 / 3.0)
        assert psi_global == pytest.approx(0.957, abs=0.005)


# ===========================================================================
# Section 12 — activar_quinto_postulado (10 tests)
# ===========================================================================

class TestActivarQuintoPostulado:
    """Test SHA-256 activation and QuintoPostuladoResult."""

    def setup_method(self):
        self.result = activar_quinto_postulado(save_certificate=False)

    def test_result_type(self):
        assert isinstance(self.result, QuintoPostuladoResult)

    def test_geometry_valid(self):
        assert self.result.geometry_valid is True

    def test_geometry_message(self):
        assert "✓ Quinto Postulado verificado" in self.result.geometry_message

    def test_psi_global_above_threshold(self):
        assert self.result.psi_global >= PSI_THRESHOLD

    def test_psi_global_approx_expected(self):
        assert self.result.psi_global == pytest.approx(0.957, abs=0.005)

    def test_sha256_format(self):
        sha = self.result.certificate_sha256
        assert len(sha) == 64
        assert all(c in "0123456789abcdef" for c in sha)

    def test_timestamp_format(self):
        from datetime import datetime
        dt = datetime.fromisoformat(self.result.timestamp)
        assert dt is not None

    def test_scale_result_attached(self):
        assert isinstance(self.result.scale_result, ScaleIdentityResult)

    def test_hamiltonian_result_attached(self):
        assert isinstance(self.result.hamiltonian_result, HamiltonianResult)

    def test_save_certificate(self, tmp_path):
        activar_quinto_postulado(save_certificate=True, output_dir=tmp_path)
        cert_file = tmp_path / "riemann_quinto_postulado_certificate.json"
        assert cert_file.exists()
        with open(cert_file, encoding="utf-8") as fh:
            data = json.load(fh)
        assert "sha256" in data
        assert data["doi"] == "10.5281/zenodo.17379721"


# ===========================================================================
# Section 13 — Certificate JSON structure (5 tests)
# ===========================================================================

class TestCertificateJSON:
    """Validate the JSON certificate content."""

    def setup_method(self):
        self.tmp = Path("/tmp/qcal_cert_test")
        self.tmp.mkdir(exist_ok=True)
        activar_quinto_postulado(save_certificate=True, output_dir=self.tmp)
        with open(self.tmp / "riemann_quinto_postulado_certificate.json",
                  encoding="utf-8") as fh:
            self.cert = json.load(fh)

    def test_has_sha256_field(self):
        assert "sha256" in self.cert
        assert len(self.cert["sha256"]) == 64

    def test_has_all_operator_keys(self):
        ops = self.cert["operators"]
        assert "ScaleIdentityOperator" in ops
        assert "SymbioticHamiltonianOperator" in ops
        assert "RiemannZetaSpectrum" in ops

    def test_psi_values_reasonable(self):
        ops = self.cert["operators"]
        assert ops["ScaleIdentityOperator"]["psi"] == pytest.approx(0.984, abs=0.005)
        assert ops["SymbioticHamiltonianOperator"]["psi"] == pytest.approx(0.892, abs=0.015)
        assert ops["RiemannZetaSpectrum"]["psi"] == pytest.approx(0.997, abs=0.005)

    def test_doi_present(self):
        assert self.cert["doi"] == "10.5281/zenodo.17379721"

    def test_author_present(self):
        assert "José Manuel Mota Burruezo" in self.cert["author"]


# ===========================================================================
# Section 14 — demonstrate_quinto_postulado (4 tests)
# ===========================================================================

class TestDemonstration:
    """Test the top-level demonstration function."""

    def test_returns_result(self):
        r = demonstrate_quinto_postulado(verbose=False)
        assert isinstance(r, QuintoPostuladoResult)

    def test_geometry_valid(self):
        r = demonstrate_quinto_postulado(verbose=False)
        assert r.geometry_valid is True

    def test_psi_global_range(self):
        r = demonstrate_quinto_postulado(verbose=False)
        assert 0.0 < r.psi_global <= 1.0

    def test_psi_global_above_threshold(self):
        r = demonstrate_quinto_postulado(verbose=False)
        assert r.psi_global >= PSI_THRESHOLD


# ===========================================================================
# Section 15 — Edge cases and robustness (3 tests)
# ===========================================================================

class TestEdgeCases:
    """Edge cases and robustness checks."""

    def test_single_prime_scale_operator(self):
        op = ScaleIdentityOperator(primes=[2])
        result = op.compute()
        assert 0.0 < result.psi <= 1.0

    def test_small_hamiltonian_n8(self):
        op = SymbioticHamiltonianOperator(matrix_size=8)
        result = op.compute()
        assert isinstance(result, HamiltonianResult)
        assert 0.0 < result.psi <= 1.0

    def test_zeta_spectrum_n5_zeros(self):
        op = RiemannZetaSpectrum(use_n_zeros=5)
        result = op.compute()
        assert isinstance(result, ZetaSpectrumResult)
        assert len(result.zeros) == 5
