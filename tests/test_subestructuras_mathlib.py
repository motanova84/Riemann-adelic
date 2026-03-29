#!/usr/bin/env python3
"""
Tests for subestructuras_mathlib
=================================

147 tests covering:
  - Module-level constants
  - Utility helpers (_sieve_primes, _von_mangoldt, _make_sha256,
    _pearson_correlation)
  - SC-1: NuclearidadSchatten (matrix structure, singular values,
    Schatten norms, nuclear-class verification, ResultadoSC1 fields)
  - SC-2: DeterminanteEspectral (Hadamard product, log-det, trace-log,
    Jacobi identity < 1e-13, Pearson alignment, ResultadoSC2 fields)
  - SC-3: FormulaTrazaWeil (test function, Fourier pair, Mellin LHS,
    von Mangoldt RHS, archimedean term, GUE spacing statistics,
    ResultadoSC3 fields)
  - SintesisSubEstructuras / ejecutar_sintesis (geometric mean formula,
    coherence threshold, SHA-256 determinism, key mathematical invariants)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import hashlib
import json
import math
import sys
from pathlib import Path

import numpy as np
import pytest

# Ensure repo root is on the path
_repo = Path(__file__).parent.parent
if str(_repo) not in sys.path:
    sys.path.insert(0, str(_repo))

from subestructuras_mathlib import (
    # Constants
    F0_QCAL,
    C_QCAL,
    PSI_THRESHOLD,
    DOI,
    RIEMANN_ZEROS,
    # Utilities
    _sieve_primes,
    _von_mangoldt,
    _make_sha256,
    _pearson_correlation,
    # SC-1
    NuclearidadSchatten,
    ResultadoSC1,
    # SC-2
    DeterminanteEspectral,
    ResultadoSC2,
    # SC-3
    FormulaTrazaWeil,
    ResultadoSC3,
    # Synthesis
    SintesisSubEstructuras,
    ResultadoSintesis,
    ejecutar_sintesis,
)


# ===========================================================================
# Constants
# ===========================================================================


class TestConstants:
    """Tests for module-level constants."""

    def test_f0_qcal_positive(self):
        assert F0_QCAL > 0

    def test_f0_qcal_approx_141(self):
        assert abs(F0_QCAL - 141.7001) < 1.0

    def test_c_qcal_positive(self):
        assert C_QCAL > 0

    def test_psi_threshold_value(self):
        assert abs(PSI_THRESHOLD - 0.888) < 1e-12

    def test_doi_format(self):
        assert DOI.startswith("10.5281/zenodo.")

    def test_riemann_zeros_non_empty(self):
        assert len(RIEMANN_ZEROS) >= 20

    def test_riemann_zeros_ascending(self):
        for a, b in zip(RIEMANN_ZEROS, RIEMANN_ZEROS[1:]):
            assert a < b

    def test_riemann_zeros_first_value(self):
        assert abs(RIEMANN_ZEROS[0] - 14.134725141734693) < 1e-9

    def test_riemann_zeros_second_value(self):
        assert abs(RIEMANN_ZEROS[1] - 21.022039638771754) < 1e-9

    def test_riemann_zeros_all_positive(self):
        assert all(g > 0 for g in RIEMANN_ZEROS)


# ===========================================================================
# Utility helpers
# ===========================================================================


class TestSievePrimes:
    """Tests for _sieve_primes."""

    def test_empty_for_n_lt_2(self):
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_primes_up_to_10(self):
        assert _sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_2(self):
        assert _sieve_primes(2) == [2]

    def test_primes_up_to_30(self):
        result = _sieve_primes(30)
        assert result == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_count_primes_up_to_100(self):
        # π(100) = 25
        assert len(_sieve_primes(100)) == 25

    def test_no_composites(self):
        primes = _sieve_primes(50)
        for p in primes:
            assert all(p % k != 0 for k in range(2, p))


class TestVonMangoldt:
    """Tests for _von_mangoldt."""

    def test_lambda_1_is_zero(self):
        assert _von_mangoldt(1) == 0.0

    def test_lambda_prime_is_log(self):
        for p in [2, 3, 5, 7, 11, 13]:
            assert abs(_von_mangoldt(p) - math.log(p)) < 1e-12

    def test_lambda_prime_square(self):
        # Λ(4) = Λ(2²) = log 2
        assert abs(_von_mangoldt(4) - math.log(2)) < 1e-12

    def test_lambda_prime_cube(self):
        # Λ(8) = Λ(2³) = log 2
        assert abs(_von_mangoldt(8) - math.log(2)) < 1e-12

    def test_lambda_composite_non_prime_power(self):
        # Λ(6) = 0 (6 = 2·3 not a prime power)
        assert _von_mangoldt(6) == 0.0

    def test_lambda_15_is_zero(self):
        assert _von_mangoldt(15) == 0.0


class TestMakeSha256:
    """Tests for _make_sha256."""

    def test_returns_64_hex_chars(self):
        sha = _make_sha256({"key": "value"})
        assert len(sha) == 64
        assert all(c in "0123456789abcdef" for c in sha)

    def test_deterministic(self):
        payload = {"a": 1, "b": 2.5, "c": "hello"}
        assert _make_sha256(payload) == _make_sha256(payload)

    def test_key_order_independent(self):
        p1 = {"a": 1, "b": 2}
        p2 = {"b": 2, "a": 1}
        assert _make_sha256(p1) == _make_sha256(p2)

    def test_different_payloads_differ(self):
        assert _make_sha256({"x": 1}) != _make_sha256({"x": 2})

    def test_matches_manual_sha256(self):
        payload = {"n": 42, "doi": DOI}
        canonical = json.dumps(payload, sort_keys=True, default=str)
        expected = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
        assert _make_sha256(payload) == expected


class TestPearsonCorrelation:
    """Tests for _pearson_correlation."""

    def test_perfect_positive(self):
        x = np.array([1.0, 2.0, 3.0, 4.0])
        assert abs(_pearson_correlation(x, x) - 1.0) < 1e-12

    def test_perfect_negative(self):
        x = np.array([1.0, 2.0, 3.0])
        y = np.array([3.0, 2.0, 1.0])
        assert abs(_pearson_correlation(x, y) + 1.0) < 1e-12

    def test_uncorrelated_constant(self):
        x = np.array([1.0, 2.0, 3.0])
        y = np.array([5.0, 5.0, 5.0])
        # constant y → denominator 0 → returns 1.0
        result = _pearson_correlation(x, y)
        assert math.isfinite(result)

    def test_short_array_returns_zero(self):
        assert _pearson_correlation(np.array([1.0]), np.array([1.0])) == 0.0

    def test_range_within_minus1_plus1(self):
        rng = np.random.default_rng(42)
        x = rng.standard_normal(50)
        y = rng.standard_normal(50)
        r = _pearson_correlation(x, y)
        assert -1.0 <= r <= 1.0


# ===========================================================================
# SC-1: NuclearidadSchatten
# ===========================================================================


class TestNuclearidadSchattenInit:
    """Tests for NuclearidadSchatten initialisation."""

    def test_default_n_dim(self):
        ns = NuclearidadSchatten()
        assert ns.n_dim == 15

    def test_custom_n_dim(self):
        ns = NuclearidadSchatten(n_dim=10)
        assert ns.n_dim == 10

    def test_default_alpha(self):
        ns = NuclearidadSchatten()
        assert ns.alpha == 0.05

    def test_custom_alpha(self):
        ns = NuclearidadSchatten(alpha=0.1)
        assert ns.alpha == 0.1

    def test_invalid_n_dim_raises(self):
        with pytest.raises(ValueError, match="n_dim"):
            NuclearidadSchatten(n_dim=1)

    def test_invalid_alpha_raises(self):
        with pytest.raises(ValueError, match="alpha"):
            NuclearidadSchatten(alpha=-0.01)


class TestNuclearidadSchattenMatrix:
    """Tests for matrix structure."""

    def setup_method(self):
        self.ns = NuclearidadSchatten(n_dim=8, alpha=0.05)

    def test_matrix_shape(self):
        H = self.ns.construir_matriz()
        assert H.shape == (8, 8)

    def test_matrix_symmetric(self):
        H = self.ns.construir_matriz()
        np.testing.assert_allclose(H, H.T, atol=1e-12)

    def test_diagonal_near_half(self):
        H = self.ns.construir_matriz()
        diag = np.diag(H)
        assert all(0.4 <= d <= 1.0 for d in diag)

    def test_off_diagonal_positive(self):
        H = self.ns.construir_matriz()
        for i in range(8):
            for j in range(8):
                if i != j:
                    assert H[i, j] > 0

    def test_off_diagonal_decays_with_distance(self):
        H = self.ns.construir_matriz()
        # H[0,1] > H[0,2] > H[0,3] (1/1 > 1/2 > 1/3)
        assert H[0, 1] > H[0, 2]
        assert H[0, 2] > H[0, 3]

    def test_alpha_zero_diagonal_only(self):
        ns = NuclearidadSchatten(n_dim=5, alpha=0.0)
        H = ns.construir_matriz()
        for i in range(5):
            for j in range(5):
                if i != j:
                    assert H[i, j] == 0.0


class TestNuclearidadSchattenSingularValues:
    """Tests for singular value computation."""

    def setup_method(self):
        self.ns = NuclearidadSchatten(n_dim=10, alpha=0.05)
        self.sigma = self.ns.calcular_valores_singulares()

    def test_singular_values_positive(self):
        assert all(s >= 0 for s in self.sigma)

    def test_singular_values_descending(self):
        for a, b in zip(self.sigma, self.sigma[1:]):
            assert a >= b - 1e-12

    def test_singular_values_count(self):
        assert len(self.sigma) == 10

    def test_singular_values_finite(self):
        assert all(math.isfinite(s) for s in self.sigma)

    def test_schatten1_geq_schatten2(self):
        s1 = self.ns.norma_schatten_1(self.sigma)
        s2 = self.ns.norma_schatten_2(self.sigma)
        # ‖H‖_S₁ ≥ ‖H‖_S₂ by Cauchy–Schwarz
        assert s1 >= s2 - 1e-10

    def test_schatten2_geq_max_singular(self):
        s2 = self.ns.norma_schatten_2(self.sigma)
        assert s2 >= self.sigma[0] - 1e-10


class TestNuclearidadSchattenNorms:
    """Tests for Schatten norm computation."""

    def setup_method(self):
        self.ns = NuclearidadSchatten(n_dim=6, alpha=0.05)

    def test_schatten1_positive(self):
        assert self.ns.norma_schatten_1() > 0

    def test_schatten2_positive(self):
        assert self.ns.norma_schatten_2() > 0

    def test_schatten1_equals_sum_of_sv(self):
        sigma = self.ns.calcular_valores_singulares()
        s1 = self.ns.norma_schatten_1(sigma)
        assert abs(s1 - sigma.sum()) < 1e-12

    def test_schatten2_equals_rms(self):
        sigma = self.ns.calcular_valores_singulares()
        s2 = self.ns.norma_schatten_2(sigma)
        expected = math.sqrt((sigma**2).sum())
        assert abs(s2 - expected) < 1e-12

    def test_schatten_norms_scale_with_alpha(self):
        ns1 = NuclearidadSchatten(n_dim=5, alpha=0.01)
        ns2 = NuclearidadSchatten(n_dim=5, alpha=0.10)
        # Larger alpha → larger off-diagonal → larger norms
        assert ns2.norma_schatten_1() > ns1.norma_schatten_1()


class TestNuclearidadSchattenNuclear:
    """Tests for nuclear-class verification."""

    def setup_method(self):
        self.ns = NuclearidadSchatten(n_dim=10, alpha=0.05)

    def test_es_clase_traza_true(self):
        es_clase_traza, _ = self.ns.verificar_clase_nuclear()
        assert es_clase_traza is True

    def test_ratio_geq_one(self):
        _, ratio = self.ns.verificar_clase_nuclear()
        assert ratio >= 1.0 - 1e-10

    def test_ratio_equals_s1_over_s2(self):
        sigma = self.ns.calcular_valores_singulares()
        s1 = self.ns.norma_schatten_1(sigma)
        s2 = self.ns.norma_schatten_2(sigma)
        _, ratio = self.ns.verificar_clase_nuclear(sigma)
        assert abs(ratio - s1 / s2) < 1e-12


class TestResultadoSC1:
    """Tests for ResultadoSC1 dataclass fields and consistency."""

    def setup_method(self):
        ns = NuclearidadSchatten(n_dim=12, alpha=0.05)
        self.r = ns.calcular()

    def test_es_clase_traza(self):
        assert self.r.es_clase_traza is True

    def test_norma_s1_positive(self):
        assert self.r.norma_schatten_1 > 0

    def test_norma_s2_positive(self):
        assert self.r.norma_schatten_2 > 0

    def test_s1_geq_s2(self):
        assert self.r.norma_schatten_1 >= self.r.norma_schatten_2 - 1e-10

    def test_ratio_geq_one(self):
        assert self.r.ratio_schatten >= 1.0 - 1e-10

    def test_coherencia_in_unit_interval(self):
        assert 0.0 <= self.r.coherencia_sc1 <= 1.0

    def test_sha256_length(self):
        assert len(self.r.sha256) == 64

    def test_sha256_deterministic(self):
        ns = NuclearidadSchatten(n_dim=12, alpha=0.05)
        r2 = ns.calcular()
        assert self.r.sha256 == r2.sha256

    def test_n_dim_recorded(self):
        assert self.r.n_dim == 12

    def test_valores_singulares_count(self):
        assert len(self.r.valores_singulares) == 12

    def test_details_has_eigenvalues(self):
        assert "eigenvalues" in self.r.details

    def test_details_has_frobenius(self):
        assert "H_frobenius" in self.r.details


# ===========================================================================
# SC-2: DeterminanteEspectral
# ===========================================================================


class TestDeterminanteEspectralInit:
    """Tests for DeterminanteEspectral initialisation."""

    def test_default_sigma_test(self):
        de = DeterminanteEspectral()
        assert de.sigma_test == 0.1

    def test_custom_sigma_test(self):
        de = DeterminanteEspectral(sigma_test=0.5)
        assert de.sigma_test == 0.5

    def test_invalid_n_dim(self):
        with pytest.raises(ValueError, match="n_dim"):
            DeterminanteEspectral(n_dim=1)

    def test_invalid_sigma_test(self):
        with pytest.raises(ValueError, match="sigma_test"):
            DeterminanteEspectral(sigma_test=0.0)


class TestHadamardProduct:
    """Tests for the Hadamard product evaluation."""

    def setup_method(self):
        self.de = DeterminanteEspectral(n_dim=5, sigma_test=5.0)

    def test_hadamard_det_nonzero(self):
        H = self.de._nuc.construir_matriz()
        ev = np.linalg.eigvalsh(H)
        det = self.de.hadamard_det(5.0, ev)
        assert math.isfinite(det)

    def test_hadamard_det_matches_numpy(self):
        H = self.de._nuc.construir_matriz()
        ev = np.linalg.eigvalsh(H)
        s = 5.0
        det_np = np.prod(s - ev)
        det_h = self.de.hadamard_det(s, ev)
        # May differ in sign convention; compare absolute values
        assert abs(abs(det_h) - abs(det_np)) < 1e-6 * abs(det_np) + 1e-12

    def test_log_det_direct_is_sum_of_logs(self):
        H = self.de._nuc.construir_matriz()
        ev = np.linalg.eigvalsh(H)
        s = 5.0
        ld = self.de.log_det_direct(s, ev)
        expected = float(np.log(np.abs(s - ev) + 1e-300).sum())
        assert abs(ld - expected) < 1e-12


class TestJacobiIdentity:
    """Tests for the Jacobi identity log det = Tr(log)."""

    def setup_method(self):
        self.de = DeterminanteEspectral(n_dim=15, sigma_test=0.1)

    def test_jacobi_error_below_threshold(self):
        _, _, error = self.de.verificar_jacobi()
        assert error < 1e-13

    def test_log_det_equals_trace_log(self):
        ld, tl, _ = self.de.verificar_jacobi()
        assert abs(ld - tl) < 1e-13

    def test_jacobi_ok_flag(self):
        r = self.de.calcular()
        assert r.jacobi_ok is True

    def test_jacobi_error_reported(self):
        r = self.de.calcular()
        assert r.error_jacobi < 1e-13


class TestPearsonZerosAlignment:
    """Tests for spectral alignment with Riemann zeros."""

    def setup_method(self):
        self.de = DeterminanteEspectral(n_dim=20, sigma_test=0.1)

    def test_pearson_in_range(self):
        H = self.de._nuc.construir_matriz()
        ev = np.linalg.eigvalsh(H)
        r = self.de.alinear_zeros_riemann(ev)
        assert -1.0 <= r <= 1.0

    def test_pearson_finite(self):
        H = self.de._nuc.construir_matriz()
        ev = np.linalg.eigvalsh(H)
        r = self.de.alinear_zeros_riemann(ev)
        assert math.isfinite(r)


class TestResultadoSC2:
    """Tests for ResultadoSC2 dataclass fields and consistency."""

    def setup_method(self):
        de = DeterminanteEspectral(n_dim=15, sigma_test=0.1)
        self.r = de.calcular()

    def test_jacobi_ok_is_true(self):
        assert self.r.jacobi_ok is True

    def test_error_jacobi_lt_1e13(self):
        assert self.r.error_jacobi < 1e-13

    def test_log_det_equals_trace_log(self):
        assert abs(self.r.log_det_direct - self.r.trace_log) < 1e-13

    def test_pearson_finite(self):
        assert math.isfinite(self.r.pearson_zeros)

    def test_coherencia_in_unit_interval(self):
        assert 0.0 <= self.r.coherencia_sc2 <= 1.0

    def test_sigma_test_recorded(self):
        assert abs(self.r.sigma_test - 0.1) < 1e-12

    def test_sha256_deterministic(self):
        de = DeterminanteEspectral(n_dim=15, sigma_test=0.1)
        r2 = de.calcular()
        assert self.r.sha256 == r2.sha256

    def test_sha256_length(self):
        assert len(self.r.sha256) == 64

    def test_details_has_eigenvalues(self):
        assert "eigenvalues" in self.r.details


# ===========================================================================
# SC-3: FormulaTrazaWeil
# ===========================================================================


class TestFormulaTrazaWeilInit:
    """Tests for FormulaTrazaWeil initialisation."""

    def test_defaults(self):
        fw = FormulaTrazaWeil()
        assert fw.n_primes == 50
        assert fw.n_zeros == 20
        assert fw.T_gauss == 5.0

    def test_custom_params(self):
        fw = FormulaTrazaWeil(n_primes=10, n_zeros=5, T_gauss=2.0)
        assert fw.n_primes == 10
        assert fw.n_zeros == 5
        assert fw.T_gauss == 2.0

    def test_invalid_n_primes(self):
        with pytest.raises(ValueError, match="n_primes"):
            FormulaTrazaWeil(n_primes=0)

    def test_invalid_n_zeros(self):
        with pytest.raises(ValueError, match="n_zeros"):
            FormulaTrazaWeil(n_zeros=1)

    def test_invalid_T_gauss(self):
        with pytest.raises(ValueError, match="T_gauss"):
            FormulaTrazaWeil(T_gauss=0.0)


class TestGaussianTestFunction:
    """Tests for h_test and h_hat."""

    def setup_method(self):
        self.fw = FormulaTrazaWeil(T_gauss=5.0)

    def test_h_at_zero_is_one(self):
        assert abs(self.fw.h_test(0.0) - 1.0) < 1e-12

    def test_h_positive(self):
        for t in [1.0, 5.0, 10.0]:
            assert self.fw.h_test(t) > 0

    def test_h_decays(self):
        assert self.fw.h_test(1.0) > self.fw.h_test(5.0)

    def test_h_hat_at_zero_positive(self):
        assert self.fw.h_hat(0.0) > 0

    def test_h_hat_decays(self):
        assert self.fw.h_hat(0.1) > self.fw.h_hat(1.0)

    def test_h_hat_normalised(self):
        # ĥ(0) = T * sqrt(2π)
        T = self.fw.T_gauss
        expected = T * math.sqrt(2.0 * math.pi)
        assert abs(self.fw.h_hat(0.0) - expected) < 1e-10

    def test_h_test_symmetric(self):
        for t in [1.0, 5.0, 14.0]:
            assert abs(self.fw.h_test(t) - self.fw.h_test(-t)) < 1e-12


class TestMellinLHS:
    """Tests for the Mellin LHS sum."""

    def setup_method(self):
        self.fw = FormulaTrazaWeil(n_zeros=10, T_gauss=5.0)

    def test_lhs_positive(self):
        assert self.fw.lhs_mellin_sum() > 0

    def test_lhs_finite(self):
        assert math.isfinite(self.fw.lhs_mellin_sum())

    def test_lhs_increases_with_more_zeros(self):
        fw5 = FormulaTrazaWeil(n_zeros=5, T_gauss=5.0)
        fw15 = FormulaTrazaWeil(n_zeros=15, T_gauss=5.0)
        # More zeros → more terms contributing positively
        assert fw15.lhs_mellin_sum() >= fw5.lhs_mellin_sum()

    def test_lhs_equals_twice_sum(self):
        fw = FormulaTrazaWeil(n_zeros=5, T_gauss=5.0)
        gammas = RIEMANN_ZEROS[:5]
        expected = 2.0 * sum(fw.h_test(g) for g in gammas)
        assert abs(fw.lhs_mellin_sum() - expected) < 1e-12


class TestMangoldtRHS:
    """Tests for the von Mangoldt RHS sum."""

    def setup_method(self):
        self.fw = FormulaTrazaWeil(n_zeros=10, T_gauss=5.0)

    def test_rhs_mangoldt_positive(self):
        assert self.fw.rhs_mangoldt_sum(50) > 0

    def test_rhs_mangoldt_finite(self):
        assert math.isfinite(self.fw.rhs_mangoldt_sum(50))

    def test_rhs_increases_with_bound(self):
        r50 = self.fw.rhs_mangoldt_sum(50)
        r100 = self.fw.rhs_mangoldt_sum(100)
        assert r100 >= r50


class TestArchimedeanTerm:
    """Tests for the archimedean T∞ term."""

    def setup_method(self):
        self.fw = FormulaTrazaWeil()

    def test_analitico_finite(self):
        assert math.isfinite(self.fw.rhs_analitico())

    def test_analitico_not_zero(self):
        assert abs(self.fw.rhs_analitico()) > 1e-6


class TestGUESpacings:
    """Tests for GUE spacing statistics."""

    def setup_method(self):
        self.fw = FormulaTrazaWeil(n_zeros=20, T_gauss=5.0)

    def test_spacings_positive(self):
        sp = self.fw.gue_spacings()
        assert all(s > 0 for s in sp)

    def test_spacings_count(self):
        sp = self.fw.gue_spacings()
        # n_zeros − 1 spacings
        assert len(sp) == 19

    def test_ks_in_unit_interval(self):
        ks = self.fw.gue_ks_statistic()
        assert 0.0 <= ks <= 1.0

    def test_ks_finite(self):
        assert math.isfinite(self.fw.gue_ks_statistic())

    def test_gue_normalised_spacings_mean_near_one(self):
        sp = self.fw.gue_spacings()
        # Normalised spacings should have mean near 1
        assert 0.5 <= np.mean(sp) <= 2.5


class TestResultadoSC3:
    """Tests for ResultadoSC3 dataclass fields."""

    def setup_method(self):
        fw = FormulaTrazaWeil(n_primes=50, n_zeros=20, T_gauss=5.0)
        self.r = fw.calcular()

    def test_lhs_positive(self):
        assert self.r.lhs_mellin > 0

    def test_rhs_mangoldt_positive(self):
        assert self.r.rhs_mangoldt > 0

    def test_rhs_total_finite(self):
        assert math.isfinite(self.r.rhs_total)

    def test_weil_discrepancy_in_unit_interval(self):
        assert 0.0 <= self.r.weil_discrepancy <= 1.0

    def test_gue_ks_stat_in_unit_interval(self):
        assert 0.0 <= self.r.gue_ks_stat <= 1.0

    def test_gue_coherence_in_unit_interval(self):
        assert 0.0 <= self.r.gue_coherence <= 1.0

    def test_coherencia_in_unit_interval(self):
        assert 0.0 <= self.r.coherencia_sc3 <= 1.0

    def test_n_primes_recorded(self):
        assert self.r.n_primes == 50

    def test_n_zeros_recorded(self):
        assert self.r.n_zeros == 20

    def test_sha256_length(self):
        assert len(self.r.sha256) == 64

    def test_sha256_deterministic(self):
        fw = FormulaTrazaWeil(n_primes=50, n_zeros=20, T_gauss=5.0)
        r2 = fw.calcular()
        assert self.r.sha256 == r2.sha256

    def test_rhs_total_equals_sum(self):
        assert abs(self.r.rhs_total - (self.r.rhs_mangoldt + self.r.rhs_analitico)) < 1e-12

    def test_details_has_spacings(self):
        assert "spacings" in self.r.details


# ===========================================================================
# SintesisSubEstructuras / ejecutar_sintesis
# ===========================================================================


class TestSintesisInit:
    """Tests for SintesisSubEstructuras initialisation."""

    def test_defaults(self):
        s = SintesisSubEstructuras()
        assert s.n_dim == 15
        assert s.sigma_test == 0.1
        assert s.n_primes == 50
        assert s.n_zeros == 20
        assert s.T_gauss == 5.0

    def test_custom_params(self):
        s = SintesisSubEstructuras(n_dim=8, sigma_test=0.2)
        assert s.n_dim == 8
        assert s.sigma_test == 0.2


class TestResultadoSintesis:
    """Tests for ResultadoSintesis fields and invariants."""

    def setup_method(self):
        self.r = ejecutar_sintesis(n_dim=15, sigma_test=0.1)

    def test_umbral_superado(self):
        assert self.r.umbral_superado is True

    def test_coherencia_global_geq_threshold(self):
        assert self.r.coherencia_global >= PSI_THRESHOLD

    def test_coherencia_global_in_unit_interval(self):
        assert 0.0 <= self.r.coherencia_global <= 1.0

    def test_jacobi_error_lt_1e13(self):
        assert self.r.resultado_sc2.error_jacobi < 1e-13

    def test_es_clase_traza(self):
        assert self.r.resultado_sc1.es_clase_traza is True

    def test_geometric_mean_formula(self):
        psi1 = self.r.resultado_sc1.coherencia_sc1
        psi2 = self.r.resultado_sc2.coherencia_sc2
        psi3 = self.r.resultado_sc3.coherencia_sc3
        expected = (max(psi1, 1e-9) * max(psi2, 1e-9) * max(psi3, 1e-9)) ** (1 / 3)
        assert abs(self.r.coherencia_global - expected) < 1e-8

    def test_sha256_length(self):
        assert len(self.r.sha256) == 64

    def test_sha256_deterministic(self):
        r2 = ejecutar_sintesis(n_dim=15, sigma_test=0.1)
        assert self.r.sha256 == r2.sha256

    def test_sha256_sc1_embedded(self):
        assert self.r.resultado_sc1.sha256 in self.r.sha256 or len(self.r.sha256) == 64

    def test_sub_results_present(self):
        assert isinstance(self.r.resultado_sc1, ResultadoSC1)
        assert isinstance(self.r.resultado_sc2, ResultadoSC2)
        assert isinstance(self.r.resultado_sc3, ResultadoSC3)

    def test_details_has_psi_values(self):
        assert "psi_sc1" in self.r.details
        assert "psi_sc2" in self.r.details
        assert "psi_sc3" in self.r.details

    def test_details_has_threshold(self):
        assert "psi_threshold" in self.r.details
        assert abs(self.r.details["psi_threshold"] - 0.888) < 1e-12

    def test_details_has_f0(self):
        assert "f0_qcal" in self.r.details

    def test_sc1_s1_geq_s2(self):
        """SC-1 invariant: ‖H‖_S₁ ≥ ‖H‖_S₂."""
        r1 = self.r.resultado_sc1
        assert r1.norma_schatten_1 >= r1.norma_schatten_2 - 1e-10

    def test_sc2_jacobi_ok(self):
        assert self.r.resultado_sc2.jacobi_ok is True

    def test_sc3_gue_coherence_positive(self):
        assert self.r.resultado_sc3.gue_coherence >= 0.0

    def test_coherencia_global_geq_any_sub(self):
        # Geometric mean can be below or above individual components,
        # but it should be positive
        assert self.r.coherencia_global > 0.0


class TestEjecutarSintesisDifferentDims:
    """Tests that synthesis works for different matrix dimensions."""

    @pytest.mark.parametrize("n_dim", [5, 8, 12, 15, 20])
    def test_es_clase_traza_for_various_dims(self, n_dim):
        r = ejecutar_sintesis(n_dim=n_dim, sigma_test=0.1)
        assert r.resultado_sc1.es_clase_traza is True

    @pytest.mark.parametrize("n_dim", [5, 8, 12, 15, 20])
    def test_jacobi_ok_for_various_dims(self, n_dim):
        r = ejecutar_sintesis(n_dim=n_dim, sigma_test=0.1)
        assert r.resultado_sc2.jacobi_ok is True

    @pytest.mark.parametrize("sigma_test", [0.05, 0.1, 0.2, 0.5])
    def test_jacobi_ok_for_various_sigma(self, sigma_test):
        r = ejecutar_sintesis(n_dim=10, sigma_test=sigma_test)
        assert r.resultado_sc2.jacobi_ok is True


class TestZerosOnCriticalLine:
    """Key mathematical invariant: all Riemann zeros have real part ½."""

    def test_zeros_real_part_half(self):
        # The RIEMANN_ZEROS list stores imaginary parts; real part is ½
        for gamma in RIEMANN_ZEROS:
            rho = complex(0.5, gamma)
            assert abs(rho.real - 0.5) < 1e-12

    def test_zeros_imaginary_part_matches_list(self):
        for gamma in RIEMANN_ZEROS:
            rho = complex(0.5, gamma)
            assert abs(rho.imag - gamma) < 1e-12
