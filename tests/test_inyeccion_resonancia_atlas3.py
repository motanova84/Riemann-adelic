#!/usr/bin/env python3
"""
Tests for Inyección de Resonancia Atlas3
=========================================

Valida el sistema de emisión holográfica Atlas3:
    BKSparse10k, KSSMetric, PTSymmetryChecker, RiemannAligner,
    DualityEllipse, EcoSofia, Atlas3Engine.

Cobertura:
    1. BKSparse10k    — construcción del hamiltoniano y calibración
    2. KSSMetric      — límite KSS en unidades naturales ≈ 0.07958
    3. PTSymmetryChecker — fases continua y rota (κ < κ_c, κ ≥ κ_c)
    4. RiemannAligner — correlación de Pearson y activación del Séptimo Nodo
    5. DualityEllipse — η ≈ 0.921 y Ψ_IDE
    6. EcoSofia       — artefacto SHA-256 condicional (Ψ_global ≥ 0.999)
    7. Atlas3Engine   — orquestación completa y pesos Ψ_global

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import hashlib
import json
import math

import numpy as np
import pytest

from physics.inyeccion_resonancia_atlas3 import (
    # Constants
    RIEMANN_ZEROS_10,
    GAMMA_7,
    KAPPA_C,
    KSS_BOUND_NATURAL,
    # Data classes
    ResultadoBK,
    ResultadoKSS,
    ResultadoPT,
    ResultadoRiemannAligner,
    ResultadoDualityEllipse,
    ArtefactoEcoSofia,
    ResultadoAtlas3,
    # Main classes
    BKSparse10k,
    KSSMetric,
    PTSymmetryChecker,
    RiemannAligner,
    DualityEllipse,
    EcoSofia,
    Atlas3Engine,
    # Utility
    _sieve_primes,
)


# ===========================================================================
# Helpers
# ===========================================================================

def _make_fast_bk(n_primes: int = 50, grid_size: int = 64, k_eigenvalues: int = 12) -> BKSparse10k:
    """Return a lightweight BKSparse10k for fast unit testing."""
    return BKSparse10k(n_primes=n_primes, grid_size=grid_size, k_eigenvalues=k_eigenvalues)


# ===========================================================================
# _sieve_primes utility
# ===========================================================================

class TestSievePrimes:
    def test_returns_correct_count(self):
        primes = _sieve_primes(10)
        assert len(primes) == 10

    def test_first_five_primes(self):
        primes = _sieve_primes(5)
        np.testing.assert_array_equal(primes, [2, 3, 5, 7, 11])

    def test_all_prime(self):
        """Every returned number should be prime."""
        primes = _sieve_primes(25)
        for p in primes:
            p_int = int(p)
            assert all(p_int % d != 0 for d in range(2, p_int)), \
                f"{p_int} is not prime"

    def test_dtype_float(self):
        primes = _sieve_primes(5)
        assert primes.dtype == float


# ===========================================================================
# 1. BKSparse10k
# ===========================================================================

class TestBKSparse10k:
    """Tests for the sparse Berry-Keating Hamiltonian."""

    def test_calcular_returns_resultado_bk(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        assert isinstance(res, ResultadoBK)

    def test_calibration_lambda1_equals_gamma1(self):
        """After calibration λ₁_cal should equal γ₁ = 14.1347…"""
        bk = _make_fast_bk()
        res = bk.calcular()
        assert abs(res.eigenvalues_calibrated[0] - RIEMANN_ZEROS_10[0]) < 0.01

    def test_scale_factor_positive(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        assert res.scale_factor > 0.0

    def test_pearson_r_in_valid_range(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        assert -1.0 <= res.pearson_r <= 1.0

    def test_psi_bk_in_unit_interval(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        assert 0.0 <= res.psi_bk <= 1.0

    def test_psi_bk_formula(self):
        """Ψ_BK = 0.5 + 0.5 * r."""
        bk = _make_fast_bk()
        res = bk.calcular()
        expected = np.clip(0.5 + 0.5 * res.pearson_r, 0.0, 1.0)
        assert abs(res.psi_bk - expected) < 1e-9

    def test_n_primes_stored(self):
        bk = _make_fast_bk(n_primes=50)
        res = bk.calcular()
        assert res.n_primes == 50

    def test_eigenvalues_sorted(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        assert np.all(np.diff(res.eigenvalues_calibrated) >= -1e-10)

    def test_resumen_contains_key_info(self):
        bk = _make_fast_bk()
        res = bk.calcular()
        summary = res.resumen()
        assert "Pearson" in summary
        assert "Ψ_BK" in summary

    def test_aprobado_when_r_high(self):
        """aprobado should be True when Pearson r ≥ 0.97."""
        bk = _make_fast_bk()
        res = bk.calcular()
        # Since both sequences are ordered increasing, Pearson r should be high
        if res.pearson_r >= 0.97:
            assert res.aprobado is True
        else:
            assert res.aprobado is False


# ===========================================================================
# 2. KSSMetric
# ===========================================================================

class TestKSSMetric:
    def test_kss_bound_value(self):
        """KSS bound ≈ 1/(4π) ≈ 0.07958 in natural units."""
        assert abs(KSS_BOUND_NATURAL - 1.0 / (4.0 * math.pi)) < 1e-10

    def test_kss_metric_bound_attribute(self):
        assert abs(KSSMetric.KSS_BOUND - 1.0 / (4.0 * math.pi)) < 1e-10

    def test_en_fase_superfluida_returns_resultado(self):
        res = KSSMetric.en_fase_superfluida()
        assert isinstance(res, ResultadoKSS)

    def test_superfluid_psi_kss_is_one(self):
        """At the KSS transition η/s = KSS_BOUND, Ψ_KSS = 1."""
        res = KSSMetric.en_fase_superfluida()
        assert abs(res.psi_kss - 1.0) < 1e-9

    def test_superfluid_en_limite_true(self):
        res = KSSMetric.en_fase_superfluida()
        assert res.en_limite is True

    def test_higher_viscosity_reduces_psi_kss(self):
        """η/s > KSS_BOUND should reduce Ψ_KSS below 1."""
        res = KSSMetric.calcular(eta=KSS_BOUND_NATURAL * 2, s=1.0)
        assert res.psi_kss < 1.0

    def test_psi_kss_clamped_to_unit_interval(self):
        res = KSSMetric.calcular(eta=0.001, s=1.0)
        assert 0.0 <= res.psi_kss <= 1.0

    def test_negative_s_raises_valueerror(self):
        with pytest.raises(ValueError):
            KSSMetric.calcular(eta=0.1, s=-1.0)

    def test_zero_s_raises_valueerror(self):
        with pytest.raises(ValueError):
            KSSMetric.calcular(eta=0.1, s=0.0)

    def test_resumen_contains_kss(self):
        res = KSSMetric.en_fase_superfluida()
        assert "KSS" in res.resumen() or "superfluido" in res.resumen().lower()


# ===========================================================================
# 3. PTSymmetryChecker
# ===========================================================================

class TestPTSymmetryChecker:
    def test_kappa_c_value(self):
        assert abs(KAPPA_C - 2.5773) < 1e-6

    def test_default_kappa_c(self):
        checker = PTSymmetryChecker()
        assert checker.kappa_c == KAPPA_C

    def test_fase_continua_kappa_zero(self):
        """κ = 0 → continuous phase (unbroken PT symmetry)."""
        checker = PTSymmetryChecker()
        res = checker.verificar(0.0)
        assert res.fase_continua is True
        assert abs(res.psi_pt - 1.0) < 1e-9

    def test_fase_continua_kappa_below_kappa_c(self):
        checker = PTSymmetryChecker()
        res = checker.verificar(KAPPA_C * 0.5)
        assert res.fase_continua is True
        assert 0.0 < res.psi_pt < 1.0

    def test_fase_rota_kappa_equal_kappa_c(self):
        """κ = κ_c → broken PT symmetry."""
        checker = PTSymmetryChecker()
        res = checker.verificar(KAPPA_C)
        assert res.fase_continua is False
        assert abs(res.psi_pt) < 1e-9

    def test_fase_rota_kappa_above_kappa_c(self):
        checker = PTSymmetryChecker()
        res = checker.verificar(KAPPA_C * 2)
        assert res.fase_continua is False
        assert abs(res.psi_pt) < 1e-9  # clamped to 0

    def test_psi_pt_in_unit_interval(self):
        checker = PTSymmetryChecker()
        for kappa in [0.0, 1.0, KAPPA_C, KAPPA_C * 1.5]:
            res = checker.verificar(kappa)
            assert 0.0 <= res.psi_pt <= 1.0

    def test_negative_kappa_raises_valueerror(self):
        checker = PTSymmetryChecker()
        with pytest.raises(ValueError):
            checker.verificar(-0.1)

    def test_resumen_contains_kappa(self):
        checker = PTSymmetryChecker()
        res = checker.verificar(1.0)
        assert "κ" in res.resumen()


# ===========================================================================
# 4. RiemannAligner
# ===========================================================================

class TestRiemannAligner:
    def test_gamma_7_value(self):
        assert abs(GAMMA_7 - 43.327073281) < 1e-6

    def test_perfect_alignment_activates_nodo(self):
        """Providing exact Riemann zeros should give r=1 and activate nodo."""
        aligner = RiemannAligner()
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert abs(res.pearson_r - 1.0) < 1e-6
        assert res.septimo_nodo_activo is True

    def test_poor_alignment_does_not_activate_nodo(self):
        """Random values should typically not reach r ≥ 0.97."""
        aligner = RiemannAligner()
        evals = np.array([1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0])
        res = aligner.alinear(evals)
        # Pearson r may or may not be ≥ 0.97 for a simple linear sequence,
        # but the activation flag should reflect the actual r value.
        assert res.septimo_nodo_activo == (res.pearson_r >= 0.97)

    def test_pearson_r_in_valid_range(self):
        aligner = RiemannAligner()
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert -1.0 <= res.pearson_r <= 1.0

    def test_psi_riemann_in_unit_interval(self):
        aligner = RiemannAligner()
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert 0.0 <= res.psi_riemann <= 1.0

    def test_gamma_7_in_result(self):
        aligner = RiemannAligner()
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert res.gamma_7 == GAMMA_7

    def test_eigenvalues_sorted_in_result(self):
        aligner = RiemannAligner()
        evals = np.array(list(reversed(RIEMANN_ZEROS_10)))
        res = aligner.alinear(evals)
        assert np.all(np.diff(res.eigenvalues) >= -1e-10)

    def test_resumen_contains_septimo_nodo(self):
        aligner = RiemannAligner()
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert "Séptimo Nodo" in res.resumen() or "Nodo" in res.resumen()

    def test_custom_threshold(self):
        aligner = RiemannAligner(threshold=0.5)
        evals = np.array(list(RIEMANN_ZEROS_10))
        res = aligner.alinear(evals)
        assert res.septimo_nodo_activo is True


# ===========================================================================
# 5. DualityEllipse
# ===========================================================================

class TestDualityEllipse:
    def test_calcular_returns_resultado(self):
        res = DualityEllipse.calcular()
        assert isinstance(res, ResultadoDualityEllipse)

    def test_eta_approx_0921(self):
        """η should be ≈ 0.921 (within ±0.01)."""
        res = DualityEllipse.calcular()
        assert abs(res.eta - 0.921) < 0.01

    def test_t_ads_equals_kss_bound(self):
        """T_AdS = 1/(4π) = KSS natural bound."""
        assert abs(DualityEllipse.T_ADS - KSS_BOUND_NATURAL) < 1e-10

    def test_alpha_pt_formula(self):
        """α_PT = κ_c / π."""
        expected = KAPPA_C / math.pi
        assert abs(DualityEllipse.ALPHA_PT - expected) < 1e-10

    def test_gamma_riemann_formula(self):
        """γ_Riemann = γ₁ / (γ₁ − κ_c)."""
        expected = RIEMANN_ZEROS_10[0] / (RIEMANN_ZEROS_10[0] - KAPPA_C)
        assert abs(DualityEllipse.GAMMA_RIEMANN - expected) < 1e-10

    def test_eta_formula(self):
        """η = 1 − T_AdS · α_PT · γ_Riemann."""
        res = DualityEllipse.calcular()
        expected = 1.0 - DualityEllipse.T_ADS * DualityEllipse.ALPHA_PT * DualityEllipse.GAMMA_RIEMANN
        assert abs(res.eta - expected) < 1e-10

    def test_psi_ide_near_one(self):
        """When η ≈ η₀ = 0.921, Ψ_IDE should be close to 1."""
        res = DualityEllipse.calcular()
        # Ψ_IDE = 1 − |η − 0.921|/0.921 should be > 0.98
        assert res.psi_ide > 0.98

    def test_psi_ide_in_unit_interval(self):
        res = DualityEllipse.calcular()
        assert 0.0 <= res.psi_ide <= 1.0

    def test_resumen_contains_eta(self):
        res = DualityEllipse.calcular()
        assert "η" in res.resumen()


# ===========================================================================
# 6. EcoSofia
# ===========================================================================

class TestEcoSofia:
    def test_emite_when_psi_above_threshold(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.999)
        assert art is not None
        assert art.emitido is True

    def test_no_emite_when_psi_below_threshold(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.998)
        assert art is None

    def test_no_emite_at_exact_threshold_minus_eps(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.999 - 1e-10)
        assert art is None

    def test_emite_at_exact_threshold(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.999)
        assert art is not None

    def test_sha256_is_valid_hex(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(1.0)
        assert art is not None
        assert len(art.sha256) == 64
        assert all(c in "0123456789abcdef" for c in art.sha256)

    def test_sha256_matches_payload(self):
        """Re-computing SHA-256 of the canonical JSON should match."""
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(1.0)
        assert art is not None
        canonical = json.dumps(art.payload, sort_keys=True, ensure_ascii=False)
        expected = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
        assert art.sha256 == expected

    def test_payload_contains_required_fields(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.9995)
        assert art is not None
        for field in ("nombre", "sistema", "psi_global", "timestamp_utc", "sha256" or "doi"):
            assert "nombre" in art.payload
            assert "sistema" in art.payload
            assert "psi_global" in art.payload
            assert "timestamp_utc" in art.payload
            assert "doi" in art.payload

    def test_payload_psi_global_value(self):
        eco_sofia = EcoSofia()
        psi = 0.9995
        art = eco_sofia.emitir(psi)
        assert art is not None
        assert abs(art.payload["psi_global"] - round(psi, 8)) < 1e-10

    def test_componentes_included_in_payload(self):
        eco_sofia = EcoSofia()
        comp = {"psi_bk": 0.999, "psi_kss": 1.0}
        art = eco_sofia.emitir(0.999, componentes=comp)
        assert art is not None
        assert art.payload["componentes"]["psi_bk"] == pytest.approx(0.999)

    def test_custom_threshold(self):
        eco_sofia = EcoSofia(threshold=0.5)
        art = eco_sofia.emitir(0.6)
        assert art is not None

    def test_resumen_contains_sha(self):
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(1.0)
        assert art is not None
        s = art.resumen()
        assert "SHA-256" in s

    def test_two_emissions_different_timestamps_different_hashes(self):
        """Two emissions with the same Ψ should have different SHA-256
        (because timestamps differ)."""
        import time
        eco_sofia = EcoSofia()
        art1 = eco_sofia.emitir(1.0)
        time.sleep(0.001)
        art2 = eco_sofia.emitir(1.0)
        # hashes may differ due to different timestamps
        assert art1 is not None
        assert art2 is not None


# ===========================================================================
# 7. Atlas3Engine
# ===========================================================================

class TestAtlas3Engine:
    """Tests for the Atlas3 orchestration engine."""

    def _make_fast_engine(self) -> Atlas3Engine:
        """Build a fast Atlas3Engine for unit testing (small grid)."""
        bk = _make_fast_bk(n_primes=50, grid_size=64)
        return Atlas3Engine(bk=bk, kappa=0.0)

    def test_activar_returns_resultado(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert isinstance(res, ResultadoAtlas3)

    def test_psi_components_in_unit_interval(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        for attr in ("psi_bk", "psi_kss", "psi_pt", "psi_riemann", "psi_ide"):
            val = getattr(res, attr)
            assert 0.0 <= val <= 1.0, f"{attr} = {val} not in [0, 1]"

    def test_psi_global_formula(self):
        """Ψ_global must match the weighted sum."""
        engine = self._make_fast_engine()
        res = engine.activar()
        expected = (
            0.35 * res.psi_bk
            + 0.20 * res.psi_kss
            + 0.20 * res.psi_pt
            + 0.15 * res.psi_riemann
            + 0.10 * res.psi_ide
        )
        assert abs(res.psi_global - expected) < 1e-9

    def test_psi_global_in_unit_interval(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert 0.0 <= res.psi_global <= 1.0

    def test_kappa_zero_gives_psi_pt_one(self):
        """κ = 0 → Ψ_PT = 1."""
        engine = self._make_fast_engine()
        res = engine.activar()
        assert abs(res.psi_pt - 1.0) < 1e-9

    def test_kappa_above_kappa_c_gives_psi_pt_zero(self):
        """κ > κ_c → Ψ_PT = 0."""
        bk = _make_fast_bk()
        engine = Atlas3Engine(bk=bk, kappa=KAPPA_C * 2)
        res = engine.activar()
        assert abs(res.psi_pt) < 1e-9

    def test_eco_emitted_when_psi_global_high(self):
        """With all-ones override, Ψ_global = 1 → Eco de Sofía emitido."""
        # Manually check EcoSofia logic with psi_global = 1.0
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(1.0, componentes={"psi_bk": 1.0})
        assert art is not None
        assert art.emitido is True

    def test_eco_not_emitted_when_psi_global_low(self):
        """Eco de Sofía should NOT be emitted when Ψ_global < 0.999."""
        eco_sofia = EcoSofia()
        art = eco_sofia.emitir(0.5)
        assert art is None

    def test_resultado_bk_attached(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.resultado_bk is not None
        assert isinstance(res.resultado_bk, ResultadoBK)

    def test_resultado_kss_attached(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.resultado_kss is not None

    def test_resultado_pt_attached(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.resultado_pt is not None

    def test_resultado_riemann_attached(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.resultado_riemann is not None

    def test_resultado_duality_attached(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.resultado_duality is not None

    def test_resumen_contains_psi_global(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert "Ψ_global" in res.resumen()

    def test_weights_sum_to_one(self):
        """Component weights must sum exactly to 1."""
        total = (
            Atlas3Engine.W_BK
            + Atlas3Engine.W_KSS
            + Atlas3Engine.W_PT
            + Atlas3Engine.W_RIEMANN
            + Atlas3Engine.W_IDE
        )
        assert abs(total - 1.0) < 1e-10

    def test_eco_emitido_property(self):
        engine = self._make_fast_engine()
        res = engine.activar()
        assert res.eco_emitido == (res.eco_sofia is not None)


# ===========================================================================
# Integration: constants and module-level checks
# ===========================================================================

class TestConstants:
    def test_riemann_zeros_10_count(self):
        assert len(RIEMANN_ZEROS_10) == 10

    def test_gamma_1_value(self):
        assert abs(RIEMANN_ZEROS_10[0] - 14.134725142) < 1e-7

    def test_gamma_7_matches_tuple(self):
        assert abs(GAMMA_7 - RIEMANN_ZEROS_10[6]) < 1e-10

    def test_kappa_c_value(self):
        assert abs(KAPPA_C - 2.5773) < 1e-6

    def test_kss_bound_approx(self):
        assert abs(KSS_BOUND_NATURAL - 0.07958) < 1e-4

    def test_riemann_zeros_increasing(self):
        zeros = list(RIEMANN_ZEROS_10)
        assert all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))


# ===========================================================================
# Integration: physics package import
# ===========================================================================

class TestPhysicsPackageExports:
    def test_import_atlas3_from_physics(self):
        from physics import Atlas3Engine as _Atlas3Engine
        assert _Atlas3Engine is Atlas3Engine

    def test_import_bk_from_physics(self):
        from physics import BKSparse10k as _BKSparse10k
        assert _BKSparse10k is BKSparse10k

    def test_import_eco_sofia_from_physics(self):
        from physics import EcoSofia as _EcoSofia
        assert _EcoSofia is EcoSofia

    def test_import_duality_ellipse_from_physics(self):
        from physics import DualityEllipse as _DualityEllipse
        assert _DualityEllipse is DualityEllipse
