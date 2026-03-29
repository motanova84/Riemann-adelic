#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for operators/puentes_mathlib_qcal.py
============================================

Verifies the three QCAL-Mathlib bridges:
  SC-1 — Schatten norms / Fredholm determinant
  SC-2 — Jacobi identity / Spectral determinant
  SC-3 — Weil explicit formula / Adelic Poisson

Author: QCAL ∞³
"""
import cmath
import math

import pytest

# Import directly from module (avoid operators/__init__.py side-effects)
import importlib.util
import pathlib

_MOD_PATH = pathlib.Path(__file__).parent.parent / "operators" / "puentes_mathlib_qcal.py"
_spec = importlib.util.spec_from_file_location("puentes_mathlib_qcal", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)  # type: ignore[union-attr]

# Re-export names used in tests
ConstantesPuentesMathlib = _mod.ConstantesPuentesMathlib
OperadorSchatten = _mod.OperadorSchatten
DeterminanteFredholm = _mod.DeterminanteFredholm
IdentidadJacobi = _mod.IdentidadJacobi
DeterminanteEspectral = _mod.DeterminanteEspectral
FormulaExplicitaWeil = _mod.FormulaExplicitaWeil
CoherenciaPuentesMathlib = _mod.CoherenciaPuentesMathlib
SistemaPuentesMathlib = _mod.SistemaPuentesMathlib
puentes_mathlib_qcal_activar = _mod.puentes_mathlib_qcal_activar

PRIMOS_BASE = _mod.PRIMOS_BASE
CEROS_RIEMANN = _mod.CEROS_RIEMANN
EPSILON = _mod.EPSILON
PSI_UMBRAL = _mod.PSI_UMBRAL
W_SC1 = _mod.W_SC1
W_SC2 = _mod.W_SC2
W_SC3 = _mod.W_SC3


# ════════════════════════════════════════════════════════════════════════════
# 1. ConstantesPuentesMathlib
# ════════════════════════════════════════════════════════════════════════════

class TestConstantesPuentesMathlib:
    def test_frozen(self):
        ctes = ConstantesPuentesMathlib()
        with pytest.raises(Exception):
            ctes.f0 = 0.0  # type: ignore[misc]

    def test_pesos_suma_unidad(self):
        ctes = ConstantesPuentesMathlib()
        assert ctes.pesos_suma_unidad()

    def test_frecuencia_resonante(self):
        ctes = ConstantesPuentesMathlib()
        assert ctes.frecuencia_resonante() == pytest.approx(141.7001)

    def test_resumen_keys(self):
        ctes = ConstantesPuentesMathlib()
        r = ctes.resumen()
        for key in ("f0", "f_888", "psi_umbral", "sello", "ram", "n_primos", "n_ceros"):
            assert key in r

    def test_n_primos_n_ceros(self):
        ctes = ConstantesPuentesMathlib()
        assert ctes.resumen()["n_primos"] == len(PRIMOS_BASE)
        assert ctes.resumen()["n_ceros"] == len(CEROS_RIEMANN)


# ════════════════════════════════════════════════════════════════════════════
# 2. OperadorSchatten
# ════════════════════════════════════════════════════════════════════════════

class TestOperadorSchatten:
    def test_norma_schatten_empty(self):
        op = OperadorSchatten()
        assert op.norma_schatten([]) == 0.0

    def test_norma_traza(self):
        op = OperadorSchatten()
        assert op.norma_traza([1.0, 2.0, 3.0]) == pytest.approx(6.0)

    def test_norma_hilbert_schmidt(self):
        op = OperadorSchatten()
        assert op.norma_hilbert_schmidt([3.0, 4.0]) == pytest.approx(5.0)

    def test_norma_schatten_p2(self):
        op = OperadorSchatten(p=2)
        singulares = [1.0, 2.0, 3.0]
        expected = math.sqrt(1 + 4 + 9)
        assert op.norma_schatten(singulares) == pytest.approx(expected)

    def test_es_traza_clase_empty(self):
        op = OperadorSchatten()
        assert op.es_traza_clase([])

    def test_es_traza_clase_finite(self):
        op = OperadorSchatten()
        assert op.es_traza_clase([0.1, 0.2, 0.3])

    def test_valores_singulares_weil_positive(self):
        op = OperadorSchatten()
        svs = op.valores_singulares_weil(PRIMOS_BASE, k=2)
        assert all(s > 0 for s in svs)
        assert len(svs) == len(PRIMOS_BASE)

    def test_weil_k2_nuclear(self):
        op = OperadorSchatten()
        result = op.verificar_nuclearidad_weil(PRIMOS_BASE, k=2)
        assert result["es_nuclear"]
        assert result["norma_s1"] > 0
        assert result["norma_s2"] > 0
        assert result["k"] == 2

    def test_weil_k1_nuclear(self):
        op = OperadorSchatten()
        result = op.verificar_nuclearidad_weil(PRIMOS_BASE, k=1)
        assert result["es_nuclear"]

    def test_norma_s1_leq_s2_scaled(self):
        # ‖A‖₂ ≤ ‖A‖₁ for finite operators (in general)
        op = OperadorSchatten()
        singulares = [0.1, 0.2, 0.4, 0.5]
        assert op.norma_hilbert_schmidt(singulares) <= op.norma_traza(singulares)


# ════════════════════════════════════════════════════════════════════════════
# 3. DeterminanteFredholm
# ════════════════════════════════════════════════════════════════════════════

class TestDeterminanteFredholm:
    def test_det_fredholm_empty(self):
        df = DeterminanteFredholm()
        assert df.det_fredholm(complex(1.0), []) == pytest.approx(complex(1.0), abs=1e-10)

    def test_det_fredholm_single_eigenvalue(self):
        df = DeterminanteFredholm()
        # det(I - 0.5 * 0.2) = 1 - 0.1 = 0.9
        val = df.det_fredholm(complex(0.5), [complex(0.2)])
        assert val.real == pytest.approx(0.9, rel=1e-6)
        assert abs(val.imag) < 1e-10

    def test_det_fredholm_real(self):
        df = DeterminanteFredholm()
        # det(I - 0*A) = 1
        assert df.det_fredholm_real(0.0, [0.5, 0.3]) == pytest.approx(1.0)
        # det(I - 1*[0.5]) = 0.5
        assert df.det_fredholm_real(1.0, [0.5]) == pytest.approx(0.5)

    def test_es_funcion_entera(self):
        df = DeterminanteFredholm()
        assert df.es_funcion_entera([complex(0.1), complex(0.2)])

    def test_orden_hadamard_trace_class(self):
        df = DeterminanteFredholm()
        # Small eigenvalues → trace class → order 1
        eigs = [complex(0.01 * i) for i in range(1, 6)]
        assert df.orden_hadamard(eigs) == 1

    def test_ceros_fredholm(self):
        df = DeterminanteFredholm()
        eigs = [complex(0.5), complex(0.25)]
        zeros = df.ceros_fredholm(eigs)
        assert len(zeros) == 2
        # z_i = 1/λ_i
        assert zeros[0] == pytest.approx(complex(2.0), abs=1e-10)
        assert zeros[1] == pytest.approx(complex(4.0), abs=1e-10)

    def test_log_det_consistency(self):
        df = DeterminanteFredholm()
        eigs = [complex(0.1, 0.05), complex(0.15, -0.02)]
        z = complex(0.5, 0.1)
        det_direct = df.det_fredholm(z, eigs)
        log_det = df.log_det_fredholm(z, eigs)
        assert abs(cmath.exp(log_det) - det_direct) < 1e-10


# ════════════════════════════════════════════════════════════════════════════
# 4. IdentidadJacobi
# ════════════════════════════════════════════════════════════════════════════

class TestIdentidadJacobi:
    def test_traza_empty(self):
        ij = IdentidadJacobi()
        assert ij.traza_operador([]) == complex(0.0)

    def test_traza_sum(self):
        ij = IdentidadJacobi()
        eigs = [complex(1.0, 0.0), complex(2.0, 0.0), complex(3.0, 0.0)]
        assert ij.traza_operador(eigs) == pytest.approx(complex(6.0), abs=1e-10)

    def test_det_exponencial_consistency(self):
        ij = IdentidadJacobi()
        eigs = [complex(0.3, 0.1), complex(0.2, -0.1)]
        via_traza = ij.det_exponencial(eigs)
        via_prod = ij.det_exponencial_producto(eigs)
        assert abs(via_traza - via_prod) < 1e-10

    def test_verificar_jacobi(self):
        ij = IdentidadJacobi()
        eigs = [complex(0.5, g) for g in CEROS_RIEMANN]
        assert ij.verificar_jacobi(eigs, tolerancia=1e-6)

    def test_error_jacobi_near_zero(self):
        ij = IdentidadJacobi()
        eigs = [complex(0.1, 0.0), complex(-0.1, 0.0)]
        assert ij.error_jacobi(eigs) < 1e-10

    def test_psi_jacobi_in_range(self):
        ij = IdentidadJacobi()
        eigs = [complex(0.5, g) for g in CEROS_RIEMANN]
        psi = ij.psi_jacobi(eigs)
        assert 0.0 <= psi <= 1.0

    def test_identidad_jacobi_log(self):
        ij = IdentidadJacobi()
        eigs = [complex(1.0, 0.0), complex(2.0, 0.0)]
        result = ij.identidad_jacobi_log(eigs)
        assert result == pytest.approx(complex(3.0), abs=1e-10)


# ════════════════════════════════════════════════════════════════════════════
# 5. DeterminanteEspectral
# ════════════════════════════════════════════════════════════════════════════

class TestDeterminanteEspectral:
    def test_det_espectral_empty(self):
        de = DeterminanteEspectral()
        assert de.det_espectral(complex(1.0), []) == pytest.approx(complex(1.0))

    def test_det_espectral_zero_at_eigenvalue(self):
        de = DeterminanteEspectral()
        lam = complex(2.0, 3.0)
        val = de.det_espectral(lam, [lam])
        assert abs(val) < 1e-12

    def test_det_espectral_product(self):
        de = DeterminanteEspectral()
        eigs = [complex(1.0), complex(2.0), complex(3.0)]
        s = complex(0.0)
        expected = (-1.0) * (-2.0) * (-3.0)  # (0-1)(0-2)(0-3) = -6
        val = de.det_espectral(s, eigs)
        assert val.real == pytest.approx(expected, abs=1e-10)

    def test_log_det_consistency(self):
        de = DeterminanteEspectral()
        eigs = [complex(0.5, g) for g in CEROS_RIEMANN[:3]]
        s = complex(2.0, 1.0)
        delta = de.det_espectral(s, eigs)
        log_d = de.log_det_espectral(s, eigs)
        assert abs(cmath.exp(log_d) - delta) / max(abs(delta), EPSILON) < 1e-8

    def test_ceros_espectrales(self):
        de = DeterminanteEspectral()
        eigs = [complex(0.5, g) for g in CEROS_RIEMANN[:3]]
        ceros = de.ceros_espectrales(eigs)
        assert len(ceros) == 3

    def test_xi_equivalencia_keys(self):
        de = DeterminanteEspectral()
        res = de.xi_equivalencia(complex(2.0, 1.0))
        for key in ("s", "delta_s", "log_delta_s", "n_ceros", "zeros_usados"):
            assert key in res

    def test_traza_calor_real(self):
        de = DeterminanteEspectral()
        eigs = [complex(1.0), complex(2.0)]
        # Tr(e^{-0*H}) = number of eigenvalues
        t0 = de.traza_calor(0.0, eigs)
        assert abs(t0.real - 2.0) < 1e-10

    def test_verificar_hadamard(self):
        de = DeterminanteEspectral()
        eigs = [complex(0.5, g) for g in CEROS_RIEMANN[:4]]
        result = de.verificar_hadamard(eigs, n_puntos=3)
        assert result["n_puntos"] == 3
        assert result["error_max"] < 1e-6
        assert result["es_valido"]


# ════════════════════════════════════════════════════════════════════════════
# 6. FormulaExplicitaWeil
# ════════════════════════════════════════════════════════════════════════════

class TestFormulaExplicitaWeil:
    def test_suma_sobre_ceros_positive_real(self):
        fw = FormulaExplicitaWeil()
        f_hat = lambda rho: complex(1.0 / (1.0 + rho.imag ** 2), 0.0)
        total = fw.suma_sobre_ceros(f_hat)
        assert total.real > 0

    def test_suma_sobre_primos_positive(self):
        fw = FormulaExplicitaWeil()
        f_fn = lambda x: math.exp(-x)
        total = fw.suma_sobre_primos(f_fn)
        assert total > 0

    def test_termino_infinito(self):
        fw = FormulaExplicitaWeil()
        val = fw.termino_infinito(1.0)
        # log(2π) + γ_Euler ≈ 2.415
        assert val == pytest.approx(math.log(2 * math.pi) + 0.5772156649015329, rel=1e-6)

    def test_verificar_formula_weil_returns_keys(self):
        fw = FormulaExplicitaWeil()
        f_hat = lambda rho: complex(math.exp(-rho.imag ** 2), 0.0)
        f_fn = lambda x: math.exp(-x * x)
        res = fw.verificar_formula_weil(f_hat, f_fn, 1.0)
        for key in ("lado_ceros", "lado_primos_puro", "termino_infinito",
                    "lado_primos_total", "error_relativo", "es_valida"):
            assert key in res

    def test_psi_sc3_in_range(self):
        fw = FormulaExplicitaWeil()
        psi = fw.psi_sc3()
        assert 0.0 <= psi <= 1.0

    def test_suma_sobre_ceros_conjugate_symmetry(self):
        fw = FormulaExplicitaWeil(gamma_zeros=[10.0, 20.0])
        # For a real-valued f_hat that depends on |Im(ρ)|, conjugate contributions are equal
        f_hat = lambda rho: complex(math.exp(-0.01 * rho.imag ** 2), 0.0)
        total = fw.suma_sobre_ceros(f_hat, gamma_zeros=[10.0])
        # Both γ and -γ contribute e^{-0.01*100}, so total ≈ 2*e^{-1}
        expected = 2.0 * math.exp(-0.01 * 100)
        assert total.real == pytest.approx(expected, rel=1e-8)


# ════════════════════════════════════════════════════════════════════════════
# 7. CoherenciaPuentesMathlib
# ════════════════════════════════════════════════════════════════════════════

class TestCoherenciaPuentesMathlib:
    def test_psi_sc1_in_range(self):
        coh = CoherenciaPuentesMathlib()
        psi = coh.psi_sc1()
        assert 0.0 <= psi <= 1.0

    def test_psi_sc2_unity(self):
        # Jacobi identity holds exactly for finite eigenvalues → psi ≈ 1
        coh = CoherenciaPuentesMathlib()
        psi = coh.psi_sc2()
        assert psi >= 0.99

    def test_psi_sc3_in_range(self):
        coh = CoherenciaPuentesMathlib()
        psi = coh.psi_sc3()
        assert 0.0 <= psi <= 1.0

    def test_psi_global_keys(self):
        coh = CoherenciaPuentesMathlib()
        g = coh.psi_global()
        for key in ("psi_sc1", "psi_sc2", "psi_sc3", "psi_global"):
            assert key in g

    def test_psi_global_weighted_sum(self):
        coh = CoherenciaPuentesMathlib()
        g = coh.psi_global()
        expected = W_SC1 * g["psi_sc1"] + W_SC2 * g["psi_sc2"] + W_SC3 * g["psi_sc3"]
        assert g["psi_global"] == pytest.approx(expected, abs=1e-8)

    def test_psi_global_in_range(self):
        coh = CoherenciaPuentesMathlib()
        g = coh.psi_global()
        assert 0.0 <= g["psi_global"] <= 1.0

    def test_cumple_umbral_returns_bool(self):
        coh = CoherenciaPuentesMathlib()
        result = coh.cumple_umbral()
        assert isinstance(result, bool)


# ════════════════════════════════════════════════════════════════════════════
# 8. SistemaPuentesMathlib & API pública
# ════════════════════════════════════════════════════════════════════════════

class TestSistemaPuentesMathlib:
    def test_ejecutar_sc1_keys(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.ejecutar_sc1()
        for key in ("puente", "nombre", "nuclearidad", "det_fredholm_z1",
                    "es_funcion_entera", "orden_hadamard", "psi_sc1", "estado"):
            assert key in res

    def test_ejecutar_sc1_nuclear(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.ejecutar_sc1()
        assert res["nuclearidad"]["es_nuclear"]
        assert res["es_funcion_entera"]

    def test_ejecutar_sc2_keys(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.ejecutar_sc2()
        for key in ("puente", "nombre", "jacobi_verificada", "error_jacobi",
                    "hadamard", "xi_equivalencia", "psi_sc2", "estado"):
            assert key in res

    def test_ejecutar_sc2_jacobi_ok(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.ejecutar_sc2()
        assert res["jacobi_verificada"]
        assert res["error_jacobi"] < 1e-10
        assert res["hadamard"]["es_valido"]

    def test_ejecutar_sc3_keys(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.ejecutar_sc3()
        for key in ("puente", "nombre", "verificacion_weil", "psi_sc3", "estado"):
            assert key in res

    def test_activar_returns_complete_dict(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.activar()
        for key in ("sello", "ram", "timestamp", "f0_hz", "sc1", "sc2", "sc3",
                    "coherencia", "cumple_umbral_qcal", "psi_umbral",
                    "constantes", "estado_global"):
            assert key in res

    def test_activar_sello(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.activar()
        assert "PMQ" in res["sello"]
        assert res["f0_hz"] == pytest.approx(141.7001)

    def test_activar_psi_umbral(self):
        sistema = SistemaPuentesMathlib()
        res = sistema.activar()
        assert res["psi_umbral"] == PSI_UMBRAL


class TestPublicApi:
    def test_puentes_mathlib_qcal_activar_no_args(self):
        res = puentes_mathlib_qcal_activar()
        assert isinstance(res, dict)
        assert "sello" in res
        assert "coherencia" in res

    def test_puentes_mathlib_qcal_activar_custom_constantes(self):
        ctes = ConstantesPuentesMathlib(
            primos_base=(2, 3, 5),
            ceros_riemann=(14.134725, 21.022040, 25.010858),
        )
        res = puentes_mathlib_qcal_activar(constantes=ctes)
        assert res["constantes"]["n_primos"] == 3
        assert res["constantes"]["n_ceros"] == 3

    def test_coherencia_values_consistent(self):
        res = puentes_mathlib_qcal_activar()
        coh = res["coherencia"]
        expected_global = W_SC1 * coh["psi_sc1"] + W_SC2 * coh["psi_sc2"] + W_SC3 * coh["psi_sc3"]
        assert coh["psi_global"] == pytest.approx(expected_global, abs=1e-8)

    def test_estado_global_string(self):
        res = puentes_mathlib_qcal_activar()
        assert isinstance(res["estado_global"], str)
        assert res["estado_global"] in ("✓ QCAL-COHERENTE", "✗ SUB-UMBRAL")

    def test_timestamp_format(self):
        res = puentes_mathlib_qcal_activar()
        # Should be ISO format datetime
        ts = res["timestamp"]
        from datetime import datetime
        # Should parse without error
        datetime.fromisoformat(ts)
