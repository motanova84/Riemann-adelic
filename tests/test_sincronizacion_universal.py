#!/usr/bin/env python3
r"""
Tests for physics/sincronizacion_universal.py
==============================================

Validates the Universal Synchronization Equation module that derives
f₀ ≈ 141,700.1 Hz from fundamental physical constants:

    f₀ = c / (2π √(λ_p · L_Λ)) · Φ²/N₇

where Φ = π/8 (Chern-Simons phase) and N₇ = 7 (C₇ ring order).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

# Ensure physics directory is importable
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "physics"))

from sincronizacion_universal import (
    COSMOLOGICAL_CONSTANT,
    F0_TOLERANCE_RELATIVE,
    HBAR,
    L_LAMBDA,
    LAMBDA_PROTON,
    N7,
    PHI_CS,
    PROTON_MASS,
    PSI_THRESHOLD,
    SPEED_OF_LIGHT,
    ConstantesSincronizacion,
    EcuacionSincronizacion,
    EscalaHolografica,
    ResultadoSincronizacion,
    SistemaSincronizacion,
    VerificadorCoherencia,
)


# ============================================================================
# Module-level constants
# ============================================================================


class TestModuleConstants:
    """Verify that module-level constants match physical values."""

    def test_speed_of_light(self):
        assert abs(SPEED_OF_LIGHT - 299_792_458.0) < 1.0

    def test_proton_mass(self):
        assert abs(PROTON_MASS - 1.672e-27) < 1e-30

    def test_lambda_proton_order_of_magnitude(self):
        # λ_p = ℏ/(m_p c) ≈ 2.103 × 10⁻¹⁶ m
        assert 1.9e-16 < LAMBDA_PROTON < 2.3e-16

    def test_lambda_proton_derivation(self):
        # Verify λ_p = ℏ / (m_p c)
        expected = HBAR / (PROTON_MASS * SPEED_OF_LIGHT)
        assert abs(LAMBDA_PROTON - expected) / expected < 1e-10

    def test_cosmological_constant_order(self):
        # Λ ≈ 1.1 × 10⁻⁵² m⁻²
        assert 1.0e-52 < COSMOLOGICAL_CONSTANT < 1.2e-52

    def test_l_lambda_order_of_magnitude(self):
        # L_Λ = Λ^{-1/4}: should be in [1e11, 1e14] m
        assert 1e11 < L_LAMBDA < 1e14

    def test_l_lambda_derivation(self):
        expected = COSMOLOGICAL_CONSTANT ** (-0.25)
        assert abs(L_LAMBDA - expected) / expected < 1e-10

    def test_phi_cs_value(self):
        # Φ = π/8
        assert abs(PHI_CS - math.pi / 8.0) < 1e-15

    def test_n7_value(self):
        assert N7 == 7

    def test_psi_threshold(self):
        assert 0.0 < PSI_THRESHOLD < 1.0


# ============================================================================
# EscalaHolografica
# ============================================================================


class TestEscalaHolografica:
    """Validate the holographic length scale L_Λ."""

    def test_default_L_lambda(self):
        esc = EscalaHolografica()
        expected = COSMOLOGICAL_CONSTANT ** (-0.25)
        assert abs(esc.L_Lambda - expected) / expected < 1e-10

    def test_custom_lambda(self):
        esc = EscalaHolografica(Lambda=1.0e-52)
        assert abs(esc.L_Lambda - (1.0e-52) ** (-0.25)) / esc.L_Lambda < 1e-10

    def test_l_lambda_in_au_range(self):
        # L_Λ should be in [5, 200] AU (Λ^{-1/4} with Λ ≈ 1.1 × 10⁻⁵² m⁻²  ≈ 65 AU)
        esc = EscalaHolografica()
        au = esc.longitud_en_au()
        assert 5.0 < au < 200.0

    def test_celda_volumen_positive(self):
        esc = EscalaHolografica()
        assert esc.celda_volumen() > 0

    def test_celda_volumen_formula(self):
        esc = EscalaHolografica()
        expected = (4.0 / 3.0) * math.pi * esc.L_Lambda ** 3
        assert abs(esc.celda_volumen() - expected) / expected < 1e-10

    def test_negative_lambda_raises(self):
        with pytest.raises(ValueError):
            EscalaHolografica(Lambda=-1.0e-52)

    def test_zero_lambda_raises(self):
        with pytest.raises(ValueError):
            EscalaHolografica(Lambda=0.0)

    def test_resumen_keys(self):
        esc = EscalaHolografica()
        r = esc.resumen()
        assert "Lambda [m^-2]" in r
        assert "L_Lambda [m]" in r
        assert "L_Lambda [AU]" in r
        assert "V_celda [m^3]" in r


# ============================================================================
# ConstantesSincronizacion
# ============================================================================


class TestConstantesSincronizacion:
    """Validate the constants container."""

    def test_c_value(self):
        ctes = ConstantesSincronizacion()
        assert abs(ctes.c - SPEED_OF_LIGHT) < 1.0

    def test_lambda_p_value(self):
        ctes = ConstantesSincronizacion()
        assert abs(ctes.lambda_p - LAMBDA_PROTON) / LAMBDA_PROTON < 1e-10

    def test_L_lambda_value(self):
        ctes = ConstantesSincronizacion()
        assert abs(ctes.L_Lambda - L_LAMBDA) / L_LAMBDA < 1e-10

    def test_phi_cs_value(self):
        ctes = ConstantesSincronizacion()
        assert abs(ctes.phi_cs - math.pi / 8.0) < 1e-15

    def test_n7_value(self):
        ctes = ConstantesSincronizacion()
        assert ctes.N7 == 7

    def test_resumen_has_au_entry(self):
        ctes = ConstantesSincronizacion()
        r = ctes.resumen()
        assert "L_Lambda [AU]" in r
        assert r["L_Lambda [AU]"] > 0


# ============================================================================
# EcuacionSincronizacion
# ============================================================================


class TestEcuacionSincronizacion:
    """Validate the Universal Synchronization Equation."""

    @pytest.fixture
    def eq(self):
        return EcuacionSincronizacion()

    @pytest.fixture
    def resultado(self, eq):
        return eq.calcular()

    def test_resultado_has_required_keys(self, resultado):
        required = {
            "sqrt_lambda_p_L_Lambda",
            "f_base",
            "factor_topologico",
            "f0_derivado",
            "f0_referencia",
            "error_relativo",
            "coherente",
        }
        assert required.issubset(resultado.keys())

    def test_sqrt_lambda_p_L_lambda_positive(self, resultado):
        assert resultado["sqrt_lambda_p_L_Lambda"] > 0

    def test_sqrt_formula(self, resultado):
        expected = math.sqrt(LAMBDA_PROTON * L_LAMBDA)
        assert abs(resultado["sqrt_lambda_p_L_Lambda"] - expected) / expected < 1e-10

    def test_f_base_positive(self, resultado):
        assert resultado["f_base"] > 0

    def test_f_base_formula(self, resultado):
        expected = SPEED_OF_LIGHT / (2.0 * math.pi * math.sqrt(LAMBDA_PROTON * L_LAMBDA))
        assert abs(resultado["f_base"] - expected) / expected < 1e-10

    def test_factor_topologico_formula(self, resultado):
        expected = (PHI_CS ** 2) / N7
        assert abs(resultado["factor_topologico"] - expected) / expected < 1e-10

    def test_factor_topologico_positive(self, resultado):
        assert resultado["factor_topologico"] > 0

    def test_f0_derivado_positive(self, resultado):
        assert resultado["f0_derivado"] > 0

    def test_f0_derivado_equals_f_base_times_topo(self, resultado):
        expected = resultado["f_base"] * resultado["factor_topologico"]
        assert abs(resultado["f0_derivado"] - expected) / expected < 1e-10

    def test_f0_referencia_is_141_7001(self, resultado):
        assert abs(resultado["f0_referencia"] - 141.7001) < 1e-4

    def test_error_relativo_is_nonnegative(self, resultado):
        assert resultado["error_relativo"] >= 0.0

    def test_coherente_flag_consistent_with_error(self, resultado):
        expected_coherente = resultado["error_relativo"] < F0_TOLERANCE_RELATIVE
        assert resultado["coherente"] == expected_coherente

    def test_phi_squared_over_n7_value(self):
        # (π/8)² / 7 ≈ 0.022
        val = (math.pi / 8) ** 2 / 7
        assert 0.01 < val < 0.05


# ============================================================================
# VerificadorCoherencia
# ============================================================================


class TestVerificadorCoherencia:
    """Validate the QCAL coherence verifier."""

    @pytest.fixture
    def verificacion(self):
        eq = EcuacionSincronizacion()
        resultado = eq.calcular()
        verif = VerificadorCoherencia(resultado)
        return verif.verificar()

    def test_verificacion_has_required_keys(self, verificacion):
        assert "aprobado" in verificacion
        assert "checks" in verificacion
        assert "psi" in verificacion

    def test_psi_in_unit_interval(self, verificacion):
        assert 0.0 <= verificacion["psi"] <= 1.0

    def test_factor_topologico_positive_check(self, verificacion):
        assert verificacion["checks"]["factor_topologico_positivo"] is True

    def test_L_lambda_range_check(self, verificacion):
        assert verificacion["checks"]["L_lambda_rango_AU"] is True


# ============================================================================
# SistemaSincronizacion (integration)
# ============================================================================


class TestSistemaSincronizacion:
    """Integration tests for the full synchronization system."""

    @pytest.fixture(scope="class")
    def resultado(self):
        sistema = SistemaSincronizacion()
        return sistema.activar(verbose=False)

    def test_resultado_type(self, resultado):
        assert isinstance(resultado, ResultadoSincronizacion)

    def test_resultado_constantes_not_empty(self, resultado):
        assert len(resultado.constantes) > 0

    def test_resultado_escala_holografica_not_empty(self, resultado):
        assert len(resultado.escala_holografica) > 0

    def test_resultado_ecuacion_not_empty(self, resultado):
        assert len(resultado.ecuacion) > 0

    def test_resultado_coherencia_not_empty(self, resultado):
        assert len(resultado.coherencia) > 0

    def test_aprobado_property(self, resultado):
        # aprobado must match coherencia dict
        assert resultado.aprobado == resultado.coherencia["aprobado"]

    def test_resumen_is_string(self, resultado):
        s = resultado.resumen()
        assert isinstance(s, str)
        assert len(s) > 0

    def test_resumen_contains_f0(self, resultado):
        s = resultado.resumen()
        assert "f₀" in s or "f0" in s.lower()

    def test_f0_derivado_is_finite(self, resultado):
        f0 = resultado.ecuacion["f0_derivado"]
        assert math.isfinite(f0)

    def test_f0_derivado_positive(self, resultado):
        f0 = resultado.ecuacion["f0_derivado"]
        assert f0 > 0

    def test_psi_above_zero(self, resultado):
        assert resultado.coherencia["psi"] > 0.0
