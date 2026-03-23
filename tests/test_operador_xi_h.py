#!/usr/bin/env python3
"""
Tests for physics.operador_xi_h — Marco de Hilbert-Pólya Ξ–H
==============================================================

69 pruebas que cubren las 7 clases y propiedades matemáticas clave:
  - Simetría de Φ (función par)
  - ‖T−Tᵀ‖ ≈ 0 (autoadjuntividad de T)
  - ‖H−Hᵀ‖/‖H‖ < 1e-10 (autoadjuntividad de H)
  - Ceros de Ξ coinciden con ceros de Riemann
  - Compatibilidad con estadísticas GUE
  - Coherencia global Ψ = 1.0

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from dataclasses import fields

from physics.operador_xi_h import (
    # Constants
    RIEMANN_ZEROS_10,
    F0_HZ,
    C_QCAL,
    PSI_THRESHOLD,
    DEFAULT_N,
    DEFAULT_L,
    _LOG_EPS,
    _H_SYMM_TOL,
    # Helpers
    _simetrizar,
    _phi_kernel,
    # Dataclasses
    ResultadoNucleo,
    ResultadoOperadorT,
    ResultadoIntensidad,
    ResultadoHamiltonianoXiH,
    ResultadoEspectro,
    ResultadoConexion,
    ResultadoSistemaXiH,
    # Pipeline classes
    NucleoConvolucionPhi,
    OperadorConvolucionT,
    OperadorIntensidadRiemann,
    HamiltonianoXiH,
    EspectroSimple,
    ConexionZerosAutovalores,
    SistemaOperadorXiH,
    # Entry point
    operador_xi_h_activar,
)

# ---------------------------------------------------------------------------
# Fixtures — small grid for fast tests
# ---------------------------------------------------------------------------

SMALL_N = 64
SMALL_L = 6.0


@pytest.fixture(scope="module")
def nucleo_obj():
    return NucleoConvolucionPhi(n_grid=SMALL_N, L=SMALL_L, n_terms=8, n_ceros=10)


@pytest.fixture(scope="module")
def r_nucleo(nucleo_obj):
    return nucleo_obj.calcular()


@pytest.fixture(scope="module")
def r_T(nucleo_obj, r_nucleo):
    op = OperadorConvolucionT(nucleo_obj, r_nucleo)
    return op.construir()


@pytest.fixture(scope="module")
def r_int(r_T):
    return OperadorIntensidadRiemann(r_T).calcular()


@pytest.fixture(scope="module")
def r_ham(r_int, r_T):
    return HamiltonianoXiH(r_int, r_T).calcular()


@pytest.fixture(scope="module")
def r_esp(r_nucleo, r_ham):
    return EspectroSimple(r_nucleo, r_ham).verificar()


@pytest.fixture(scope="module")
def r_con(r_nucleo, r_ham, r_T):
    return ConexionZerosAutovalores(r_nucleo, r_ham, r_T).mapear()


@pytest.fixture(scope="module")
def resultado_sistema():
    """Full pipeline result (cached for the module)."""
    return operador_xi_h_activar(n_grid=SMALL_N)


# ===========================================================================
# 1. Constants
# ===========================================================================


class TestConstants:
    """Tests for module-level constants."""

    def test_riemann_zeros_length(self):
        assert len(RIEMANN_ZEROS_10) == 10

    def test_riemann_zeros_first(self):
        assert abs(RIEMANN_ZEROS_10[0] - 14.134725) < 1e-4

    def test_riemann_zeros_increasing(self):
        assert np.all(np.diff(RIEMANN_ZEROS_10) > 0)

    def test_f0_hz(self):
        assert abs(F0_HZ - 141.7001) < 1e-4

    def test_c_qcal(self):
        assert abs(C_QCAL - 244.36) < 1e-4

    def test_psi_threshold(self):
        assert 0.0 < PSI_THRESHOLD <= 1.0

    def test_default_n(self):
        assert DEFAULT_N > 0

    def test_default_l(self):
        assert DEFAULT_L > 0.0

    def test_log_eps_small(self):
        assert _LOG_EPS < 1e-8

    def test_h_symm_tol(self):
        assert _H_SYMM_TOL < 1e-8


# ===========================================================================
# 2. Helpers
# ===========================================================================


class TestHelpers:
    """Tests for internal helper functions."""

    def test_simetrizar_symmetric_input(self):
        A = np.array([[1.0, 2.0], [2.0, 3.0]])
        result = _simetrizar(A)
        np.testing.assert_allclose(result, A)

    def test_simetrizar_asymmetric_input(self):
        A = np.array([[1.0, 3.0], [1.0, 2.0]])
        result = _simetrizar(A)
        np.testing.assert_allclose(result, result.T)

    def test_simetrizar_shape_preserved(self):
        A = np.random.rand(5, 5)
        result = _simetrizar(A)
        assert result.shape == (5, 5)

    def test_phi_kernel_even(self):
        u = np.linspace(-4.0, 4.0, 128)
        phi = _phi_kernel(u)
        phi_neg = _phi_kernel(-u[::-1])
        np.testing.assert_allclose(phi, phi_neg[::-1], atol=1e-10)

    def test_phi_kernel_real(self):
        u = np.linspace(-3.0, 3.0, 64)
        phi = _phi_kernel(u)
        assert phi.dtype == float

    def test_phi_kernel_shape(self):
        u = np.linspace(-2.0, 2.0, 32)
        phi = _phi_kernel(u)
        assert phi.shape == u.shape

    def test_phi_kernel_peak_at_zero(self):
        u = np.linspace(-4.0, 4.0, 256)
        phi = _phi_kernel(u)
        center_idx = np.argmin(np.abs(u))
        max_idx = np.argmax(np.abs(phi))
        # Maximum of |Φ| should be near u=0
        assert abs(u[max_idx]) < 2.0


# ===========================================================================
# 3. NucleoConvolucionPhi
# ===========================================================================


class TestNucleoConvolucionPhi:
    """Tests for NucleoConvolucionPhi class."""

    def test_default_init(self):
        nc = NucleoConvolucionPhi()
        assert nc.n_grid == DEFAULT_N
        assert nc.L == DEFAULT_L

    def test_custom_init(self):
        nc = NucleoConvolucionPhi(n_grid=32, L=5.0, n_terms=4, n_ceros=5)
        assert nc.n_grid == 32
        assert nc.L == 5.0
        assert nc.n_terms == 4
        assert nc.n_ceros == 5

    def test_calcular_returns_result_nucleo(self, r_nucleo):
        assert isinstance(r_nucleo, ResultadoNucleo)

    def test_u_grid_shape(self, r_nucleo):
        assert r_nucleo.u.shape == (SMALL_N,)

    def test_phi_shape(self, r_nucleo):
        assert r_nucleo.phi.shape == (SMALL_N,)

    def test_phi_is_even(self, r_nucleo):
        """Φ(u) = Φ(−u) — KEY MATHEMATICAL PROPERTY."""
        phi = r_nucleo.phi
        # With symmetric grid, phi[i] should equal phi[N-1-i]
        np.testing.assert_allclose(phi, phi[::-1], atol=1e-10,
                                   err_msg="Φ must be an even function")

    def test_es_par_flag(self, r_nucleo):
        assert r_nucleo.es_par is True

    def test_ceros_xi_count(self, r_nucleo):
        assert r_nucleo.n_ceros == 10

    def test_ceros_xi_first(self, r_nucleo):
        assert abs(r_nucleo.ceros_xi[0] - 14.13) < 0.5

    def test_ceros_xi_increasing(self, r_nucleo):
        ceros = np.array(r_nucleo.ceros_xi, dtype=float)
        assert np.all(np.diff(ceros) > 0)

    def test_ceros_xi_known_values(self, r_nucleo):
        """Detected zeros should be close to known Riemann zeros."""
        for detected, known in zip(r_nucleo.ceros_xi, RIEMANN_ZEROS_10):
            assert abs(float(detected) - known) < 1.0

    def test_t_grid_shape(self, r_nucleo):
        assert r_nucleo.t_grid.shape == (SMALL_N,)

    def test_xi_t_shape(self, r_nucleo):
        assert r_nucleo.xi_t.shape == (SMALL_N,)

    def test_xi_t_real(self, r_nucleo):
        assert r_nucleo.xi_t.dtype == float


# ===========================================================================
# 4. OperadorConvolucionT
# ===========================================================================


class TestOperadorConvolucionT:
    """Tests for OperadorConvolucionT class."""

    def test_construir_returns_result(self, r_T):
        assert isinstance(r_T, ResultadoOperadorT)

    def test_kernel_matrix_shape(self, r_T):
        assert r_T.K.shape == (SMALL_N, SMALL_N)

    def test_kernel_matrix_symmetric(self, r_T):
        """‖K − Kᵀ‖ = 0 — CORE SELF-ADJOINTNESS TEST."""
        asym = np.linalg.norm(r_T.K - r_T.K.T)
        assert asym < 1e-10, f"K must be symmetric; ‖K−Kᵀ‖ = {asym}"

    def test_autoadjunto_flag(self, r_T):
        assert r_T.autoadjunto is True

    def test_norma_asimetria_small(self, r_T):
        assert r_T.norma_asimetria < 1e-10

    def test_autovalores_shape(self, r_T):
        assert r_T.autovalores.shape == (SMALL_N,)

    def test_autovalores_real(self, r_T):
        assert r_T.autovalores.dtype == float

    def test_autovalores_sorted(self, r_T):
        avs = r_T.autovalores
        np.testing.assert_array_equal(avs, np.sort(avs))

    def test_kernel_matrix_real(self, r_T):
        assert r_T.K.dtype == float


# ===========================================================================
# 5. OperadorIntensidadRiemann
# ===========================================================================


class TestOperadorIntensidadRiemann:
    """Tests for OperadorIntensidadRiemann class."""

    def test_calcular_returns_result(self, r_int):
        assert isinstance(r_int, ResultadoIntensidad)

    def test_abs_T_shape(self, r_int):
        assert r_int.abs_T.shape == (SMALL_N, SMALL_N)

    def test_abs_T_symmetric(self, r_int):
        asym = np.linalg.norm(r_int.abs_T - r_int.abs_T.T)
        assert asym < 1e-10

    def test_abs_T_positive_semidefinite(self, r_int):
        """All eigenvalues of |T| must be ≥ 0."""
        assert np.all(r_int.autovalores_abs >= -1e-10)

    def test_positivo_flag(self, r_int):
        assert r_int.positivo is True

    def test_norma_negatividad(self, r_int):
        assert r_int.norma_negatividad < _LOG_EPS

    def test_autovalores_abs_shape(self, r_int):
        assert r_int.autovalores_abs.shape == (SMALL_N,)

    def test_abs_T_real(self, r_int):
        assert r_int.abs_T.dtype == float


# ===========================================================================
# 6. HamiltonianoXiH
# ===========================================================================


class TestHamiltonianoXiH:
    """Tests for HamiltonianoXiH class."""

    def test_calcular_returns_result(self, r_ham):
        assert isinstance(r_ham, ResultadoHamiltonianoXiH)

    def test_H_shape(self, r_ham):
        assert r_ham.H.shape == (SMALL_N, SMALL_N)

    def test_H_symmetric(self, r_ham):
        """‖H − Hᵀ‖/‖H‖ < 1e-10 — CORE HERMITICITY TEST."""
        H = r_ham.H
        norm_H = np.linalg.norm(H)
        asym_rel = np.linalg.norm(H - H.T) / (norm_H + _LOG_EPS)
        assert asym_rel < _H_SYMM_TOL, (
            f"H must be symmetric; ‖H−Hᵀ‖/‖H‖ = {asym_rel}"
        )

    def test_autoadjunto_flag(self, r_ham):
        assert r_ham.autoadjunto is True

    def test_norma_asimetria_relativa(self, r_ham):
        assert r_ham.norma_asimetria_relativa < _H_SYMM_TOL

    def test_autovalores_H_shape(self, r_ham):
        assert r_ham.autovalores_H.shape == (SMALL_N,)

    def test_autovalores_H_real(self, r_ham):
        assert r_ham.autovalores_H.dtype == float

    def test_singularidades_not_empty(self, r_ham):
        assert len(r_ham.singularidades) > 0

    def test_H_real(self, r_ham):
        assert r_ham.H.dtype == float


# ===========================================================================
# 7. EspectroSimple
# ===========================================================================


class TestEspectroSimple:
    """Tests for EspectroSimple class."""

    def test_verificar_returns_result(self, r_esp):
        assert isinstance(r_esp, ResultadoEspectro)

    def test_multiplicidad_1(self, r_esp):
        assert r_esp.multiplicidad_1 is True

    def test_gue_ok(self, r_esp):
        """GUE level-repulsion statistics — COMPATIBILITY TEST."""
        assert r_esp.gue_ok is True

    def test_derivada_no_cero(self, r_esp):
        """Ξ′(t_n) ≠ 0 at each detected zero."""
        assert r_esp.derivada_no_cero is True

    def test_gaps_positive(self, r_esp):
        assert np.all(r_esp.gaps > 0)

    def test_p_value_gue_range(self, r_esp):
        assert 0.0 <= r_esp.p_value_gue <= 1.0

    def test_derivada_en_ceros_count(self, r_esp):
        assert len(r_esp.derivada_en_ceros) == 10

    def test_derivada_en_ceros_nonzero(self, r_esp):
        for d in r_esp.derivada_en_ceros:
            assert abs(d) > 1e-10

    def test_gaps_shape(self, r_esp):
        # gaps of 10 zeros → 9 gaps
        assert len(r_esp.gaps) == 9


# ===========================================================================
# 8. ConexionZerosAutovalores
# ===========================================================================


class TestConexionZerosAutovalores:
    """Tests for ConexionZerosAutovalores class."""

    def test_mapear_returns_result(self, r_con):
        assert isinstance(r_con, ResultadoConexion)

    def test_zeros_coinciden(self, r_con):
        """10/10 coincidencias — CORE SPECTRAL MAPPING TEST."""
        assert r_con.zeros_coinciden is True

    def test_n_coincidencias(self, r_con):
        assert r_con.n_coincidencias == 10

    def test_n_total(self, r_con):
        assert r_con.n_total == 10

    def test_mapa_keys(self, r_con):
        keys = list(r_con.mapa.keys())
        assert len(keys) == 10

    def test_mapa_values_finite(self, r_con):
        for v in r_con.mapa.values():
            assert np.isfinite(v)

    def test_tolerancia_usada(self, r_con):
        assert r_con.tolerancia_usada > 0.0


# ===========================================================================
# 9. SistemaOperadorXiH (pipeline)
# ===========================================================================


class TestSistemaOperadorXiH:
    """Tests for the integrated SistemaOperadorXiH pipeline."""

    def test_ejecutar_returns_result(self, resultado_sistema):
        assert isinstance(resultado_sistema, ResultadoSistemaXiH)

    def test_autoadjunto(self, resultado_sistema):
        assert resultado_sistema.autoadjunto is True

    def test_espectro_simple_ok(self, resultado_sistema):
        assert resultado_sistema.espectro_simple_ok is True

    def test_zeros_coinciden(self, resultado_sistema):
        assert resultado_sistema.zeros_coinciden is True

    def test_coherencia_global_1(self, resultado_sistema):
        """Coherencia global Ψ = 1.0 — GLOBAL PIPELINE TEST."""
        assert resultado_sistema.coherencia_global == pytest.approx(1.0, abs=1e-9)

    def test_ceros_xi_count(self, resultado_sistema):
        assert resultado_sistema.nucleo.n_ceros == 10

    def test_ceros_xi_first_value(self, resultado_sistema):
        first = float(resultado_sistema.nucleo.ceros_xi[0])
        assert abs(first - 14.13) < 1.0

    def test_metadata_keys(self, resultado_sistema):
        assert "f0_hz" in resultado_sistema.metadata
        assert "c_qcal" in resultado_sistema.metadata
        assert "doi" in resultado_sistema.metadata

    def test_resumen_returns_string(self, resultado_sistema):
        s = resultado_sistema.resumen()
        assert isinstance(s, str)
        assert len(s) > 50

    def test_resumen_contains_coherencia(self, resultado_sistema):
        s = resultado_sistema.resumen()
        assert "1.0000" in s

    def test_verbose_mode(self, capsys):
        sistema = SistemaOperadorXiH(n_grid=SMALL_N)
        sistema.ejecutar(verbose=True)
        captured = capsys.readouterr()
        assert "[1/6]" in captured.out
        assert "[6/6]" in captured.out


# ===========================================================================
# 10. operador_xi_h_activar entry point
# ===========================================================================


class TestActivar:
    """Tests for the public operador_xi_h_activar() entry point."""

    def test_returns_resultado_sistema(self, resultado_sistema):
        assert isinstance(resultado_sistema, ResultadoSistemaXiH)

    def test_autoadjunto_true(self, resultado_sistema):
        assert resultado_sistema.autoadjunto is True

    def test_espectro_simple_true(self, resultado_sistema):
        assert resultado_sistema.espectro_simple_ok is True

    def test_zeros_coinciden_true(self, resultado_sistema):
        assert resultado_sistema.zeros_coinciden is True

    def test_coherencia_1(self, resultado_sistema):
        assert resultado_sistema.coherencia_global == pytest.approx(1.0, abs=1e-9)

    def test_ceros_known_values(self, resultado_sistema):
        """Known Riemann zeros: [14.13, 21.02, 25.01, 30.42, ...]."""
        expected = [14.13, 21.02, 25.01, 30.42]
        for i, exp in enumerate(expected):
            detected = float(resultado_sistema.nucleo.ceros_xi[i])
            assert abs(detected - exp) < 1.0, (
                f"Zero {i}: expected ≈{exp}, got {detected}"
            )

    def test_custom_n_grid(self):
        r = operador_xi_h_activar(n_grid=32)
        assert isinstance(r, ResultadoSistemaXiH)

    def test_default_call(self):
        r = operador_xi_h_activar()
        assert isinstance(r, ResultadoSistemaXiH)

    def test_nucleo_is_result_nucleo(self, resultado_sistema):
        assert isinstance(resultado_sistema.nucleo, ResultadoNucleo)

    def test_operador_T_is_result_T(self, resultado_sistema):
        assert isinstance(resultado_sistema.operador_T, ResultadoOperadorT)

    def test_intensidad_is_result_intensidad(self, resultado_sistema):
        assert isinstance(resultado_sistema.intensidad, ResultadoIntensidad)

    def test_hamiltoniano_is_result(self, resultado_sistema):
        assert isinstance(resultado_sistema.hamiltoniano, ResultadoHamiltonianoXiH)

    def test_espectro_is_result(self, resultado_sistema):
        assert isinstance(resultado_sistema.espectro, ResultadoEspectro)

    def test_conexion_is_result(self, resultado_sistema):
        assert isinstance(resultado_sistema.conexion, ResultadoConexion)
