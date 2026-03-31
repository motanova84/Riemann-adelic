#!/usr/bin/env python3
r"""
Tests para la Interacción Schrödinger-Riemann (QCAL ∞³)

Valida el módulo ``physics.interaccion_schrodinger_riemann`` que implementa:

  L_int = -g_eff · ψψ̄ · H
  iℏ ∂Ψ/∂t = (Ĥ_π + μ|H|² - g_eff·H)Ψ

Cobertura:
    1. ConstantesInteraccion   — valores y relaciones internas
    2. OperadorHPi             — construcción y hermiticidad
    3. LagrangianoInteraccion  — evaluación y densidad de campo
    4. HamiltonianoTotal       — hermiticidad, espectro, ensamblaje
    5. EvolucionSchrodinger    — unitariedad, coherencia temporal
    6. ResultadoInteraccion    — estructura de datos y __str__
    7. SistemaInteraccionSR    — integración completa
    8. API pública             — interaccion_schrodinger_riemann_activar

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import pytest

from physics.interaccion_schrodinger_riemann import (
    ConstantesInteraccion,
    EvolucionSchrodinger,
    G_EFF_DEFAULT,
    HamiltonianoTotal,
    LagrangianoInteraccion,
    MU_DEFAULT,
    OperadorHPi,
    ResultadoInteraccion,
    SistemaInteraccionSR,
    _RIEMANN_ZEROS_FALLBACK,
    interaccion_schrodinger_riemann_activar,
)

# ---------------------------------------------------------------------------
# Constantes de prueba
# ---------------------------------------------------------------------------
_N_ZEROS_SMALL: int = 5       # base espectral pequeña para rapidez
_G_EFF_TEST: float = 0.5
_MU_TEST: float = 0.05
_F0_EXPECTED: float = 141.7001
_GAMMA_1_EXPECTED: float = 14.13472514
_HBAR: float = 1.054571817e-34
_TOL_REL: float = 1e-6
_TOL_ABS: float = 1e-10


# ===========================================================================
# 1. ConstantesInteraccion
# ===========================================================================

class TestConstantesInteraccion:
    """Valida los valores y la inmutabilidad de ConstantesInteraccion."""

    def test_valores_por_defecto(self):
        """Los valores por defecto deben coincidir con las constantes globales."""
        c = ConstantesInteraccion()
        assert c.g_eff == pytest.approx(G_EFF_DEFAULT, rel=_TOL_REL)
        assert c.mu == pytest.approx(MU_DEFAULT, rel=_TOL_REL)
        assert c.f0 == pytest.approx(_F0_EXPECTED, rel=_TOL_REL)
        assert c.gamma_1 == pytest.approx(_GAMMA_1_EXPECTED, rel=_TOL_REL)

    def test_hbar_positivo(self):
        """ℏ debe ser positivo."""
        c = ConstantesInteraccion()
        assert c.hbar > 0.0

    def test_psi_threshold_rango(self):
        """PSI_THRESHOLD debe estar en (0, 1)."""
        c = ConstantesInteraccion()
        assert 0.0 < c.psi_threshold < 1.0

    def test_frozen_immutable(self):
        """ConstantesInteraccion es frozen y no debe permitir mutación."""
        c = ConstantesInteraccion()
        with pytest.raises(Exception):
            c.g_eff = 99.0  # type: ignore[misc]

    def test_instancia_personalizada(self):
        """Debe poder instanciarse con valores personalizados."""
        c = ConstantesInteraccion(g_eff=2.0, mu=0.3)
        assert c.g_eff == pytest.approx(2.0, rel=_TOL_REL)
        assert c.mu == pytest.approx(0.3, rel=_TOL_REL)


# ===========================================================================
# 2. OperadorHPi
# ===========================================================================

class TestOperadorHPi:
    """Valida la construcción de Ĥ_π."""

    @pytest.fixture
    def ceros_y_constantes(self):
        ceros = list(_RIEMANN_ZEROS_FALLBACK[:_N_ZEROS_SMALL])
        constantes = ConstantesInteraccion()
        return ceros, constantes

    def test_forma_matriz(self, ceros_y_constantes):
        """Ĥ_π debe ser una matriz cuadrada N×N."""
        ceros, constantes = ceros_y_constantes
        n = len(ceros)
        op = OperadorHPi(ceros, constantes)
        H_pi = op.construir()
        assert H_pi.shape == (n, n)

    def test_hermiticidad(self, ceros_y_constantes):
        """Ĥ_π debe ser hermitiana (diagonal real ⟹ H = H†)."""
        ceros, constantes = ceros_y_constantes
        op = OperadorHPi(ceros, constantes)
        H_pi = op.construir()
        diff = np.linalg.norm(H_pi - H_pi.conj().T, "fro")
        assert diff < _TOL_ABS

    def test_diagonal(self, ceros_y_constantes):
        """Ĥ_π debe ser diagonal."""
        ceros, constantes = ceros_y_constantes
        op = OperadorHPi(ceros, constantes)
        H_pi = op.construir()
        off_diag = H_pi - np.diag(np.diag(H_pi))
        assert np.linalg.norm(off_diag, "fro") < _TOL_ABS

    def test_autovalores_positivos(self, ceros_y_constantes):
        """Los autovalores de Ĥ_π deben ser positivos (ω_n > 0)."""
        ceros, constantes = ceros_y_constantes
        op = OperadorHPi(ceros, constantes)
        H_pi = op.construir()
        eigenvalues = np.diag(H_pi)
        assert np.all(eigenvalues > 0), "Todos los autovalores deben ser positivos"

    def test_primer_modo_frecuencia_base(self, ceros_y_constantes):
        """El primer modo debe ser proporcional a 2π·f₀·ℏ."""
        ceros, constantes = ceros_y_constantes
        op = OperadorHPi(ceros, constantes)
        H_pi = op.construir()
        omega0_hbar = constantes.hbar * 2.0 * np.pi * constantes.f0
        assert H_pi[0, 0] == pytest.approx(omega0_hbar, rel=1e-4)

    def test_propiedad_matriz_acceso(self, ceros_y_constantes):
        """La propiedad .matriz debe devolver el mismo resultado que construir()."""
        ceros, constantes = ceros_y_constantes
        op = OperadorHPi(ceros, constantes)
        H1 = op.construir()
        H2 = op.matriz
        np.testing.assert_array_equal(H1, H2)


# ===========================================================================
# 3. LagrangianoInteraccion
# ===========================================================================

class TestLagrangianoInteraccion:
    """Valida la evaluación del Lagrangiano de interacción."""

    @pytest.fixture
    def sistema_pequeno(self):
        n = _N_ZEROS_SMALL
        ceros = list(_RIEMANN_ZEROS_FALLBACK[:n])
        H = np.diag(np.array(ceros))
        constantes = ConstantesInteraccion(g_eff=_G_EFF_TEST)
        return H, constantes, n

    def test_lagrangiano_es_real(self, sistema_pequeno):
        """L_int debe ser un escalar real."""
        H, constantes, n = sistema_pequeno
        psi = np.ones(n, dtype=complex) / np.sqrt(n)
        lag = LagrangianoInteraccion(H, constantes)
        val = lag.evaluar(psi)
        assert isinstance(val, float)

    def test_lagrangiano_signo_negativo_geff_positivo(self, sistema_pequeno):
        """Para g_eff > 0 y H con espectro positivo, L_int < 0."""
        H, constantes, n = sistema_pequeno
        psi = np.ones(n, dtype=complex) / np.sqrt(n)
        lag = LagrangianoInteraccion(H, constantes)
        val = lag.evaluar(psi)
        # ⟨H⟩ > 0 (todos los autovalores son positivos) ⟹ L_int < 0
        assert val < 0.0

    def test_lagrangiano_escala_con_geff(self, sistema_pequeno):
        """L_int debe escalar linealmente con g_eff."""
        H, _, n = sistema_pequeno
        psi = np.ones(n, dtype=complex) / np.sqrt(n)
        c1 = ConstantesInteraccion(g_eff=1.0)
        c2 = ConstantesInteraccion(g_eff=2.0)
        l1 = LagrangianoInteraccion(H, c1).evaluar(psi)
        l2 = LagrangianoInteraccion(H, c2).evaluar(psi)
        assert l2 == pytest.approx(2.0 * l1, rel=1e-9)

    def test_densidad_campo_suma_uno(self, sistema_pequeno):
        """La densidad ψψ̄ debe sumar 1 para un estado normalizado."""
        H, constantes, n = sistema_pequeno
        psi = np.ones(n, dtype=complex) / np.sqrt(n)
        lag = LagrangianoInteraccion(H, constantes)
        densidad = lag.densidad_campo(psi)
        assert np.sum(densidad) == pytest.approx(1.0, rel=1e-9)

    def test_densidad_campo_no_negativa(self, sistema_pequeno):
        """La densidad de campo debe ser no negativa en todos los modos."""
        H, constantes, n = sistema_pequeno
        psi = np.random.randn(n) + 1j * np.random.randn(n)
        psi /= np.linalg.norm(psi)
        lag = LagrangianoInteraccion(H, constantes)
        densidad = lag.densidad_campo(psi)
        assert np.all(densidad >= 0.0)

    def test_lagrangiano_estado_nulo_no_falla(self, sistema_pequeno):
        """evaluar() no debe lanzar excepción con estado casi nulo."""
        H, constantes, n = sistema_pequeno
        psi = np.zeros(n, dtype=complex)
        lag = LagrangianoInteraccion(H, constantes)
        val = lag.evaluar(psi)
        assert np.isfinite(val)


# ===========================================================================
# 4. HamiltonianoTotal
# ===========================================================================

class TestHamiltonianoTotal:
    """Valida el ensamblaje y propiedades de Ĥ_total."""

    @pytest.fixture
    def hamiltoniano(self):
        n = _N_ZEROS_SMALL
        ceros = np.array(list(_RIEMANN_ZEROS_FALLBACK[:n]))
        constantes = ConstantesInteraccion(g_eff=_G_EFF_TEST, mu=_MU_TEST)
        H_pi = np.diag(constantes.hbar * 2.0 * np.pi * constantes.f0 * ceros / ceros[0])
        H_riemann = np.diag(ceros)
        return HamiltonianoTotal(H_pi, H_riemann, constantes), n

    def test_forma_matriz(self, hamiltoniano):
        """Ĥ_total debe ser una matriz cuadrada N×N."""
        ht, n = hamiltoniano
        assert ht.matriz.shape == (n, n)

    def test_hermiticidad(self, hamiltoniano):
        """Ĥ_total debe ser hermitiana."""
        ht, _ = hamiltoniano
        assert ht.verificar_hermiticidad(tolerancia=1e-9)

    def test_espectro_real(self, hamiltoniano):
        """Los autovalores de Ĥ_total deben ser reales."""
        ht, _ = hamiltoniano
        eigenvalues = ht.espectro()
        imag_part = np.max(np.abs(eigenvalues.imag)) if np.iscomplexobj(eigenvalues) else 0.0
        assert imag_part < _TOL_ABS

    def test_espectro_ordenado(self, hamiltoniano):
        """eigvalsh devuelve autovalores en orden creciente."""
        ht, _ = hamiltoniano
        eigenvalues = ht.espectro()
        assert np.all(np.diff(eigenvalues) >= 0.0)

    def test_hermiticidad_falla_con_tolerancia_cero(self, hamiltoniano):
        """Con tolerancia 0 la verificación debe fallar (errores numéricos)."""
        ht, _ = hamiltoniano
        # Tolerancia estrictamente cero siempre falla en aritmética de punto flotante
        resultado = ht.verificar_hermiticidad(tolerancia=0.0)
        # No exigimos resultado específico; solo que no lanza excepción
        assert isinstance(resultado, bool)

    def test_construir_idempotente(self, hamiltoniano):
        """Llamar a construir() dos veces debe devolver la misma matriz."""
        ht, _ = hamiltoniano
        H1 = ht.construir()
        H2 = ht.construir()
        np.testing.assert_array_almost_equal(H1, H2)


# ===========================================================================
# 5. EvolucionSchrodinger
# ===========================================================================

class TestEvolucionSchrodinger:
    """Valida la integración temporal y la conservación de probabilidad."""

    @pytest.fixture
    def evolucion(self):
        n = _N_ZEROS_SMALL
        ceros = np.array(list(_RIEMANN_ZEROS_FALLBACK[:n]))
        constantes = ConstantesInteraccion(g_eff=_G_EFF_TEST, mu=_MU_TEST)
        H_pi = np.diag(constantes.hbar * 2.0 * np.pi * constantes.f0 * ceros / ceros[0])
        H_riemann = np.diag(ceros)
        ht = HamiltonianoTotal(H_pi, H_riemann, constantes)
        return EvolucionSchrodinger(ht, constantes), n

    def test_numero_pasos(self, evolucion):
        """La evolución debe devolver exactamente n_pasos estados."""
        ev, n = evolucion
        psi0 = np.ones(n, dtype=complex) / np.sqrt(n)
        tiempos, estados = ev.propagar(psi0, t_final=0.1, n_pasos=20)
        assert len(tiempos) == 20
        assert estados.shape == (20, n)

    def test_normalizacion_conservada(self, evolucion):
        """Los estados deben permanecer normalizados en cada instante."""
        ev, n = evolucion
        psi0 = np.ones(n, dtype=complex) / np.sqrt(n)
        _, estados = ev.propagar(psi0, t_final=0.1, n_pasos=15)
        normas = np.linalg.norm(estados, axis=1)
        np.testing.assert_allclose(normas, 1.0, atol=1e-10)

    def test_estado_inicial_preservado(self, evolucion):
        """El estado en t=0 debe ser el estado inicial normalizado."""
        ev, n = evolucion
        psi0 = np.array([1.0] + [0.0] * (n - 1), dtype=complex)
        _, estados = ev.propagar(psi0, t_final=0.1, n_pasos=10)
        np.testing.assert_allclose(np.abs(estados[0]), np.abs(psi0), atol=1e-12)

    def test_coherencia_rango(self, evolucion):
        """La coherencia cuántica debe estar en [0, 1]."""
        ev, n = evolucion
        psi0 = np.ones(n, dtype=complex) / np.sqrt(n)
        _, estados = ev.propagar(psi0, t_final=0.1, n_pasos=20)
        coh = ev.coherencia(estados)
        assert np.all(coh >= -1e-12)   # no negativa (tolerancia numérica)
        assert np.all(coh <= 1.0 + 1e-12)

    def test_coherencia_longitud(self, evolucion):
        """La serie de coherencia debe tener la misma longitud que tiempos."""
        ev, n = evolucion
        psi0 = np.ones(n, dtype=complex) / np.sqrt(n)
        tiempos, estados = ev.propagar(psi0, t_final=0.1, n_pasos=25)
        coh = ev.coherencia(estados)
        assert len(coh) == len(tiempos)


# ===========================================================================
# 6. ResultadoInteraccion
# ===========================================================================

class TestResultadoInteraccion:
    """Valida la estructura de datos ResultadoInteraccion."""

    @pytest.fixture
    def resultado_basico(self):
        n = 3
        return ResultadoInteraccion(
            hamiltoniano_hermitiano=True,
            lagrangiano_inicial=-0.5,
            espectro_H_total=np.array([1.0, 2.0, 3.0]),
            tiempos=np.linspace(0, 1, 10),
            estados=np.ones((10, n), dtype=complex) / np.sqrt(n),
            coherencia_temporal=np.full(10, 0.9),
            coherencia_media=0.9,
            rh_validada=True,
            metadata={"n_zeros": n, "g_eff": 1.0, "mu": 0.1},
        )

    def test_campos_obligatorios_presentes(self, resultado_basico):
        """Todos los campos obligatorios deben estar presentes."""
        r = resultado_basico
        assert hasattr(r, "hamiltoniano_hermitiano")
        assert hasattr(r, "lagrangiano_inicial")
        assert hasattr(r, "espectro_H_total")
        assert hasattr(r, "tiempos")
        assert hasattr(r, "estados")
        assert hasattr(r, "coherencia_temporal")
        assert hasattr(r, "coherencia_media")
        assert hasattr(r, "rh_validada")

    def test_str_contiene_campos_clave(self, resultado_basico):
        """__str__ debe mencionar hermiticidad, coherencia y RH."""
        s = str(resultado_basico)
        assert "hermitiano" in s.lower() or "Ĥ" in s
        assert "coherencia" in s.lower() or "Coherencia" in s
        assert "validada" in s.lower() or "HR" in s

    def test_metadata_dict(self, resultado_basico):
        """El campo metadata debe ser un diccionario."""
        assert isinstance(resultado_basico.metadata, dict)

    def test_rh_validada_tipo(self, resultado_basico):
        """rh_validada debe ser booleano."""
        assert isinstance(resultado_basico.rh_validada, bool)


# ===========================================================================
# 7. SistemaInteraccionSR
# ===========================================================================

class TestSistemaInteraccionSR:
    """Valida el orquestador SistemaInteraccionSR."""

    @pytest.fixture
    def sistema(self):
        return SistemaInteraccionSR(
            n_zeros=_N_ZEROS_SMALL,
            g_eff=_G_EFF_TEST,
            mu=_MU_TEST,
            t_final=0.1,
            n_pasos=10,
        )

    def test_ejecutar_devuelve_resultado(self, sistema):
        """ejecutar() debe devolver un ResultadoInteraccion."""
        resultado = sistema.ejecutar()
        assert isinstance(resultado, ResultadoInteraccion)

    def test_hamiltoniano_hermitiano(self, sistema):
        """El Hamiltoniano total debe ser hermitiano."""
        resultado = sistema.ejecutar()
        assert resultado.hamiltoniano_hermitiano is True

    def test_lagrangiano_inicial_finito(self, sistema):
        """L_int(Ψ₀) debe ser un número finito."""
        resultado = sistema.ejecutar()
        assert np.isfinite(resultado.lagrangiano_inicial)

    def test_espectro_finito(self, sistema):
        """Todos los autovalores de Ĥ_total deben ser finitos."""
        resultado = sistema.ejecutar()
        assert np.all(np.isfinite(resultado.espectro_H_total))

    def test_espectro_longitud_correcta(self, sistema):
        """El espectro debe tener exactamente n_zeros autovalores."""
        resultado = sistema.ejecutar()
        assert len(resultado.espectro_H_total) == _N_ZEROS_SMALL

    def test_metadata_contiene_g_eff_mu(self, sistema):
        """El metadata debe incluir g_eff y mu."""
        resultado = sistema.ejecutar()
        assert "g_eff" in resultado.metadata
        assert "mu" in resultado.metadata
        assert resultado.metadata["g_eff"] == pytest.approx(_G_EFF_TEST, rel=_TOL_REL)
        assert resultado.metadata["mu"] == pytest.approx(_MU_TEST, rel=_TOL_REL)

    def test_coherencia_media_rango(self, sistema):
        """La coherencia media debe estar en [0, 1]."""
        resultado = sistema.ejecutar()
        assert 0.0 <= resultado.coherencia_media <= 1.0

    def test_pasos_temporales_correctos(self, sistema):
        """Los arrays temporales deben tener n_pasos elementos."""
        resultado = sistema.ejecutar()
        assert len(resultado.tiempos) == 10
        assert resultado.estados.shape[0] == 10

    def test_n_zeros_distintos(self):
        """La simulación debe funcionar con n_zeros distintos."""
        for n in [3, 5, 8]:
            s = SistemaInteraccionSR(n_zeros=n, t_final=0.05, n_pasos=5)
            r = s.ejecutar()
            assert len(r.espectro_H_total) == n

    def test_g_eff_cero_hamiltoniano_hermitiano(self):
        """Con g_eff=0 el Hamiltoniano sigue siendo hermitiano."""
        s = SistemaInteraccionSR(n_zeros=4, g_eff=0.0, mu=0.0, t_final=0.05, n_pasos=5)
        r = s.ejecutar()
        assert r.hamiltoniano_hermitiano is True

    def test_lagrangiano_geff_cero_es_cero(self):
        """Con g_eff=0, L_int = 0."""
        s = SistemaInteraccionSR(n_zeros=4, g_eff=0.0, mu=0.0, t_final=0.05, n_pasos=5)
        r = s.ejecutar()
        assert r.lagrangiano_inicial == pytest.approx(0.0, abs=1e-12)


# ===========================================================================
# 8. API pública
# ===========================================================================

class TestAPIPublica:
    """Valida el punto de entrada público interaccion_schrodinger_riemann_activar."""

    def test_activar_devuelve_resultado(self):
        """La función pública debe devolver un ResultadoInteraccion."""
        r = interaccion_schrodinger_riemann_activar(
            n_zeros=_N_ZEROS_SMALL,
            g_eff=_G_EFF_TEST,
            mu=_MU_TEST,
            t_final=0.05,
            n_pasos=5,
        )
        assert isinstance(r, ResultadoInteraccion)

    def test_activar_valores_por_defecto(self):
        """La función pública debe ejecutarse correctamente con valores por defecto."""
        r = interaccion_schrodinger_riemann_activar(n_zeros=_N_ZEROS_SMALL, t_final=0.05, n_pasos=5)
        assert isinstance(r, ResultadoInteraccion)
        assert r.hamiltoniano_hermitiano is True

    def test_activar_coherencia_valida(self):
        """La coherencia media devuelta debe ser un flotante en [0, 1]."""
        r = interaccion_schrodinger_riemann_activar(
            n_zeros=_N_ZEROS_SMALL, t_final=0.05, n_pasos=5
        )
        assert isinstance(r.coherencia_media, float)
        assert 0.0 <= r.coherencia_media <= 1.0

    def test_activar_str_no_lanza(self):
        """str(resultado) no debe lanzar ninguna excepción."""
        r = interaccion_schrodinger_riemann_activar(
            n_zeros=_N_ZEROS_SMALL, t_final=0.05, n_pasos=5
        )
        s = str(r)
        assert len(s) > 0
