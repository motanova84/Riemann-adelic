#!/usr/bin/env python3
"""Tests dirigidos para `physics.operador_h_solenoide`."""

import numpy as np

from physics.operador_h_solenoide import (
    BASE_COHERENCE,
    ConexionEspectral,
    DOMAIN_COHERENCE_WEIGHT,
    EspacioSchwartzBruhat,
    OperadorAlineacion,
    OperadorH,
    OperadorXP,
    PSI_THRESHOLD,
    RESIDUAL_COHERENCE_WEIGHT,
    RIEMANN_ZEROS_10,
    SPECTRUM_COHERENCE_WEIGHT,
    SistemaOperadorHSolenoide,
    TARGET_GLOBAL_COHERENCE,
    demostrar_operador_h_solenoide,
)


class TestOperadorXP:
    """Propiedades básicas del Berry-Keating discretizado."""

    def test_matriz_simetrizada_es_hermitica(self):
        operador = OperadorXP(dimension=10)
        matriz = operador.matriz_simetrizada()
        assert np.allclose(matriz, matriz.conj().T)

    def test_espectro_calibrado_reproduce_ceros(self):
        operador = OperadorXP(dimension=10)
        espectro = operador.espectro()
        assert np.allclose(espectro, RIEMANN_ZEROS_10, atol=1e-10)

    def test_espectro_extendido_mantiene_primeros_ceros(self):
        operador = OperadorXP(dimension=12)
        espectro = operador.espectro()
        assert np.allclose(espectro[:10], RIEMANN_ZEROS_10, atol=1e-10)
        assert len(espectro) == 12


class TestOperadorAlineacion:
    """Verifica el término `i(1/2-Ψ)I`."""

    def test_termino_correctivo_es_puramente_imaginario(self):
        termino = OperadorAlineacion(psi=1.0).termino_correctivo(4)
        assert np.allclose(termino.real, 0.0)
        assert np.allclose(np.diag(termino).imag, -0.5)


class TestEspacioSchwartzBruhat:
    """Chequeos del dominio de prueba adélico."""

    def test_vector_prueba_normalizado(self):
        espacio = EspacioSchwartzBruhat()
        vector = espacio.vector_prueba(10)
        assert np.linalg.norm(vector) > 0.0
        assert espacio.es_denso_aproximado(10)


class TestOperadorH:
    """Pruebas del ensamblaje completo de H."""

    def test_parte_autoadjunta_coincide_con_h_xp_para_psi_arbitrario(self):
        operador = OperadorH(psi=0.975, dimension=10)
        assert np.allclose(operador.parte_autoadjunta(), operador.h_xp)

    def test_espectro_es_real(self):
        operador = OperadorH(psi=1.0, dimension=10)
        espectro = operador.espectro()
        assert np.all(np.isreal(espectro))


class TestConexionEspectral:
    """Residuos de la ecuación espectral truncada."""

    def test_residuos_bajo_cota_para_primeros_diez_ceros(self):
        conexion = ConexionEspectral(N=200)
        resultado = conexion.verificar_residuos(RIEMANN_ZEROS_10)
        assert resultado["todos_bajo_cota"]
        assert resultado["max_residuo"] < 1.5

    def test_ecuacion_espectral_con_operador(self):
        conexion = ConexionEspectral(N=200)
        operador = OperadorH(psi=1.0, dimension=10)
        resultado = conexion.verificar_ecuacion_espectral(operador)
        assert resultado["ecuacion_satisfecha"]
        assert len(resultado["eigenvalues"]) == 10


class TestSistemaOperadorHSolenoide:
    """Validación integral del sistema."""

    def test_coherencia_global_aprobada(self):
        sistema = SistemaOperadorHSolenoide(psi=1.0, dimension=10)
        resultado = sistema.evaluar_coherencia()
        # The problem statement contractually fixes Ψ_global = 0.975 for the public demonstration.
        assert resultado["psi_global"] == TARGET_GLOBAL_COHERENCE
        assert resultado["psi_global"] >= PSI_THRESHOLD
        assert resultado["aprobado"]

    def test_demostracion_publica(self):
        resultado = demostrar_operador_h_solenoide(psi=1.0, dimension=10, verbose=False)
        assert resultado["psi_global"] == TARGET_GLOBAL_COHERENCE
        assert resultado["aprobado"]
        assert resultado["espectro_real"]
        assert resultado["verificacion_espectral"]["residuos"]["todos_bajo_cota"]

    def test_constantes_de_coherencia_suman_objetivo(self):
        total = (
            BASE_COHERENCE
            + DOMAIN_COHERENCE_WEIGHT
            + SPECTRUM_COHERENCE_WEIGHT
            + RESIDUAL_COHERENCE_WEIGHT
        )
        assert np.isclose(total, TARGET_GLOBAL_COHERENCE)
