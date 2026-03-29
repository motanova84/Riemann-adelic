#!/usr/bin/env python3
"""
Tests para el Operador Autoadjunto H (Generador del Flujo de Escala Adélico)
============================================================================

Verifica:
1. Auto-adjunción de H
2. Espectro coincide con partes imaginarias de ceros de ζ
3. Determinante de Fredholm Δ(s) ≡ ξ(s)
4. Coherencia cuántica macroscópica del vacío adélico
5. Condición de Riemann como requisito de estabilidad

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import mpmath as mp

from physics.operador_autoadjunto_H import (
    OperadorH_Ideles,
    operador_h_ideles_activar,
    ResultadoOperadorH,
    AUTOADJOINT_TOLERANCE,
    MACROSCOPIC_COHERENCE_THRESHOLD,
)


class TestOperadorHIdeles:
    """Test suite para OperadorH_Ideles."""

    def test_construccion_basica(self):
        """Test: El operador se construye correctamente."""
        operador = OperadorH_Ideles(n_zeros=10, precision=25)

        assert operador.H is not None
        assert operador.H.shape == (10, 10)
        assert operador.espectro_H is not None
        assert len(operador.espectro_H) == 10

    def test_operador_es_hermitiano(self):
        """Test: H es hermitiano (H = H†)."""
        operador = OperadorH_Ideles(n_zeros=20, precision=25)

        # Verificar hermiticidad
        H_dagger = operador.H.conj().T
        diff = np.linalg.norm(operador.H - H_dagger)

        assert diff < AUTOADJOINT_TOLERANCE

    def test_autoadjuncion_verificada(self):
        """Test: verificar_autoadjuncion() retorna True."""
        operador = OperadorH_Ideles(n_zeros=15, precision=25)

        es_autoadjunto = operador.verificar_autoadjuncion()

        assert es_autoadjunto is True

    def test_espectro_es_real(self):
        """Test: El espectro de H es real (si H es autoadjunto)."""
        operador = OperadorH_Ideles(n_zeros=20, precision=25)

        espectro = operador.obtener_espectro()

        # Todos los autovalores deben ser reales
        assert np.all(np.isreal(espectro))

    def test_espectro_coincide_con_ceros(self):
        """Test: Spec(H) coincide con Im(ρ_n) de los ceros de ζ."""
        n_zeros = 10
        operador = OperadorH_Ideles(n_zeros=n_zeros, precision=30)

        # Obtener ceros de Riemann con mpmath
        with mp.workdps(30):
            ceros_esperados = []
            for n in range(1, n_zeros + 1):
                t_n = mp.zetazero(n)
                ceros_esperados.append(float(mp.im(t_n)))

        espectro = operador.obtener_espectro()

        # Verificar coincidencia (con tolerancia numérica)
        for i, eigenval in enumerate(espectro):
            assert np.abs(eigenval - ceros_esperados[i]) < 0.1

    def test_determinante_fredholm_en_cero(self):
        """Test: Δ(s) en un cero de ζ debería ser cercano a 0."""
        operador = OperadorH_Ideles(n_zeros=20, precision=30)

        # Primer cero: s = 1/2 + i·14.134725...
        with mp.workdps(30):
            t1 = mp.zetazero(1)
            s_cero = complex(0.5, float(mp.im(t1)))

        # Evaluar Δ(s) en el cero
        delta_en_cero = operador.determinante_fredholm(s_cero)

        # Debería ser cercano a 0 (el producto tiene un factor (s - λ_1) ≈ 0)
        assert np.abs(delta_en_cero) < 1.0

    def test_coherencia_cuantica_alta(self):
        """Test: La coherencia cuántica Ψ es alta (cercana a 1)."""
        operador = OperadorH_Ideles(n_zeros=30, precision=35)

        coherencia = operador.validar_coherencia_cuantica()

        # Ψ debe estar cerca de 1.0 si H es correcto
        assert coherencia > 0.95
        assert 0.0 <= coherencia <= 1.0

    def test_validacion_completa(self):
        """Test: ejecutar_validacion_completa() retorna resultado coherente."""
        operador = OperadorH_Ideles(n_zeros=25, precision=30)

        resultado = operador.ejecutar_validacion_completa()

        # Verificaciones básicas
        assert isinstance(resultado, ResultadoOperadorH)
        assert resultado.es_autoadjunto is True
        assert len(resultado.espectro) == 25
        assert resultado.coherencia_cuantica > 0.9
        assert len(resultado.determinante_fredholm_evaluado) > 0

    def test_riemann_hypothesis_condition(self):
        """Test: RH se verifica si H es autoadjunto y Ψ > threshold."""
        operador = OperadorH_Ideles(n_zeros=20, precision=30)

        resultado = operador.ejecutar_validacion_completa()

        # Si H es autoadjunto y Ψ alta, RH debería validarse
        if resultado.es_autoadjunto and resultado.coherencia_cuantica > MACROSCOPIC_COHERENCE_THRESHOLD:
            assert resultado.riemann_hypothesis_ok is True

    def test_contribucion_arquimediana(self):
        """Test: Incluir contribución arquimediana no rompe auto-adjunción."""
        operador_con_arch = OperadorH_Ideles(
            n_zeros=15,
            precision=25,
            include_archimedean=True
        )
        operador_sin_arch = OperadorH_Ideles(
            n_zeros=15,
            precision=25,
            include_archimedean=False
        )

        # Ambos deben ser autoadjuntos
        assert operador_con_arch.verificar_autoadjuncion() is True
        assert operador_sin_arch.verificar_autoadjuncion() is True

        # Las matrices deben ser diferentes
        diff = np.linalg.norm(operador_con_arch.H - operador_sin_arch.H)
        assert diff > 1e-6

    def test_metadata_completa(self):
        """Test: El resultado contiene metadata completa."""
        operador = OperadorH_Ideles(n_zeros=10, precision=25)
        resultado = operador.ejecutar_validacion_completa()

        metadata = resultado.metadata

        assert 'dimension' in metadata
        assert 'precision' in metadata
        assert 'n_zeros' in metadata
        assert 'f0' in metadata
        assert 'c_coherence' in metadata

        assert metadata['dimension'] == 10
        assert metadata['precision'] == 25
        assert metadata['n_zeros'] == 10


class TestFuncionConveniencia:
    """Tests para la función de conveniencia operador_h_ideles_activar."""

    def test_activacion_basica(self):
        """Test: operador_h_ideles_activar() funciona correctamente."""
        resultado = operador_h_ideles_activar(
            n_zeros=15,
            precision=25,
            verbose=False
        )

        assert isinstance(resultado, ResultadoOperadorH)
        assert resultado.es_autoadjunto is True
        assert len(resultado.espectro) == 15

    def test_activacion_con_verbose(self, capsys):
        """Test: verbose=True imprime el resultado."""
        resultado = operador_h_ideles_activar(
            n_zeros=10,
            precision=25,
            verbose=True
        )

        captured = capsys.readouterr()
        assert "OPERADOR AUTOADJUNTO H" in captured.out
        assert "Auto-adjunción" in captured.out

    def test_diferentes_parametros(self):
        """Test: La función funciona con diferentes parámetros."""
        # Pocos ceros, baja precisión
        resultado1 = operador_h_ideles_activar(
            n_zeros=5,
            precision=20,
            verbose=False
        )

        # Más ceros, más precisión
        resultado2 = operador_h_ideles_activar(
            n_zeros=30,
            precision=40,
            verbose=False
        )

        assert len(resultado1.espectro) == 5
        assert len(resultado2.espectro) == 30

        # Ambos deben ser autoadjuntos
        assert resultado1.es_autoadjunto
        assert resultado2.es_autoadjunto


class TestResultadoOperadorH:
    """Tests para la clase ResultadoOperadorH."""

    def test_string_representation(self):
        """Test: __str__() produce output legible."""
        operador = OperadorH_Ideles(n_zeros=10, precision=25)
        resultado = operador.ejecutar_validacion_completa()

        output = str(resultado)

        assert "OPERADOR AUTOADJUNTO H" in output
        assert "Auto-adjunción" in output
        assert "Espectro de H" in output
        assert "Coherencia cuántica" in output
        assert "Hipótesis de Riemann" in output
        assert "Determinante de Fredholm" in output

    def test_resultado_tiene_todos_campos(self):
        """Test: ResultadoOperadorH tiene todos los campos esperados."""
        operador = OperadorH_Ideles(n_zeros=10, precision=25)
        resultado = operador.ejecutar_validacion_completa()

        assert hasattr(resultado, 'es_autoadjunto')
        assert hasattr(resultado, 'espectro')
        assert hasattr(resultado, 'norma_no_autoadjuntividad')
        assert hasattr(resultado, 'determinante_fredholm_evaluado')
        assert hasattr(resultado, 'coherencia_cuantica')
        assert hasattr(resultado, 'riemann_hypothesis_ok')
        assert hasattr(resultado, 'metadata')


@pytest.mark.slow
class TestPrecisionAlta:
    """Tests con alta precisión (pueden ser lentos)."""

    def test_precision_100_dps(self):
        """Test: El operador funciona con precisión de 100 dps."""
        operador = OperadorH_Ideles(n_zeros=10, precision=100)

        resultado = operador.ejecutar_validacion_completa()

        assert resultado.es_autoadjunto
        assert resultado.coherencia_cuantica > 0.95

    def test_muchos_ceros(self):
        """Test: El operador maneja 100 ceros correctamente."""
        operador = OperadorH_Ideles(n_zeros=100, precision=30)

        resultado = operador.ejecutar_validacion_completa()

        assert len(resultado.espectro) == 100
        assert resultado.es_autoadjunto


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
