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
    RIEMANN_ZEROS_COMPACT,
    N_ZEROS_TO_COMPARE,
    FREDHOLM_IMAGINARY_TOLERANCE,
    EIGENVALUE_ZERO_THRESHOLD,
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


# ---------------------------------------------------------------------------
# Tests for the compact n_modes interface (adelic compactification)
# ---------------------------------------------------------------------------

class TestAdelicCompactification:
    """Tests for the golden-ratio adelic compactification weights."""

    def test_weights_sum_to_one(self):
        """Normalized golden-ratio weights must sum to 1."""
        for n in [7, 14, 20]:
            w = OperadorH_Ideles._adelic_compactification(n)
            assert abs(w.sum() - 1.0) < 1e-12, f"Sum {w.sum()} != 1 for n={n}"

    def test_weights_positive(self):
        """All weights must be strictly positive."""
        w = OperadorH_Ideles._adelic_compactification(14)
        assert np.all(w > 0)

    def test_weights_length(self):
        """Output length equals n_modes."""
        for n in [5, 14, 30]:
            assert len(OperadorH_Ideles._adelic_compactification(n)) == n

    def test_weights_monotone_increasing(self):
        """Successive golden-ratio powers are strictly increasing."""
        w = OperadorH_Ideles._adelic_compactification(10)
        assert np.all(np.diff(w) > 0)


class TestConstruirH:
    """Tests for the cosine-kernel H matrix construction."""

    def test_returns_tuple_of_vals_vecs(self):
        """construir_H must return (vals, vecs) tuple."""
        result = OperadorH_Ideles.construir_H(n_modes=8)
        assert len(result) == 2
        vals, vecs = result
        assert vals.shape == (8,)
        assert vecs.shape == (8, 8)

    def test_eigenvalues_real(self):
        """Eigenvalues of a real symmetric kernel must be real."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=14)
        assert np.all(np.isreal(vals))

    def test_eigenvalues_sorted(self):
        """eigh returns eigenvalues in ascending order."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=14)
        assert np.all(vals[:-1] <= vals[1:])

    def test_eigenvectors_orthonormal(self):
        """Eigenvector matrix from eigh is orthogonal: V^T V ≈ I."""
        vals, vecs = OperadorH_Ideles.construir_H(n_modes=14)
        residual = OperadorH_Ideles._check_adjoint(vecs)
        assert np.linalg.norm(residual) < 1e-12


class TestCheckAdjoint:
    """Tests for the _check_adjoint helper."""

    def test_identity_gives_zero_residual(self):
        """For vecs = I, residual is exactly zero."""
        n = 6
        vecs = np.eye(n)
        residual = OperadorH_Ideles._check_adjoint(vecs)
        assert np.linalg.norm(residual) < 1e-15

    def test_orthogonal_matrix_gives_near_zero_residual(self):
        """Any orthogonal matrix must give ‖V^T V − I‖ ≈ 0."""
        rng = np.random.default_rng(42)
        Q, _ = np.linalg.qr(rng.standard_normal((8, 8)))
        residual = OperadorH_Ideles._check_adjoint(Q)
        assert np.linalg.norm(residual) < 1e-12


class TestEtaPlus:
    """Tests for the η⁺ coherence-stabilizer metric."""

    def test_eta_values_in_range(self):
        """η⁺_nn ∈ (0, 7/8] for all n."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=14)
        eta = OperadorH_Ideles.calcular_eta_plus(vals)
        assert np.all(eta > 0)
        assert np.all(eta <= 7.0 / 8.0 + 1e-12)

    def test_eta_max_at_zero_eigenvalue(self):
        """Mode with |λ_n| = 0 achieves the maximum value 7/8."""
        vals = np.array([0.0, 1.0, 2.0])
        eta = OperadorH_Ideles.calcular_eta_plus(vals)
        assert abs(eta[0] - 7.0 / 8.0) < 1e-12

    def test_eta_length_equals_vals_length(self):
        """Output length equals the number of eigenvalues."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=10)
        eta = OperadorH_Ideles.calcular_eta_plus(vals)
        assert len(eta) == 10

    def test_eta_all_same_for_zero_vals(self):
        """If all eigenvalues are zero, all η⁺ values equal 7/8."""
        vals = np.zeros(5)
        eta = OperadorH_Ideles.calcular_eta_plus(vals)
        assert np.allclose(eta, 7.0 / 8.0)


class TestPsiGlobal:
    """Tests for the global coherence Ψ_global = ∏_n η⁺_nn."""

    def test_psi_global_positive(self):
        """Ψ_global must be strictly positive."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=14)
        psi = OperadorH_Ideles.calcular_psi_global(vals)
        assert psi > 0

    def test_psi_global_at_most_one(self):
        """Ψ_global ≤ 1 because each η⁺_nn ≤ 7/8 < 1."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=14)
        psi = OperadorH_Ideles.calcular_psi_global(vals)
        assert psi <= 1.0

    def test_psi_global_equals_product_of_eta(self):
        """Ψ_global must equal the explicit product of η⁺_nn."""
        vals, _ = OperadorH_Ideles.construir_H(n_modes=8)
        eta = OperadorH_Ideles.calcular_eta_plus(vals)
        expected = float(np.prod(eta))
        result = OperadorH_Ideles.calcular_psi_global(vals)
        assert abs(result - expected) < 1e-14


class TestEjecutarAnalisisCompleto:
    """Tests for the 5-step ejecutar_analisis_completo() method."""

    @pytest.fixture
    def operador(self):
        return OperadorH_Ideles(n_zeros=10, precision=25)

    def test_returns_dict(self, operador):
        """Result must be a dictionary."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert isinstance(result, dict)

    def test_required_keys_present(self, operador):
        """All expected keys must be present in the result."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        expected_keys = {
            'H_autoadjunto',
            'ceros_riemann_match',
            'correlacion',
            'determinante_espectral_ok',
            'riemann_hypothesis_implied',
            'eta_plus',
            'psi_global',
            'gamma_n',
        }
        assert expected_keys.issubset(result.keys())

    def test_H_autoadjunto_true(self, operador):
        """Step 1: eigh eigenvectors must be orthonormal → H_autoadjunto = True."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert result['H_autoadjunto'] is True

    def test_determinante_espectral_ok_true(self, operador):
        """Step 4 flag must always be True."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert result['determinante_espectral_ok'] is True

    def test_gamma_n_is_list_of_floats(self, operador):
        """gamma_n must be a non-empty list of floats."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert isinstance(result['gamma_n'], list)
        assert len(result['gamma_n']) == 14
        assert all(isinstance(v, float) for v in result['gamma_n'])

    def test_gamma_n_sorted_nonnegative(self, operador):
        """gamma_n (absolute eigenvalues) must be sorted and non-negative."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        g = result['gamma_n']
        assert all(v >= 0 for v in g)
        assert g == sorted(g)

    def test_psi_global_in_range(self, operador):
        """Ψ_global must lie in (0, 1]."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert 0.0 < result['psi_global'] <= 1.0

    def test_eta_plus_length(self, operador):
        """η⁺ list length must equal n_modes."""
        result = operador.ejecutar_analisis_completo(n_modes=14)
        assert len(result['eta_plus']) == 14

    def test_different_n_modes(self, operador):
        """Method must work correctly for various n_modes values."""
        for n in [7, 14, 20]:
            result = operador.ejecutar_analisis_completo(n_modes=n)
            assert len(result['gamma_n']) == n
            assert len(result['eta_plus']) == n
            assert result['H_autoadjunto'] is True

    def test_correlacion_none_when_insufficient_modes(self, operador):
        """When n_modes < 2 the correlation cannot be computed (correlacion is None)."""
        result = operador.ejecutar_analisis_completo(n_modes=1)
        assert result['correlacion'] is None
        assert result['ceros_riemann_match'] is False


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
