#!/usr/bin/env python3
"""
Tests para Visualización del Fluido Holográfico
================================================

Valida el mapa η/s vs. Ψ y la animación del microtúbulo como
cavidad de Kaluza-Klein del módulo
``physics.visualizacion_fluido_holografico``.

Cobertura:
    1. MapaEtaSObrePsi  — cálculo numérico y graficado
    2. AnimacionMicrotubulo — generación de fotogramas
    3. VisualizacionFluido  — integrador completo
    4. Importaciones desde physics (paquete)

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import math

import numpy as np
import pytest

from physics.visualizacion_fluido_holografico import (
    KSS_BOUND,
    AnimacionMicrotubulo,
    FrameMicrotubulo,
    MapaEtaSObrePsi,
    ResultadoMapaEtaS,
    ResultadoVisualizacion,
    VisualizacionFluido,
    _eta_sobre_s,
)


# ===========================================================================
# Función auxiliar _eta_sobre_s
# ===========================================================================

class TestEtaSobreS:
    """Valida la función auxiliar _eta_sobre_s."""

    def test_decrece_con_psi(self):
        """η/s debe decrecer a medida que Ψ aumenta."""
        valores = [_eta_sobre_s(p) for p in np.linspace(0.0, 0.999, 50)]
        assert all(v1 >= v2 for v1, v2 in zip(valores, valores[1:]))

    def test_positivo_siempre(self):
        """η/s debe ser siempre positivo."""
        for psi in [0.0, 0.5, 0.888, 0.999]:
            assert _eta_sobre_s(psi) > 0.0

    def test_psi_invalido_lanza_error(self):
        """Debe lanzar ValueError si psi está fuera de [0,1]."""
        with pytest.raises(ValueError):
            _eta_sobre_s(1.5)
        with pytest.raises(ValueError):
            _eta_sobre_s(-0.1)

    def test_converge_hacia_kss(self):
        """Para Ψ alto, η/s debe acercarse o ser comparable al KSS_BOUND."""
        val_alto = _eta_sobre_s(0.99999)
        val_bajo = _eta_sobre_s(0.001)
        assert val_alto < val_bajo


# ===========================================================================
# 1. MapaEtaSObrePsi
# ===========================================================================

class TestMapaEtaSObrePsi:
    """Valida el generador del mapa η/s vs. Ψ."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse con parámetros por defecto."""
        mapa = MapaEtaSObrePsi()
        assert mapa.n_puntos == 500
        assert mapa.eta_base > 0
        assert mapa.s_base > 0

    def test_instanciacion_invalida_n_puntos(self):
        """Debe lanzar ValueError si n_puntos < 2."""
        with pytest.raises(ValueError):
            MapaEtaSObrePsi(n_puntos=1)

    def test_instanciacion_invalida_eta_base(self):
        """Debe lanzar ValueError si eta_base <= 0."""
        with pytest.raises(ValueError):
            MapaEtaSObrePsi(eta_base=-1.0)

    def test_instanciacion_invalida_s_base(self):
        """Debe lanzar ValueError si s_base <= 0."""
        with pytest.raises(ValueError):
            MapaEtaSObrePsi(s_base=0.0)

    def test_calcular_devuelve_resultado(self):
        """calcular() debe devolver ResultadoMapaEtaS."""
        mapa = MapaEtaSObrePsi(n_puntos=100)
        resultado = mapa.calcular()
        assert isinstance(resultado, ResultadoMapaEtaS)

    def test_calcular_grid_longitud(self):
        """El grid Ψ debe tener la longitud pedida."""
        mapa = MapaEtaSObrePsi(n_puntos=200)
        resultado = mapa.calcular()
        assert len(resultado.psi_grid) == 200
        assert len(resultado.eta_s_grid) == 200

    def test_kss_bound_correcto(self):
        """KSS_BOUND debe ser ≈ ℏ/(4π k_B) ≈ 6.08 × 10⁻¹³."""
        mapa = MapaEtaSObrePsi()
        resultado = mapa.calcular()
        assert 6.0e-13 < resultado.kss_bound < 6.2e-13

    def test_psi_grid_en_0_1(self):
        """El grid Ψ debe estar en [0, 1]."""
        mapa = MapaEtaSObrePsi(n_puntos=50)
        resultado = mapa.calcular()
        assert resultado.psi_grid[0] == pytest.approx(0.0)
        assert resultado.psi_grid[-1] == pytest.approx(1.0)

    def test_eta_s_positivo(self):
        """Todos los valores η/s deben ser positivos."""
        mapa = MapaEtaSObrePsi(n_puntos=50)
        resultado = mapa.calcular()
        assert np.all(resultado.eta_s_grid > 0)

    def test_psi_kss_en_rango(self):
        """El umbral Ψ_KSS debe estar en [0, 1]."""
        mapa = MapaEtaSObrePsi(n_puntos=100)
        resultado = mapa.calcular()
        assert 0.0 <= resultado.psi_kss <= 1.0

    def test_graficar_devuelve_figura(self):
        """graficar() debe devolver un objeto Figure."""
        import matplotlib
        matplotlib.use("Agg")
        from matplotlib.figure import Figure
        mapa = MapaEtaSObrePsi(n_puntos=50)
        fig = mapa.graficar()
        assert isinstance(fig, Figure)
        import matplotlib.pyplot as plt
        plt.close(fig)


# ===========================================================================
# 2. AnimacionMicrotubulo
# ===========================================================================

class TestAnimacionMicrotubulo:
    """Valida la animación del microtúbulo KK."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse con parámetros por defecto."""
        anim = AnimacionMicrotubulo()
        assert anim.n_frames == 10
        assert anim.n_modes == 13

    def test_n_frames_invalido(self):
        """Debe lanzar ValueError si n_frames < 1."""
        with pytest.raises(ValueError):
            AnimacionMicrotubulo(n_frames=0)

    def test_n_modes_invalido(self):
        """Debe lanzar ValueError si n_modes < 1."""
        with pytest.raises(ValueError):
            AnimacionMicrotubulo(n_modes=0)

    def test_psi_ini_invalido(self):
        """Debe lanzar ValueError si psi_ini fuera de [0,1]."""
        with pytest.raises(ValueError):
            AnimacionMicrotubulo(psi_ini=1.5)

    def test_psi_fin_invalido(self):
        """Debe lanzar ValueError si psi_fin fuera de [0,1]."""
        with pytest.raises(ValueError):
            AnimacionMicrotubulo(psi_fin=-0.1)

    def test_generar_frames_longitud(self):
        """generar_frames() debe devolver n_frames fotogramas."""
        anim = AnimacionMicrotubulo(n_frames=5)
        frames = anim.generar_frames()
        assert len(frames) == 5

    def test_frames_son_FrameMicrotubulo(self):
        """Cada fotograma debe ser FrameMicrotubulo."""
        anim = AnimacionMicrotubulo(n_frames=3)
        frames = anim.generar_frames()
        for f in frames:
            assert isinstance(f, FrameMicrotubulo)

    def test_psi_evoluciona(self):
        """La coherencia debe aumentar entre el primer y el último frame."""
        anim = AnimacionMicrotubulo(n_frames=5, psi_ini=0.9, psi_fin=0.999)
        frames = anim.generar_frames()
        assert frames[0].psi < frames[-1].psi

    def test_amplitudes_normalizadas(self):
        """Las amplitudes de cada frame deben estar en [-1, 1]."""
        anim = AnimacionMicrotubulo(n_frames=3, n_modes=5)
        frames = anim.generar_frames()
        for f in frames:
            assert np.all(np.abs(f.amplitudes) <= 1.0 + 1e-10)

    def test_graficar_frame_devuelve_figura(self):
        """graficar_frame() debe devolver un Figure."""
        import matplotlib
        matplotlib.use("Agg")
        from matplotlib.figure import Figure
        anim = AnimacionMicrotubulo(n_frames=1, n_modes=3)
        frames = anim.generar_frames()
        fig = anim.graficar_frame(frames[0])
        assert isinstance(fig, Figure)
        import matplotlib.pyplot as plt
        plt.close(fig)


# ===========================================================================
# 3. VisualizacionFluido (Integrador)
# ===========================================================================

class TestVisualizacionFluido:
    """Valida el integrador de visualizaciones."""

    def test_instanciacion_por_defecto(self):
        """Debe instanciarse con mapa y animación por defecto."""
        vis = VisualizacionFluido()
        assert isinstance(vis.mapa, MapaEtaSObrePsi)
        assert isinstance(vis.animacion, AnimacionMicrotubulo)

    def test_instanciacion_personalizada(self):
        """Debe aceptar instancias personalizadas."""
        mapa = MapaEtaSObrePsi(n_puntos=50)
        anim = AnimacionMicrotubulo(n_frames=3)
        vis = VisualizacionFluido(mapa=mapa, animacion=anim)
        assert vis.mapa.n_puntos == 50
        assert vis.animacion.n_frames == 3

    def test_generar_devuelve_resultado(self):
        """generar() debe devolver ResultadoVisualizacion."""
        vis = VisualizacionFluido(
            mapa=MapaEtaSObrePsi(n_puntos=30),
            animacion=AnimacionMicrotubulo(n_frames=2, n_modes=3),
        )
        resultado = vis.generar(guardar=False)
        assert isinstance(resultado, ResultadoVisualizacion)

    def test_generar_frames_correctos(self):
        """El resultado debe tener el número correcto de frames."""
        n_frames = 4
        vis = VisualizacionFluido(
            mapa=MapaEtaSObrePsi(n_puntos=20),
            animacion=AnimacionMicrotubulo(n_frames=n_frames, n_modes=3),
        )
        resultado = vis.generar(guardar=False)
        assert len(resultado.frames_microtubulo) == n_frames

    def test_generar_sin_guardar_no_crea_archivos(self):
        """Sin guardar no debe crear archivos."""
        vis = VisualizacionFluido(
            mapa=MapaEtaSObrePsi(n_puntos=20),
            animacion=AnimacionMicrotubulo(n_frames=2, n_modes=3),
        )
        resultado = vis.generar(guardar=False)
        assert len(resultado.rutas_guardadas) == 0

    def test_kss_bound_positivo_en_resultado(self):
        """KSS_BOUND en el resultado del mapa debe ser positivo."""
        vis = VisualizacionFluido(
            mapa=MapaEtaSObrePsi(n_puntos=20),
            animacion=AnimacionMicrotubulo(n_frames=2, n_modes=3),
        )
        resultado = vis.generar(guardar=False)
        assert resultado.resultado_mapa.kss_bound > 0.0


# ===========================================================================
# 4. Constante KSS_BOUND
# ===========================================================================

class TestKSSBoundConstante:
    """Valida la constante KSS_BOUND del módulo."""

    def test_kss_bound_valor(self):
        """KSS_BOUND debe ser ≈ ℏ/(4π k_B)."""
        hbar = 1.0545718e-34
        k_b = 1.380649e-23
        esperado = hbar / (4.0 * math.pi * k_b)
        assert abs(KSS_BOUND - esperado) < 1e-18

    def test_kss_bound_orden_magnitud(self):
        """KSS_BOUND debe estar en ~6 × 10⁻¹³ kg/K."""
        assert 6.0e-13 < KSS_BOUND < 6.2e-13


# ===========================================================================
# 5. Importaciones desde physics (paquete)
# ===========================================================================

class TestImportacionesPhysics:
    """Verifica que las nuevas clases se exportan desde physics."""

    def test_importar_desde_physics(self):
        """Todas las clases nuevas deben importarse desde physics."""
        from physics import (
            AnimacionMicrotubulo,
            FrameMicrotubulo,
            KSS_BOUND_VIS,
            MapaEtaSObrePsi,
            ResultadoMapaEtaS,
            ResultadoVisualizacion,
            VisualizacionFluido,
        )
        assert KSS_BOUND_VIS > 0.0
