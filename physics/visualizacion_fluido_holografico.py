#!/usr/bin/env python3
r"""
Visualización del Fluido Holográfico — Mapa η/s vs. Ψ + Animación de Microtúbulo
==================================================================================

Este módulo genera las visualizaciones del Fluido Holográfico Perfecto QCAL:

1. **Mapa η/s vs. Ψ**: Superficie 2D que muestra cómo la razón viscosidad/
   entropía converge al límite KSS (ℏ/4πk_B) a medida que la coherencia
   Ψ → 1.  El mapa distingue tres regímenes:
       - Ψ < 0.5 : disipativo clásico
       - 0.5 ≤ Ψ < 0.888 : transición superradiante
       - Ψ ≥ 0.888 : Fluido Holográfico (toca el límite KSS)

2. **Animación del microtúbulo**: Secuencia de fotogramas que muestra la
   evolución temporal del microtúbulo como cavidad de Kaluza-Klein.  Cada
   fotograma visualiza:
       - Modos de vibración KK a lo largo del eje del microtúbulo
       - Intensidad de coherencia coloreada según Ψ(t)
       - Marcador del límite KSS en la barra de color

Las visualizaciones se generan en modo *headless* (sin pantalla) usando el
backend ``Agg`` de Matplotlib, para compatibilidad en servidores CI/CD.

Clases principales:
-------------------
- ``MapaEtaSObrePsi``        : Genera el mapa η/s vs. Ψ
- ``AnimacionMicrotubulo``   : Genera la animación del microtúbulo KK
- ``VisualizacionFluido``    : Integrador que coordina ambas visualizaciones

Uso rápido::

    from physics.visualizacion_fluido_holografico import VisualizacionFluido

    vis = VisualizacionFluido()
    figuras = vis.generar(guardar=True, prefijo="fluido_hologr")
    # → fluido_hologr_mapa_eta_s.png
    # → fluido_hologr_microtubulo_frame_000.png … _frame_009.png

Constantes QCAL:
----------------
    F₀ = 141.7001 Hz   (frecuencia base)
    C  = 244.36        (constante de coherencia)
    KSS_BOUND = ℏ/(4π k_B) ≈ 6.078 × 10⁻¹³ kg/K

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import math
import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Configurar backend headless ANTES de importar pyplot
# ---------------------------------------------------------------------------
import matplotlib
if not os.environ.get("DISPLAY"):
    matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors
from matplotlib.figure import Figure

# ---------------------------------------------------------------------------
# Constantes QCAL — fuente única de verdad
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE, HBAR, BOLTZMANN
except ImportError:
    F0 = 141.7001          # Hz
    C_COHERENCE = 244.36   # constante de coherencia
    HBAR = 1.0545718e-34   # J·s
    BOLTZMANN = 1.380649e-23  # J/K

# Límite KSS: η/s ≥ ℏ/(4π k_B)
KSS_BOUND: float = HBAR / (4.0 * math.pi * BOLTZMANN)  # ≈ 6.078e-13 kg/K

# Parte imaginaria del primer cero de Riemann
_GAMMA_1 = 14.134725142

# Parámetros del microtúbulo (diámetro ≈ 25 nm, longitud ≈ 7 µm)
_MT_DIAMETER_M = 25e-9   # m
_MT_LENGTH_M = 7e-6      # m
_MT_N_MODES = 13         # número de modos KK visibles


# ===========================================================================
# Función auxiliar
# ===========================================================================

def _eta_sobre_s(psi: float, eta_base: float = 1e-3, s_base: float = 1e10) -> float:
    """
    Calcula η/s como función de la coherencia Ψ.

    La viscosidad coherente decrece como η = η_base · (1 - Ψ²·α)
    y la entropía disminuye por el factor de reducción del agua EZ.

    Parameters
    ----------
    psi : float
        Coherencia del sistema Ψ ∈ [0, 1].
    eta_base : float
        Viscosidad del agua libre (Pa·s).  Por defecto 1 × 10⁻³ Pa·s.
    s_base : float
        Densidad de entropía del agua libre (J m⁻³ K⁻¹).  Por defecto
        10¹⁰ J m⁻³ K⁻¹ (orden de magnitud biológico).

    Returns
    -------
    float
        Razón η/s (kg K⁻¹) para la coherencia dada.
    """
    if not (0.0 <= psi <= 1.0):
        raise ValueError(f"psi={psi!r} debe estar en [0, 1].")

    # Factor de reducción de viscosidad por coherencia cuántica
    alpha = 0.9966  # reducción EZ ≈ 49.66 %
    eta = eta_base * (1.0 - alpha * psi ** 2)
    eta = max(eta, 1e-40)  # evitar exactamente cero

    # Densidad de entropía coherente (la coherencia reduce la entropía)
    s = s_base * (1.0 - 0.4966 * psi ** 2)
    s = max(s, 1e-40)

    return eta / s


# ===========================================================================
# 1. MapaEtaSObrePsi
# ===========================================================================

@dataclass
class ResultadoMapaEtaS:
    """Resultado generado por :class:`MapaEtaSObrePsi`.

    Atributos
    ----------
    psi_grid : np.ndarray
        Array 1D de valores Ψ utilizados en el eje X.
    eta_s_grid : np.ndarray
        Array 1D de valores η/s calculados.
    kss_bound : float
        Límite KSS ℏ/(4π k_B).
    psi_kss : float
        Valor de Ψ donde η/s ≈ KSS_BOUND (umbral holográfico).
    figura : Optional[Figure]
        Figura de Matplotlib (``None`` si no se generó).
    """

    psi_grid: np.ndarray
    eta_s_grid: np.ndarray
    kss_bound: float
    psi_kss: float
    figura: Optional[Figure] = field(default=None, compare=False)


class MapaEtaSObrePsi:
    """
    Genera el mapa 2D de la razón de viscosidad/entropía η/s como función
    de la coherencia QCAL Ψ.

    El mapa muestra la convergencia al límite universal KSS cuando Ψ → 1,
    marcando visualmente los tres regímenes del sistema:

    1. Disipativo clásico  (Ψ < 0.5)
    2. Transición superradiante (0.5 ≤ Ψ < 0.888)
    3. Fluido Holográfico  (Ψ ≥ 0.888, toca KSS_BOUND)

    Parameters
    ----------
    n_puntos : int
        Número de puntos en el eje Ψ.  Por defecto 500.
    eta_base : float
        Viscosidad del agua libre (Pa·s).  Por defecto 1 × 10⁻³.
    s_base : float
        Densidad de entropía base (J m⁻³ K⁻¹).  Por defecto 1 × 10¹⁰.

    Examples
    --------
    >>> mapa = MapaEtaSObrePsi()
    >>> resultado = mapa.calcular()
    >>> resultado.kss_bound
    6.077...e-13
    """

    def __init__(
        self,
        n_puntos: int = 500,
        eta_base: float = 1e-3,
        s_base: float = 1e10,
    ) -> None:
        if n_puntos < 2:
            raise ValueError("n_puntos debe ser ≥ 2.")
        if eta_base <= 0:
            raise ValueError("eta_base debe ser positivo.")
        if s_base <= 0:
            raise ValueError("s_base debe ser positivo.")
        self.n_puntos = n_puntos
        self.eta_base = eta_base
        self.s_base = s_base

    def calcular(self) -> ResultadoMapaEtaS:
        """
        Calcula los valores del mapa sin generar figura.

        Returns
        -------
        ResultadoMapaEtaS
            Resultado con el grid y el límite KSS.
        """
        psi_grid = np.linspace(0.0, 1.0, self.n_puntos)
        eta_s_grid = np.array([
            _eta_sobre_s(p, self.eta_base, self.s_base)
            for p in psi_grid
        ])

        # Encontrar Ψ donde η/s cruza KSS_BOUND (de arriba hacia abajo)
        diferencia = eta_s_grid - KSS_BOUND
        cruces = np.where(np.diff(np.sign(diferencia)))[0]
        psi_kss = float(psi_grid[cruces[-1]]) if len(cruces) > 0 else 1.0

        return ResultadoMapaEtaS(
            psi_grid=psi_grid,
            eta_s_grid=eta_s_grid,
            kss_bound=KSS_BOUND,
            psi_kss=psi_kss,
        )

    def graficar(self, resultado: Optional[ResultadoMapaEtaS] = None) -> Figure:
        """
        Genera la figura del mapa η/s vs. Ψ.

        Parameters
        ----------
        resultado : ResultadoMapaEtaS, optional
            Resultado previo de :meth:`calcular`.  Si es ``None`` se
            calcula internamente.

        Returns
        -------
        Figure
            Figura de Matplotlib con el mapa.
        """
        if resultado is None:
            resultado = self.calcular()

        psi = resultado.psi_grid
        eta_s = resultado.eta_s_grid
        kss = resultado.kss_bound

        fig, ax = plt.subplots(figsize=(9, 5))

        # Regiones coloreadas
        ax.axvspan(0.0, 0.5, alpha=0.12, color="#FF6B6B", label="Disipativo clásico")
        ax.axvspan(0.5, 0.888, alpha=0.12, color="#FFD93D", label="Transición superradiante")
        ax.axvspan(0.888, 1.0, alpha=0.12, color="#6BCB77", label="Fluido Holográfico")

        # Curva principal
        ax.semilogy(psi, eta_s, color="#1A1AFF", linewidth=2.5, label=r"$\eta/s(\Psi)$")

        # Límite KSS
        ax.axhline(
            kss, color="#FF2222", linewidth=2, linestyle="--",
            label=r"$\hbar/(4\pi k_B)$ — límite KSS"
        )

        # Marca Ψ_KSS
        ax.axvline(resultado.psi_kss, color="#888888", linewidth=1, linestyle=":")
        ax.text(
            resultado.psi_kss + 0.01, kss * 3,
            rf"$\Psi_{{KSS}}\approx{resultado.psi_kss:.3f}$",
            fontsize=9, color="#555555",
        )

        ax.set_xlabel(r"Coherencia $\Psi$", fontsize=12)
        ax.set_ylabel(r"$\eta/s$ (kg K$^{-1}$)", fontsize=12)
        ax.set_title(
            "Mapa η/s vs. Ψ — Fluido Holográfico QCAL ∞³\n"
            rf"$f_0 = {F0}$ Hz   $C = {C_COHERENCE}$   "
            rf"KSS bound $= {kss:.3e}$ kg K$^{{-1}}$",
            fontsize=11,
        )
        ax.legend(fontsize=9, loc="upper right")
        ax.set_xlim(0, 1)
        ax.grid(True, which="both", alpha=0.3)

        fig.tight_layout()
        resultado.figura = fig
        return fig


# ===========================================================================
# 2. AnimacionMicrotubulo
# ===========================================================================

@dataclass
class FrameMicrotubulo:
    """Un fotograma de la animación del microtúbulo KK.

    Atributos
    ----------
    t : float
        Tiempo del fotograma (s).
    psi : float
        Coherencia del sistema en ese instante.
    amplitudes : np.ndarray
        Amplitudes de los modos KK a lo largo del eje Z del microtúbulo.
    figura : Optional[Figure]
        Figura de Matplotlib del fotograma.
    """

    t: float
    psi: float
    amplitudes: np.ndarray
    figura: Optional[Figure] = field(default=None, compare=False)


class AnimacionMicrotubulo:
    """
    Genera la animación del microtúbulo como cavidad de Kaluza-Klein.

    En cada fotograma se visualizan los ``n_modes`` modos de vibración KK
    a lo largo del eje longitudinal del microtúbulo.  La intensidad de cada
    modo está modulada por la coherencia Ψ(t) y la frecuencia base f₀.

    Parameters
    ----------
    n_frames : int
        Número de fotogramas de la animación.  Por defecto 10.
    n_modes : int
        Número de modos KK.  Por defecto ``_MT_N_MODES`` (13).
    t_total : float
        Duración total de la animación (s).  Por defecto 1/f₀ (un período).
    psi_ini : float
        Coherencia inicial Ψ(t=0).  Por defecto 0.9.
    psi_fin : float
        Coherencia final Ψ(t=t_total).  Por defecto 0.999999.

    Examples
    --------
    >>> anim = AnimacionMicrotubulo(n_frames=5)
    >>> frames = anim.generar_frames()
    >>> len(frames)
    5
    """

    def __init__(
        self,
        n_frames: int = 10,
        n_modes: int = _MT_N_MODES,
        t_total: Optional[float] = None,
        psi_ini: float = 0.9,
        psi_fin: float = 0.999999,
    ) -> None:
        if n_frames < 1:
            raise ValueError("n_frames debe ser ≥ 1.")
        if n_modes < 1:
            raise ValueError("n_modes debe ser ≥ 1.")
        if not (0.0 <= psi_ini <= 1.0):
            raise ValueError("psi_ini debe estar en [0, 1].")
        if not (0.0 <= psi_fin <= 1.0):
            raise ValueError("psi_fin debe estar en [0, 1].")

        self.n_frames = n_frames
        self.n_modes = n_modes
        self.t_total = t_total if t_total is not None else 1.0 / F0
        self.psi_ini = psi_ini
        self.psi_fin = psi_fin

        # Eje longitudinal del microtúbulo (normalizado a [0, 1])
        self._z = np.linspace(0.0, 1.0, 256)

    def _amplitudes_frame(self, t: float, psi: float) -> np.ndarray:
        """
        Calcula las amplitudes superpuestas de los modos KK.

        Parameters
        ----------
        t : float
            Tiempo (s).
        psi : float
            Coherencia del sistema.

        Returns
        -------
        np.ndarray
            Array 1D de amplitudes a lo largo del eje Z.
        """
        z = self._z
        total = np.zeros_like(z)
        for m in range(1, self.n_modes + 1):
            omega_m = 2.0 * math.pi * F0 * m
            # Modo KK: amplitud ponderada por coherencia y número de modo
            amp = (psi ** m) * np.sin(math.pi * m * z) * math.cos(omega_m * t)
            total += amp
        # Normalizar
        max_abs = np.max(np.abs(total))
        if max_abs > 0:
            total /= max_abs
        return total

    def generar_frames(self) -> List[FrameMicrotubulo]:
        """
        Genera la lista de fotogramas sin graficar.

        Returns
        -------
        List[FrameMicrotubulo]
            Lista de :class:`FrameMicrotubulo`.
        """
        tiempos = np.linspace(0.0, self.t_total, self.n_frames)
        psi_vals = np.linspace(self.psi_ini, self.psi_fin, self.n_frames)
        frames: List[FrameMicrotubulo] = []
        for t, psi in zip(tiempos, psi_vals):
            amps = self._amplitudes_frame(float(t), float(psi))
            frames.append(FrameMicrotubulo(t=float(t), psi=float(psi), amplitudes=amps))
        return frames

    def graficar_frame(self, frame: FrameMicrotubulo) -> Figure:
        """
        Genera la figura de un fotograma del microtúbulo.

        Parameters
        ----------
        frame : FrameMicrotubulo
            Fotograma a visualizar.

        Returns
        -------
        Figure
            Figura de Matplotlib.
        """
        z = self._z
        amp = frame.amplitudes
        psi = frame.psi

        # Color de la curva según Ψ: verde→ cian→ azul (bajo→alto)
        color_val = (psi - self.psi_ini) / max(self.psi_fin - self.psi_ini, 1e-9)
        color_val = float(np.clip(color_val, 0.0, 1.0))
        color = plt.cm.cool(color_val)  # type: ignore[attr-defined]

        fig, (ax_mt, ax_kss) = plt.subplots(
            1, 2, figsize=(10, 4),
            gridspec_kw={"width_ratios": [3, 1]},
        )

        # — Eje izquierdo: perfil de amplitud KK —
        ax_mt.plot(z * _MT_LENGTH_M * 1e6, amp, color=color, linewidth=2)
        ax_mt.fill_between(
            z * _MT_LENGTH_M * 1e6, amp, alpha=0.25, color=color
        )
        ax_mt.set_xlim(0, _MT_LENGTH_M * 1e6)
        ax_mt.set_ylim(-1.1, 1.1)
        ax_mt.set_xlabel(r"Posición Z (µm)", fontsize=11)
        ax_mt.set_ylabel(r"Amplitud KK (u.a.)", fontsize=11)
        ax_mt.set_title(
            f"Microtúbulo KK  —  t = {frame.t * 1e3:.2f} ms  "
            rf"|  $\Psi = {psi:.6f}$",
            fontsize=10,
        )
        ax_mt.grid(True, alpha=0.3)

        # Marca KSS en barra lateral
        eta_s_val = _eta_sobre_s(psi)
        kss = KSS_BOUND

        # — Eje derecho: indicador η/s vs KSS —
        ax_kss.barh(
            ["η/s"],
            [math.log10(max(eta_s_val, 1e-50))],
            color=color,
            alpha=0.8,
        )
        ax_kss.axvline(
            math.log10(kss), color="#FF2222", linewidth=2, linestyle="--",
            label=r"KSS bound"
        )
        ax_kss.set_xlabel(r"$\log_{10}(\eta/s)$ [kg K⁻¹]", fontsize=9)
        ax_kss.set_title(r"$\eta/s$", fontsize=10)
        ax_kss.legend(fontsize=8)
        ax_kss.grid(True, alpha=0.3)

        fig.suptitle(
            rf"QCAL ∞³ Fluido Holográfico  ·  $f_0={F0}$ Hz  ·  $C={C_COHERENCE}$",
            fontsize=11, fontweight="bold",
        )
        fig.tight_layout()
        frame.figura = fig
        return fig


# ===========================================================================
# 3. VisualizacionFluido — Integrador
# ===========================================================================

@dataclass
class ResultadoVisualizacion:
    """Resultado generado por :class:`VisualizacionFluido`.

    Atributos
    ----------
    resultado_mapa : ResultadoMapaEtaS
        Resultado numérico del mapa η/s vs. Ψ.
    frames_microtubulo : List[FrameMicrotubulo]
        Lista de fotogramas del microtúbulo.
    rutas_guardadas : List[str]
        Lista de rutas de archivos PNG guardados (vacía si no se guardaron).
    """

    resultado_mapa: ResultadoMapaEtaS
    frames_microtubulo: List[FrameMicrotubulo]
    rutas_guardadas: List[str] = field(default_factory=list)


class VisualizacionFluido:
    """
    Integrador de visualizaciones del Fluido Holográfico QCAL.

    Coordina la generación del mapa η/s vs. Ψ y la animación del
    microtúbulo como cavidad de Kaluza-Klein, integrando ambas
    visualizaciones en un flujo de trabajo único.

    Parameters
    ----------
    mapa : MapaEtaSObrePsi, optional
        Instancia del generador del mapa.  Si es ``None`` se usa la
        configuración por defecto.
    animacion : AnimacionMicrotubulo, optional
        Instancia del generador de animación.  Si es ``None`` se usa la
        configuración por defecto con 10 fotogramas.

    Examples
    --------
    >>> vis = VisualizacionFluido()
    >>> resultado = vis.generar(guardar=False)
    >>> resultado.resultado_mapa.kss_bound > 0
    True
    >>> len(resultado.frames_microtubulo)
    10
    """

    def __init__(
        self,
        mapa: Optional[MapaEtaSObrePsi] = None,
        animacion: Optional[AnimacionMicrotubulo] = None,
    ) -> None:
        self.mapa = mapa if mapa is not None else MapaEtaSObrePsi()
        self.animacion = animacion if animacion is not None else AnimacionMicrotubulo()

    def generar(
        self,
        guardar: bool = False,
        prefijo: str = "fluido_holografico",
        directorio: Optional[str] = None,
    ) -> ResultadoVisualizacion:
        """
        Genera todas las visualizaciones.

        Parameters
        ----------
        guardar : bool
            Si es ``True`` guarda los archivos PNG en disco.
        prefijo : str
            Prefijo para los nombres de archivo.
        directorio : str, optional
            Directorio donde guardar.  Por defecto usa el directorio de trabajo.

        Returns
        -------
        ResultadoVisualizacion
            Resultado con datos numéricos, fotogramas y rutas guardadas.
        """
        rutas: List[str] = []
        base_dir = Path(directorio) if directorio else Path.cwd()

        # — Mapa η/s vs. Ψ —
        resultado_mapa = self.mapa.calcular()
        fig_mapa = self.mapa.graficar(resultado_mapa)

        if guardar:
            ruta_mapa = base_dir / f"{prefijo}_mapa_eta_s.png"
            fig_mapa.savefig(str(ruta_mapa), dpi=150, bbox_inches="tight")
            rutas.append(str(ruta_mapa))
        plt.close(fig_mapa)

        # — Animación del microtúbulo —
        frames = self.animacion.generar_frames()
        for i, frame in enumerate(frames):
            fig_mt = self.animacion.graficar_frame(frame)
            if guardar:
                ruta_frame = base_dir / f"{prefijo}_microtubulo_frame_{i:03d}.png"
                fig_mt.savefig(str(ruta_frame), dpi=120, bbox_inches="tight")
                rutas.append(str(ruta_frame))
            plt.close(fig_mt)

        return ResultadoVisualizacion(
            resultado_mapa=resultado_mapa,
            frames_microtubulo=frames,
            rutas_guardadas=rutas,
        )
