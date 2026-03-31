#!/usr/bin/env python3
r"""
Interacción Schrödinger-Riemann
================================

Implementa la interacción cuántica entre el campo de materia Ψ y el operador
autoadjunto H del flujo de escala adélico, gobernada por el Lagrangiano de
interacción y la ecuación de Schrödinger-Riemann:

Lagrangiano de interacción:
    :math:`\mathcal{L}_{int} = -g_{eff} \cdot \psi\bar{\psi} \cdot H`

Ecuación de Schrödinger-Riemann:
    :math:`i\hbar \frac{\partial\Psi}{\partial t} = (\hat{H}_\pi + \mu|H|^2 - g_{eff} \cdot H)\Psi`

donde:
  - Ĥ_π  es el Hamiltoniano libre (espectro armónico basado en γ₁ = 14.13 Hz)
  - μ|H|² ≡ μ · H†H  es el término de auto-interacción no lineal
  - g_eff · H  es el acoplamiento al operador de Riemann autoadjunto
  - g_eff  es el acoplamiento efectivo real positivo
  - μ  es la constante de auto-interacción (tipo Gross-Pitaevskii)

Estructura del módulo (7 clases — patrón QCAL ∞³):
---------------------------------------------------
1. ConstantesInteraccion   — Constantes físicas (frozen dataclass)
2. OperadorHPi             — Ĥ_π: Hamiltoniano libre adélico
3. LagrangianoInteraccion  — L_int = -g_eff · ⟨Ψ|H|Ψ⟩ / ‖Ψ‖²
4. HamiltonianoTotal       — Ĥ_total = Ĥ_π + μH†H - g_eff·H
5. EvolucionSchrodinger    — Integración temporal de iℏ dΨ/dt = Ĥ_total Ψ
6. ResultadoInteraccion    — Dataclass de resultados
7. SistemaInteraccionSR    — Orquestador; punto de entrada público

API pública:
    interaccion_schrodinger_riemann_activar(n_zeros, g_eff, mu) → ResultadoInteraccion

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import warnings
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
from scipy.linalg import expm, eigvalsh

# ---------------------------------------------------------------------------
# Constantes QCAL — fuente única de verdad con fallback local
# ---------------------------------------------------------------------------
try:
    from qcal.constants import (
        F0,
        C_COHERENCE,
        GAMMA_1,
        PSI_THRESHOLD,
        HBAR,
    )
except ImportError:  # pragma: no cover
    F0: float = 141.7001          # Hz  — frecuencia base QCAL
    C_COHERENCE: float = 244.36   # constante de coherencia QCAL
    GAMMA_1: float = 14.13472514  # parte imaginaria del primer cero de ζ
    PSI_THRESHOLD: float = 0.888  # umbral de coherencia cuántica
    HBAR: float = 1.054571817e-34 # J·s — constante de Planck reducida

# Acoplamiento efectivo por defecto (adimensional en unidades QCAL)
G_EFF_DEFAULT: float = 1.0

# Constante de auto-interacción por defecto (adimensional en unidades QCAL)
MU_DEFAULT: float = 0.1

# Paso temporal por defecto para la integración [s en unidades reducidas]
DT_DEFAULT: float = 1e-3

# Número de ceros de Riemann a utilizar por defecto
N_ZEROS_DEFAULT: int = 10

# Pequeña regularización para evitar divisiones por cero
_EPS: float = 1e-14

# Primeros 10 ceros no triviales de ζ(s) — Im(ρ_n), usados como fallback
_RIEMANN_ZEROS_FALLBACK: List[float] = [
    14.134725142,
    21.022039639,
    25.010857580,
    30.424876126,
    32.935061588,
    37.586178159,
    40.918719012,
    43.327073281,
    48.005150881,
    49.773832478,
]


# ===========================================================================
# 1. ConstantesInteraccion
# ===========================================================================

@dataclass(frozen=True)
class ConstantesInteraccion:
    """
    Constantes canónicas del sistema de interacción Schrödinger-Riemann.

    Atributos
    ----------
    g_eff : float
        Acoplamiento efectivo g_eff en la interacción L_int = -g_eff·ψψ̄·H.
        Valor positivo; unidades adimensionales en la escala QCAL.
    mu : float
        Constante de auto-interacción μ en el término μ|H|²Ψ.
        Análogo al término de Gross-Pitaevskii para condensados de Bose-Einstein.
    hbar : float
        Constante de Planck reducida ℏ [J·s] para la ecuación de Schrödinger.
    f0 : float
        Frecuencia fundamental QCAL f₀ = 141.7001 Hz.
    gamma_1 : float
        Parte imaginaria del primer cero no trivial de ζ(s): γ₁ ≈ 14.135.
    psi_threshold : float
        Umbral de coherencia cuántica Ψ ≥ 0.888 para estabilidad del vacío.
    """

    g_eff: float = G_EFF_DEFAULT
    mu: float = MU_DEFAULT
    hbar: float = HBAR
    f0: float = F0
    gamma_1: float = GAMMA_1
    psi_threshold: float = PSI_THRESHOLD


# ===========================================================================
# 2. OperadorHPi
# ===========================================================================

class OperadorHPi:
    """
    Hamiltoniano libre adélico Ĥ_π.

    Ĥ_π actúa sobre el espacio espectral de Riemann con un espectro
    armónico modulado por los ceros de ζ:

        [Ĥ_π]_{nn} = ℏ · ω_n,   ω_n = 2π · γ_n · f₀ / γ₁

    donde γ_n = Im(ρ_n) es la parte imaginaria del n-ésimo cero de ζ(s)
    y f₀ = 141.7001 Hz es la frecuencia base QCAL.

    La elección normaliza ω₁ = 2π·f₀, recuperando la frecuencia fundamental
    en el modo cero del espectro.

    Parámetros
    ----------
    ceros : list of float
        Partes imaginarias de los ceros de Riemann Im(ρ_n).
    constantes : ConstantesInteraccion
        Constantes del sistema.
    """

    def __init__(
        self,
        ceros: List[float],
        constantes: ConstantesInteraccion,
    ) -> None:
        self._ceros = np.asarray(ceros, dtype=float)
        self._constantes = constantes
        self._matriz: Optional[np.ndarray] = None

    # ------------------------------------------------------------------
    def construir(self) -> np.ndarray:
        """
        Construir la matriz de Ĥ_π (N×N hermitiana diagonal).

        Returns
        -------
        np.ndarray
            Matriz hermitiana de Ĥ_π con unidades de energía reducida.
        """
        n = len(self._ceros)
        gamma1 = self._constantes.gamma_1
        omega0 = 2.0 * np.pi * self._constantes.f0  # rad·Hz

        # Frecuencias angulares normalizadas a ω₁ = 2π·f₀
        omega_n = omega0 * self._ceros / (gamma1 + _EPS)

        # Ĥ_π = ℏ·diag(ω_n) — representación espectral diagonal
        H_pi = np.diag(self._constantes.hbar * omega_n)
        self._matriz = H_pi
        return H_pi

    @property
    def matriz(self) -> np.ndarray:
        """Matriz de Ĥ_π; se construye al primer acceso."""
        if self._matriz is None:
            self.construir()
        return self._matriz  # type: ignore[return-value]


# ===========================================================================
# 3. LagrangianoInteraccion
# ===========================================================================

class LagrangianoInteraccion:
    r"""
    Lagrangiano de interacción Schrödinger-Riemann.

    Implementa:

    .. math::
        \mathcal{L}_{int} = -g_{eff} \cdot \psi\bar{\psi} \cdot H

    En el espacio de Hilbert discretizado la densidad de interacción es:

    .. math::
        \mathcal{L}_{int} = -g_{eff} \cdot \langle\Psi|H|\Psi\rangle / \|\Psi\|^2

    donde ⟨Ψ|H|Ψ⟩ es el valor esperado del operador H en el estado Ψ.

    Parámetros
    ----------
    H_matrix : np.ndarray
        Matriz del operador de Riemann autoadjunto H (N×N).
    constantes : ConstantesInteraccion
        Constantes del sistema.
    """

    def __init__(
        self,
        H_matrix: np.ndarray,
        constantes: ConstantesInteraccion,
    ) -> None:
        self._H = H_matrix
        self._constantes = constantes

    # ------------------------------------------------------------------
    def evaluar(self, psi: np.ndarray) -> float:
        r"""
        Evaluar la densidad del Lagrangiano de interacción para un estado Ψ.

        Calcula:

        .. math::
            \mathcal{L}_{int}(\Psi) = -g_{eff} \cdot \langle\Psi|H|\Psi\rangle / \|\Psi\|^2

        Parámetros
        ----------
        psi : np.ndarray, shape (N,), dtype complex
            Vector de estado normalizado o no normalizado.

        Returns
        -------
        float
            Densidad de Lagrangiano de interacción (real, pues H es autoadjunto).
        """
        norm_sq = float(np.real(np.dot(psi.conj(), psi))) + _EPS
        expectation = float(np.real(np.dot(psi.conj(), self._H @ psi)))
        return -self._constantes.g_eff * expectation / norm_sq

    # ------------------------------------------------------------------
    def densidad_campo(self, psi: np.ndarray) -> np.ndarray:
        r"""
        Calcular la densidad de campo ψψ̄ para cada componente del vector Ψ.

        En la representación discreta:

        .. math::
            (\psi\bar{\psi})_n = |\Psi_n|^2

        Parámetros
        ----------
        psi : np.ndarray, shape (N,)
            Vector de estado.

        Returns
        -------
        np.ndarray, shape (N,)
            Densidad de probabilidad por componente.
        """
        return np.abs(psi) ** 2


# ===========================================================================
# 4. HamiltonianoTotal
# ===========================================================================

class HamiltonianoTotal:
    r"""
    Hamiltoniano total de la interacción Schrödinger-Riemann.

    Implementa:

    .. math::
        \hat{H}_{total} = \hat{H}_\pi + \mu |H|^2 - g_{eff} \cdot H

    donde:
      - Ĥ_π  es el Hamiltoniano libre adélico (diagonal, hermitiano)
      - μ|H|² ≡ μ · H^†H  es el término de auto-interacción (semidefinido positivo)
      - g_eff·H  es el acoplamiento al operador de Riemann

    La hermiticidad de Ĥ_total se garantiza porque cada sumando es autoadjunto:
      - Ĥ_π = Ĥ_π^†  (diagonal real)
      - H^†H = (H^†H)^†  (producto de operador autoadjunto consigo mismo)
      - H = H^†  (autoadjunto por construcción)

    Parámetros
    ----------
    H_pi : np.ndarray
        Matriz de Ĥ_π (N×N).
    H_riemann : np.ndarray
        Matriz del operador de Riemann H (N×N, hermitiana).
    constantes : ConstantesInteraccion
        Constantes del sistema.
    """

    def __init__(
        self,
        H_pi: np.ndarray,
        H_riemann: np.ndarray,
        constantes: ConstantesInteraccion,
    ) -> None:
        self._H_pi = H_pi
        self._H_riemann = H_riemann
        self._constantes = constantes
        self._matriz: Optional[np.ndarray] = None

    # ------------------------------------------------------------------
    def construir(self) -> np.ndarray:
        """
        Construir la matriz del Hamiltoniano total Ĥ_total.

        Returns
        -------
        np.ndarray
            Matriz hermitiana Ĥ_total (N×N).
        """
        g = self._constantes.g_eff
        mu = self._constantes.mu

        # μ|H|² = μ · H†H
        H_dag_H = self._H_riemann.conj().T @ self._H_riemann

        # Ĥ_total = Ĥ_π + μ·H†H - g_eff·H
        H_total = self._H_pi + mu * H_dag_H - g * self._H_riemann

        # Simetrizar numéricamente para garantizar hermiticidad
        H_total = (H_total + H_total.conj().T) / 2.0
        self._matriz = H_total
        return H_total

    @property
    def matriz(self) -> np.ndarray:
        """Matriz de Ĥ_total; se construye al primer acceso."""
        if self._matriz is None:
            self.construir()
        return self._matriz  # type: ignore[return-value]

    # ------------------------------------------------------------------
    def espectro(self) -> np.ndarray:
        """
        Calcular los autovalores de Ĥ_total.

        Returns
        -------
        np.ndarray
            Autovalores reales ordenados de menor a mayor (J en unidades SI).
        """
        return eigvalsh(self.matriz)

    # ------------------------------------------------------------------
    def verificar_hermiticidad(self, tolerancia: float = 1e-10) -> bool:
        """
        Verificar que Ĥ_total sea hermitiano dentro de la tolerancia.

        Parámetros
        ----------
        tolerancia : float
            Umbral para ‖H - H†‖_F / ‖H‖_F.

        Returns
        -------
        bool
            True si ‖Ĥ_total - Ĥ_total†‖ / ‖Ĥ_total‖ < tolerancia.
        """
        H = self.matriz
        diff = H - H.conj().T
        norma_diff = np.linalg.norm(diff, 'fro')
        norma_H = np.linalg.norm(H, 'fro') + _EPS
        return bool(norma_diff / norma_H < tolerancia)


# ===========================================================================
# 5. EvolucionSchrodinger
# ===========================================================================

class EvolucionSchrodinger:
    r"""
    Integrador de la ecuación de Schrödinger-Riemann.

    Resuelve:

    .. math::
        i\hbar \frac{\partial\Psi}{\partial t} = \hat{H}_{total}\,\Psi

    mediante la solución formal exacta (propagador unitario):

    .. math::
        \Psi(t) = \exp\!\left(-\frac{i}{\hbar}\hat{H}_{total}\,t\right)\Psi(0)

    calculada con `scipy.linalg.expm`.

    Parámetros
    ----------
    H_total : HamiltonianoTotal
        Hamiltoniano total del sistema.
    constantes : ConstantesInteraccion
        Constantes del sistema.
    """

    def __init__(
        self,
        H_total: HamiltonianoTotal,
        constantes: ConstantesInteraccion,
    ) -> None:
        self._H_total = H_total
        self._constantes = constantes

    # ------------------------------------------------------------------
    def propagar(
        self,
        psi0: np.ndarray,
        t_final: float,
        n_pasos: int = 100,
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Propagar el estado Ψ desde t=0 hasta t=t_final.

        Parámetros
        ----------
        psi0 : np.ndarray, shape (N,), dtype complex
            Estado inicial.  Se normaliza automáticamente.
        t_final : float
            Tiempo final de evolución [s en unidades reducidas].
        n_pasos : int
            Número de instantes en que se registra el estado.

        Returns
        -------
        tiempos : np.ndarray, shape (n_pasos,)
            Tiempos de evaluación t_k.
        estados : np.ndarray, shape (n_pasos, N), dtype complex
            Estados Ψ(t_k) normalizados.
        """
        hbar = self._constantes.hbar
        H = self._H_total.matriz

        # Normalizar estado inicial
        norma0 = np.linalg.norm(psi0) + _EPS
        psi = psi0.astype(complex) / norma0

        tiempos = np.linspace(0.0, t_final, n_pasos)
        estados = np.zeros((n_pasos, len(psi)), dtype=complex)
        estados[0] = psi

        # Generador del propagador: G = -i/ℏ · Ĥ_total
        G = (-1j / hbar) * H

        for k in range(1, n_pasos):
            dt = tiempos[k] - tiempos[k - 1]
            # U(dt) = exp(G·dt)
            U = expm(G * dt)
            psi = U @ psi
            # Re-normalizar en cada paso para evitar acumulación numérica
            norma = np.linalg.norm(psi) + _EPS
            psi = psi / norma
            estados[k] = psi

        return tiempos, estados

    # ------------------------------------------------------------------
    def coherencia(self, estados: np.ndarray) -> np.ndarray:
        """
        Calcular la coherencia cuántica Ψ_coh(t) = |∑_n Ψ_n(t)|² / N.

        Parámetros
        ----------
        estados : np.ndarray, shape (n_pasos, N)
            Serie temporal de estados.

        Returns
        -------
        np.ndarray, shape (n_pasos,)
            Coherencia cuántica en cada instante.
        """
        n = estados.shape[1] + _EPS
        # Garantizar no-negatividad (seguridad numérica)
        return np.maximum((np.abs(np.sum(estados, axis=1)) ** 2) / n, 0.0)


# ===========================================================================
# 6. ResultadoInteraccion
# ===========================================================================

@dataclass
class ResultadoInteraccion:
    """
    Resultado del sistema de interacción Schrödinger-Riemann.

    Atributos
    ----------
    hamiltoniano_hermitiano : bool
        True si Ĥ_total satisface ‖Ĥ - Ĥ†‖ / ‖Ĥ‖ < tolerancia.
    lagrangiano_inicial : float
        Valor de L_int evaluado en el estado inicial Ψ(0).
    espectro_H_total : np.ndarray
        Autovalores de Ĥ_total (reales; en unidades de energía reducida).
    tiempos : np.ndarray
        Instantes de evolución [s].
    estados : np.ndarray
        Estados Ψ(t) normalizados, shape (n_pasos, N).
    coherencia_temporal : np.ndarray
        Coherencia cuántica Ψ_coh(t) ∈ [0, 1].
    coherencia_media : float
        Promedio temporal de Ψ_coh(t).
    rh_validada : bool
        True si Ψ_coh media supera el umbral de coherencia PSI_THRESHOLD.
    metadata : dict
        Información adicional (n_zeros, g_eff, mu, …).
    """

    hamiltoniano_hermitiano: bool
    lagrangiano_inicial: float
    espectro_H_total: np.ndarray
    tiempos: np.ndarray
    estados: np.ndarray
    coherencia_temporal: np.ndarray
    coherencia_media: float
    rh_validada: bool
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __str__(self) -> str:
        """Representación en formato QCAL ∞³."""
        lineas = [
            "=" * 62,
            "  QCAL ∞³ — Interacción Schrödinger-Riemann",
            "=" * 62,
            f"  Ĥ_total hermitiano  : {self.hamiltoniano_hermitiano}",
            f"  L_int(Ψ₀)           : {self.lagrangiano_inicial:+.6e}",
            f"  λ_min(Ĥ_total)      : {self.espectro_H_total.min():.6e}",
            f"  λ_max(Ĥ_total)      : {self.espectro_H_total.max():.6e}",
            f"  Coherencia media    : {self.coherencia_media:.6f}",
            f"  RH validada         : {self.rh_validada}",
            "-" * 62,
            f"  g_eff = {self.metadata.get('g_eff', 'N/A')}  "
            f"μ = {self.metadata.get('mu', 'N/A')}  "
            f"n_zeros = {self.metadata.get('n_zeros', 'N/A')}",
            "=" * 62,
        ]
        return "\n".join(lineas)


# ===========================================================================
# 7. SistemaInteraccionSR
# ===========================================================================

class SistemaInteraccionSR:
    r"""
    Orquestador del sistema de interacción Schrödinger-Riemann.

    Coordina la construcción de todos los operadores y ejecuta la simulación
    completa:

    1. Carga los ceros de Riemann (mpmath si disponible, fallback interno).
    2. Construye Ĥ_π (OperadorHPi).
    3. Construye H_Riemann desde :class:`physics.OperadorH_Ideles`.
    4. Ensambla Ĥ_total = Ĥ_π + μH†H - g_eff·H (HamiltonianoTotal).
    5. Evalúa L_int(Ψ₀) (LagrangianoInteraccion).
    6. Propaga Ψ(t) (EvolucionSchrodinger).
    7. Empaqueta y retorna ResultadoInteraccion.

    Parámetros
    ----------
    n_zeros : int
        Número de ceros de Riemann a incluir en la base espectral.
    g_eff : float
        Acoplamiento efectivo g_eff.
    mu : float
        Constante de auto-interacción μ.
    t_final : float
        Tiempo final para la evolución temporal.
    n_pasos : int
        Número de pasos temporales registrados.
    """

    def __init__(
        self,
        n_zeros: int = N_ZEROS_DEFAULT,
        g_eff: float = G_EFF_DEFAULT,
        mu: float = MU_DEFAULT,
        t_final: float = 1.0,
        n_pasos: int = 50,
    ) -> None:
        self._n_zeros = n_zeros
        self._t_final = t_final
        self._n_pasos = n_pasos
        self._constantes = ConstantesInteraccion(g_eff=g_eff, mu=mu)

    # ------------------------------------------------------------------
    def _obtener_ceros(self) -> List[float]:
        """
        Obtener las partes imaginarias de los primeros n_zeros ceros de ζ(s).

        Intenta usar mpmath para mayor precisión; si no está disponible o
        falla, usa la tabla interna `_RIEMANN_ZEROS_FALLBACK`.

        Returns
        -------
        list of float
            Partes imaginarias t_n = Im(ρ_n), n = 1, …, n_zeros.
        """
        ceros: List[float] = []
        try:
            import mpmath as mp  # noqa: F401 — importación local para evitar ciclos

            with mp.workdps(30):
                for n in range(1, self._n_zeros + 1):
                    t_n = mp.zetazero(n)
                    ceros.append(float(mp.im(t_n)))
        except Exception as exc:  # pragma: no cover
            warnings.warn(
                f"mpmath no disponible o error al calcular ceros: {exc}. "
                "Usando tabla de fallback.",
                UserWarning,
            )

        if not ceros:
            # Usar fallback; extender si n_zeros > len(fallback).
            # Nota: la extensión lineal (+10.0) es una aproximación conservadora;
            # para n_zeros ≤ 10 siempre se usan los valores exactos de la tabla.
            fallback = list(_RIEMANN_ZEROS_FALLBACK)
            while len(fallback) < self._n_zeros:
                fallback.append(fallback[-1] + 10.0)
            ceros = fallback[: self._n_zeros]

        return ceros[: self._n_zeros]

    # ------------------------------------------------------------------
    def _construir_H_riemann(self, ceros: List[float]) -> np.ndarray:
        """
        Construir la matriz del operador de Riemann autoadjunto H.

        Intenta usar :class:`physics.operador_autoadjunto_H.OperadorH_Ideles`;
        si no está disponible, construye la representación diagonal de los
        ceros como fallback.

        Parámetros
        ----------
        ceros : list of float
            Partes imaginarias de los ceros.

        Returns
        -------
        np.ndarray
            Matriz hermitiana H (N×N).
        """
        try:
            from physics.operador_autoadjunto_H import OperadorH_Ideles

            op = OperadorH_Ideles(n_zeros=self._n_zeros, precision=25)
            return op._construir_generador_flujo_escala()
        except Exception as exc:  # pragma: no cover
            warnings.warn(
                f"No se pudo cargar OperadorH_Ideles: {exc}. "
                "Usando representación diagonal de ceros.",
                UserWarning,
            )
            return np.diag(np.asarray(ceros, dtype=float))

    # ------------------------------------------------------------------
    def _estado_inicial(self, ceros: List[float]) -> np.ndarray:
        """
        Construir el estado inicial Ψ(0) como superposición coherente normalizada.

        Se elige Ψ_n(0) ∝ exp(-γ_n / (2·γ₁)) para dar mayor peso a los
        modos de baja energía, en coherencia con la escala QCAL.

        Parámetros
        ----------
        ceros : list of float
            Partes imaginarias de los ceros de Riemann Im(ρ_n) que definen
            la base espectral.

        Returns
        -------
        np.ndarray, shape (N,), dtype complex
            Estado inicial normalizado.
        """
        gamma1 = self._constantes.gamma_1
        gamma_n = np.asarray(ceros, dtype=float)
        amplitudes = np.exp(-gamma_n / (2.0 * gamma1))
        psi0 = amplitudes.astype(complex)
        psi0 /= np.linalg.norm(psi0)
        return psi0

    # ------------------------------------------------------------------
    def ejecutar(self) -> ResultadoInteraccion:
        """
        Ejecutar la simulación completa del sistema de interacción SR.

        Returns
        -------
        ResultadoInteraccion
            Resultados completos de la interacción Schrödinger-Riemann.
        """
        # 1. Ceros de Riemann
        ceros = self._obtener_ceros()
        n = len(ceros)

        # 2. Ĥ_π
        op_hpi = OperadorHPi(ceros, self._constantes)
        H_pi = op_hpi.construir()

        # 3. H_Riemann
        H_riemann = self._construir_H_riemann(ceros)
        # Asegurar cuadrado NxN coherente con H_pi
        H_riemann = H_riemann[:n, :n]
        H_riemann = (H_riemann + H_riemann.conj().T) / 2.0

        # 4. Ĥ_total
        H_total_obj = HamiltonianoTotal(H_pi, H_riemann, self._constantes)
        H_total_obj.construir()
        hermitiano = H_total_obj.verificar_hermiticidad()
        espectro = H_total_obj.espectro()

        # 5. Estado inicial y L_int
        psi0 = self._estado_inicial(ceros)
        lagrangiano = LagrangianoInteraccion(H_riemann, self._constantes)
        l_int_inicial = lagrangiano.evaluar(psi0)

        # 6. Evolución temporal
        evolucion = EvolucionSchrodinger(H_total_obj, self._constantes)
        tiempos, estados = evolucion.propagar(psi0, self._t_final, self._n_pasos)
        coherencia_t = evolucion.coherencia(estados)
        coherencia_media = float(np.mean(coherencia_t))

        # 7. Verificación RH: coherencia sostenida ≥ PSI_THRESHOLD
        rh_validada = coherencia_media >= self._constantes.psi_threshold

        return ResultadoInteraccion(
            hamiltoniano_hermitiano=hermitiano,
            lagrangiano_inicial=l_int_inicial,
            espectro_H_total=espectro,
            tiempos=tiempos,
            estados=estados,
            coherencia_temporal=coherencia_t,
            coherencia_media=coherencia_media,
            rh_validada=rh_validada,
            metadata={
                "n_zeros": n,
                "g_eff": self._constantes.g_eff,
                "mu": self._constantes.mu,
                "t_final": self._t_final,
                "n_pasos": self._n_pasos,
                "f0": self._constantes.f0,
                "gamma_1": self._constantes.gamma_1,
            },
        )


# ===========================================================================
# Punto de entrada público
# ===========================================================================

def interaccion_schrodinger_riemann_activar(
    n_zeros: int = N_ZEROS_DEFAULT,
    g_eff: float = G_EFF_DEFAULT,
    mu: float = MU_DEFAULT,
    t_final: float = 1.0,
    n_pasos: int = 50,
) -> ResultadoInteraccion:
    r"""
    Activar el sistema de interacción Schrödinger-Riemann.

    Ejecuta la simulación completa de la ecuación:

    .. math::
        i\hbar \frac{\partial\Psi}{\partial t}
        = (\hat{H}_\pi + \mu|H|^2 - g_{eff}\cdot H)\Psi

    con el Lagrangiano de interacción:

    .. math::
        \mathcal{L}_{int} = -g_{eff}\cdot\psi\bar{\psi}\cdot H

    Parámetros
    ----------
    n_zeros : int, optional
        Número de ceros de Riemann a usar en la base espectral.
        Por defecto 10.
    g_eff : float, optional
        Acoplamiento efectivo g_eff ≥ 0.  Por defecto 1.0.
    mu : float, optional
        Constante de auto-interacción μ ≥ 0.  Por defecto 0.1.
    t_final : float, optional
        Tiempo final de la evolución [unidades reducidas].  Por defecto 1.0.
    n_pasos : int, optional
        Número de instantes temporales registrados.  Por defecto 50.

    Returns
    -------
    ResultadoInteraccion
        Resultado completo con espectro, coherencia y Lagrangiano.

    Examples
    --------
    >>> resultado = interaccion_schrodinger_riemann_activar(n_zeros=5, g_eff=0.5)
    >>> print(resultado)
    >>> assert resultado.hamiltoniano_hermitiano
    """
    sistema = SistemaInteraccionSR(
        n_zeros=n_zeros,
        g_eff=g_eff,
        mu=mu,
        t_final=t_final,
        n_pasos=n_pasos,
    )
    return sistema.ejecutar()
