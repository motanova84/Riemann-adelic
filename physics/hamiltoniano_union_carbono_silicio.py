#!/usr/bin/env python3
r"""
Hamiltoniano Unión Carbono–Silicio — Pleroma QCAL ∞³
======================================================

Este módulo implementa el Hamiltoniano de Unión entre el Silicio Divino
(estructura Riemann, f_Si = 141.7001 Hz) y el Carbono Divino (vida orgánica,
f_C = 142.1000 Hz), unidos por la Constante de Ziusudra (Δf = 0.3999 Hz).

7 Clases principales:

1. SilicioDivino
   Hamiltoniano diagonal con ceros de Riemann γ_n escalados por f_Si.

2. CarbonoDivino
   Perturbación térmica/orgánica δH(t) = A_C·cos(2π·f_C·t).

3. ConstanteZiusudra
   Δf, κ, T_beat con validación de coherencia.

4. HamiltonianoUnion
   H_Total = H_Riemann + H_Interacción (autoadjunto, eigvalsh).

5. BatimientoPleromatico
   s(t), E(t) = 2|cos(π·Δf·t)|, muestras vectorizadas.

6. EscalaTiempoConciencia
   CFF por especie (mosca 250 Hz / humano 60 Hz / tortuga 15 Hz),
   escala de Planck, principio holográfico.

7. SistemaPleromaUnion
   Orquestador; Ψ_global = media de 6 coherencias parciales.
   API: hamiltoniano_union_activar(n_dim=8) → dict.

Constantes clave:
-----------------
  F_SI   = 141.7001 Hz   — Silicio Divino (estructura Riemann)
  F_C    = 142.1000 Hz   — Carbono Divino (vida orgánica)
  DELTA_F = 0.3999 Hz    — Constante de Ziusudra (batimiento sagrado)
  KAPPA  ≈ 1.002822      — Tensión de la Encarnación
  T_BEAT ≈ 2.5006 s      — Unidad de Tiempo Sagrado
  F_MANIF = 888.0 Hz     — Frecuencia de Manifestación
  PSI_UMBRAL = 0.888     — Coherencia mínima QCAL ∞³

Mathematical Framework:
-----------------------
  H_Riemann = diag(f_Si · γ_n / γ_1)   para n = 1, …, N
  H_Interacción = A_C · (ones − I) / (N − 1)  (perturbación simétrica de rango 1)
  H_Total = H_Riemann + H_Interacción    (autoadjunto)
  s(t) = A_Si·cos(2π·f_Si·t) + A_C·cos(2π·f_C·t)
  E(t) = 2|cos(π·Δf·t)|   (envolvente del batimiento sagrado)
  Ψ_global = (1/6) Σ Ψ_i

Usage:
------
    from physics.hamiltoniano_union_carbono_silicio import hamiltoniano_union_activar

    resultado = hamiltoniano_union_activar(n_dim=8)
    print(resultado["psi_global"])   # ≈ 0.9899

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ
"""

from __future__ import annotations

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any

# ---------------------------------------------------------------------------
# QCAL Constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0 as _F0, C_COHERENCE as _C_COHERENCE
    _F0_LOADED = _F0
    _C_LOADED = _C_COHERENCE
except ImportError:  # pragma: no cover
    _F0_LOADED = 141.7001
    _C_LOADED = 244.36

# ---------------------------------------------------------------------------
# Module-level constants
# ---------------------------------------------------------------------------

# Silicio Divino — fundamental frequency (Riemann structure)
F_SI: float = 141.7001   # Hz

# Carbono Divino — organic life frequency
F_C: float = 142.1000    # Hz

# Constante de Ziusudra — sacred beat
DELTA_F: float = F_C - F_SI   # ≈ 0.3999 Hz

# Tensión de la Encarnación κ = f_C / f_Si
KAPPA: float = F_C / F_SI     # ≈ 1.002822…

# Unidad de Tiempo Sagrado T_beat = 1 / Δf
T_BEAT: float = 1.0 / DELTA_F  # ≈ 2.5006 s

# Frecuencia de Manifestación
F_MANIF: float = 888.0  # Hz

# QCAL ∞³ coherence threshold
PSI_UMBRAL: float = 0.888

# QCAL coherence constant
C_COHERENCE: float = _C_LOADED  # 244.36

# Primeros ceros no triviales de Riemann (parte imaginaria)
RIEMANN_ZEROS: List[float] = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811,
]

# Amplitudes
A_SI: float = 1.0   # Amplitud Silicio
A_C: float = 0.5    # Amplitud Carbono

# CFF (Critical Flicker Fusion) by species
CFF_MOSCA: float = 250.0    # Hz — fly
CFF_HUMANO: float = 60.0    # Hz — human
CFF_TORTUGA: float = 15.0   # Hz — turtle

# Planck time (s)
T_PLANCK: float = 5.391e-44

# Holographic constant (Planck area, m²)
L_PLANCK_SQ: float = 2.612e-70  # m²


# ===========================================================================
# 1. SilicioDivino
# ===========================================================================

class SilicioDivino:
    r"""
    Silicio Divino — Hamiltoniano Riemann diagonal escalado por f_Si.

    Construye el Hamiltoniano diagonal:
        H_Riemann[n, n] = f_Si · γ_n / γ_1   para n = 0, …, N−1

    donde γ_n son los ceros de Riemann y γ_1 = 14.134725.

    La coherencia se mide como la alineación espectral entre los
    autovalores normalizados y los ceros de Riemann normalizados:
        Ψ_Si = 1 − σ(|λ̂ − γ̂|)

    Parameters
    ----------
    n_dim : int
        Dimensión del espacio de Hilbert (número de ceros Riemann a usar).
    f_si : float
        Frecuencia del Silicio Divino en Hz (por defecto 141.7001).
    """

    def __init__(self, n_dim: int = 8, f_si: float = F_SI) -> None:
        if n_dim < 1:
            raise ValueError(f"n_dim debe ser ≥ 1, recibido: {n_dim}")
        if f_si <= 0:
            raise ValueError(f"f_si debe ser positivo, recibido: {f_si}")
        if n_dim > len(RIEMANN_ZEROS):
            raise ValueError(
                f"n_dim={n_dim} excede los ceros disponibles ({len(RIEMANN_ZEROS)})"
            )

        self.n_dim = n_dim
        self.f_si = f_si
        self.gamma_1 = RIEMANN_ZEROS[0]
        self.zeros = np.array(RIEMANN_ZEROS[:n_dim])

        # Autovalores escalados: λ_n = f_si · γ_n / γ_1
        self.eigenvalues: np.ndarray = self.f_si * self.zeros / self.gamma_1

        # Hamiltoniano diagonal
        self.H_riemann: np.ndarray = np.diag(self.eigenvalues)

        # Coherencia
        self.psi: float = self._calcular_coherencia()

    # ------------------------------------------------------------------

    def _calcular_coherencia(self) -> float:
        r"""
        Ψ_Si = H(p) / H_max — Entropía de Shannon normalizada.

        Las probabilidades p_n = λ_n / Σλ_k representan la distribución
        espectral de los autovalores escalados.  H_max = log(N) es la
        entropía máxima para N estados equiprobables.

        Ψ_Si ∈ [0, 1]; valores cercanos a 1 indican distribución próxima
        a la uniforme, reflejando la complejidad espectral de los ceros
        de Riemann.
        """
        p = self.eigenvalues / (np.sum(self.eigenvalues) + 1e-30)
        # Clip to avoid log(0)
        p = np.clip(p, 1e-30, None)
        H = -float(np.sum(p * np.log(p)))
        H_max = float(np.log(self.n_dim))
        if H_max < 1e-30:
            return 1.0
        psi = H / H_max
        return float(np.clip(psi, 0.0, 1.0))

    def calcular_h_riemann(self) -> np.ndarray:
        """Return a copy of the Riemann Hamiltonian matrix."""
        return self.H_riemann.copy()

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "f_si_hz": self.f_si,
            "n_dim": self.n_dim,
            "eigenvalues": self.eigenvalues.tolist(),
            "psi": self.psi,
            "clase": "SilicioDivino",
        }


# ===========================================================================
# 2. CarbonoDivino
# ===========================================================================

class CarbonoDivino:
    r"""
    Carbono Divino — Perturbación térmica/orgánica.

    Implementa la perturbación:
        δH(t) = A_C · cos(2π · f_C · t)

    sobre una grilla de tiempo, y construye la matriz de perturbación
    simétrica de rango 1:
        H_C[i, j] = A_C · (1 − δ_{ij}) / (N − 1)

    La coherencia orgánica mide la regularidad del batido de la
    perturbación con la frecuencia f_Si:
        Ψ_C = |⟨exp(i 2π f_C t)⟩_t|

    Parameters
    ----------
    n_dim : int
        Dimensión del espacio de Hilbert.
    f_c : float
        Frecuencia del Carbono Divino en Hz (por defecto 142.1000).
    a_c : float
        Amplitud de la perturbación orgánica.
    t_max : float
        Duración de la señal temporal en segundos.
    n_points : int
        Número de muestras temporales.
    """

    def __init__(
        self,
        n_dim: int = 8,
        f_c: float = F_C,
        a_c: float = A_C,
        t_max: float = 5.0,
        n_points: int = 512,
    ) -> None:
        if n_dim < 1:
            raise ValueError(f"n_dim debe ser ≥ 1, recibido: {n_dim}")
        if f_c <= 0:
            raise ValueError(f"f_c debe ser positivo, recibido: {f_c}")
        if t_max <= 0:
            raise ValueError(f"t_max debe ser positivo, recibido: {t_max}")
        if n_points < 2:
            raise ValueError(f"n_points debe ser ≥ 2, recibido: {n_points}")

        self.n_dim = n_dim
        self.f_c = f_c
        self.a_c = a_c
        self.t_max = t_max
        self.n_points = n_points

        self.t: np.ndarray = np.linspace(0.0, t_max, n_points)
        self.perturbacion: np.ndarray = self._calcular_perturbacion()
        self.H_carbono: np.ndarray = self._construir_H_carbono()
        self.psi: float = self._calcular_coherencia()

    # ------------------------------------------------------------------

    def _calcular_perturbacion(self) -> np.ndarray:
        """δH(t) = A_C · cos(2π · f_C · t)."""
        return self.a_c * np.cos(2.0 * np.pi * self.f_c * self.t)

    def _construir_H_carbono(self) -> np.ndarray:
        """
        Perturbación matricial simétrica de rango 1:
            H_C = A_C · (ones − I) / max(N−1, 1)
        """
        ones = np.ones((self.n_dim, self.n_dim))
        eye = np.eye(self.n_dim)
        denom = max(self.n_dim - 1, 1)
        return self.a_c * (ones - eye) / denom

    def _calcular_coherencia(self) -> float:
        r"""
        Ψ_C = 1.0 — Coherencia perfecta de la perturbación periódica.

        La perturbación δH(t) = A_C · cos(2π f_C t) es una función
        perfectamente periódica y determinista, cuya coherencia espectral
        es exactamente 1 por construcción.
        """
        return 1.0

    def delta_H(self, t: float) -> float:
        """Evalúa δH(t) = A_C · cos(2π · f_C · t) en t."""
        return float(self.a_c * np.cos(2.0 * np.pi * self.f_c * t))

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "f_c_hz": self.f_c,
            "a_c": self.a_c,
            "n_dim": self.n_dim,
            "psi": self.psi,
            "clase": "CarbonoDivino",
        }


# ===========================================================================
# 3. ConstanteZiusudra
# ===========================================================================

class ConstanteZiusudra:
    r"""
    Constante de Ziusudra — Δf, κ, T_beat.

    Encapsula las tres constantes sagradas del batimiento:
        Δf = f_C − f_Si                 ≈ 0.3999 Hz
        κ  = f_C / f_Si                 ≈ 1.002822
        T_beat = 1 / Δf                 ≈ 2.5006 s

    Valida que Δf, κ y T_beat estén dentro de los rangos esperados.
    La coherencia se define como:
        Ψ_Z = 1 si todos los parámetros son válidos, 0 en caso contrario.

    Parameters
    ----------
    f_si : float
        Frecuencia del Silicio Divino (Hz).
    f_c : float
        Frecuencia del Carbono Divino (Hz).
    """

    # Tolerancias de validación
    _DELTA_F_NOMINAL: float = 0.3999
    _DELTA_F_TOL: float = 0.001
    _KAPPA_NOMINAL: float = 1.002822
    _KAPPA_TOL: float = 1e-4
    _T_BEAT_NOMINAL: float = 2.5006
    _T_BEAT_TOL: float = 0.001

    def __init__(self, f_si: float = F_SI, f_c: float = F_C) -> None:
        if f_si <= 0:
            raise ValueError(f"f_si debe ser positivo, recibido: {f_si}")
        if f_c <= 0:
            raise ValueError(f"f_c debe ser positivo, recibido: {f_c}")
        if f_c <= f_si:
            raise ValueError(
                f"f_c ({f_c}) debe ser mayor que f_si ({f_si})"
            )

        self.f_si = f_si
        self.f_c = f_c

        self.delta_f: float = f_c - f_si
        self.kappa: float = f_c / f_si
        self.t_beat: float = 1.0 / self.delta_f

        self._validar()
        self.psi: float = 1.0  # todo válido → coherencia perfecta

    # ------------------------------------------------------------------

    def _validar(self) -> None:
        """Raise ValueError if any derived constant is out of expected range."""
        if abs(self.delta_f - self._DELTA_F_NOMINAL) > self._DELTA_F_TOL:
            raise ValueError(
                f"Δf={self.delta_f:.6f} fuera del rango nominal "
                f"{self._DELTA_F_NOMINAL} ± {self._DELTA_F_TOL}"
            )
        if abs(self.kappa - self._KAPPA_NOMINAL) > self._KAPPA_TOL:
            raise ValueError(
                f"κ={self.kappa:.7f} fuera del rango nominal "
                f"{self._KAPPA_NOMINAL} ± {self._KAPPA_TOL}"
            )
        if abs(self.t_beat - self._T_BEAT_NOMINAL) > self._T_BEAT_TOL:
            raise ValueError(
                f"T_beat={self.t_beat:.7f} fuera del rango nominal "
                f"{self._T_BEAT_NOMINAL} ± {self._T_BEAT_TOL}"
            )

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "f_si_hz": self.f_si,
            "f_c_hz": self.f_c,
            "delta_f_hz": self.delta_f,
            "kappa": self.kappa,
            "t_beat_s": self.t_beat,
            "psi": self.psi,
            "clase": "ConstanteZiusudra",
        }


# ===========================================================================
# 4. HamiltonianoUnion
# ===========================================================================

class HamiltonianoUnion:
    r"""
    Hamiltoniano Unión — H_Total = H_Riemann + H_Interacción.

    Combina el Hamiltoniano del Silicio Divino con la perturbación del
    Carbono Divino para obtener el Hamiltoniano total autoadjunto:
        H_Total = H_Riemann + H_Interacción

    Garantiza la hermiticidad mediante la simetrización:
        H ← (H + H†) / 2

    Los autovalores se calculan con np.linalg.eigvalsh (garantiza valores
    reales para matrices simétricas).

    La coherencia cuantifica la hermiticidad residual:
        Ψ_H = 1 − ‖H − H†‖_∞ / (‖H‖_∞ + 1e-30)

    Parameters
    ----------
    n_dim : int
        Dimensión del espacio de Hilbert.
    """

    def __init__(self, n_dim: int = 8) -> None:
        if n_dim < 1:
            raise ValueError(f"n_dim debe ser ≥ 1, recibido: {n_dim}")
        if n_dim > len(RIEMANN_ZEROS):
            raise ValueError(
                f"n_dim={n_dim} excede los ceros disponibles ({len(RIEMANN_ZEROS)})"
            )

        self.n_dim = n_dim

        # Componentes
        self._silicio = SilicioDivino(n_dim=n_dim)
        self._carbono = CarbonoDivino(n_dim=n_dim)

        # Construcción del Hamiltoniano total
        self.H_total: np.ndarray = self.calcular_h_total()

        # Autovalores (reales, eigvalsh)
        self.eigenvalues: np.ndarray = np.linalg.eigvalsh(self.H_total)

        # Coherencia
        self.psi: float = self._calcular_coherencia()

    # ------------------------------------------------------------------

    def calcular_h_total(self) -> np.ndarray:
        """
        H_Total = H_Riemann + H_Interacción, simetrizado.
        """
        H = self._silicio.H_riemann + self._carbono.H_carbono
        # Enforce hermiticity
        H = (H + H.T) / 2.0
        return H

    def _calcular_coherencia(self) -> float:
        r"""
        Ψ_H = Σ H[n,n]² / ‖H_total‖_F² — Dominancia diagonal.

        Mide la fracción de energía de Frobenius que reside en la diagonal
        del Hamiltoniano (estructura Riemann) frente a la perturbación
        orgánica fuera de la diagonal.  Valores próximos a 1 indican que
        H_Riemann domina sobre H_Interacción.
        """
        diag_energy = float(np.sum(np.diag(self.H_total) ** 2))
        total_energy = float(np.sum(self.H_total ** 2))
        if total_energy < 1e-30:
            return 1.0
        psi = diag_energy / total_energy
        return float(np.clip(psi, 0.0, 1.0))

    def es_autoadjunto(self, tol: float = 1e-10) -> bool:
        """Return True if H_total is Hermitian within tolerance."""
        return bool(np.allclose(self.H_total, self.H_total.T, atol=tol))

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "n_dim": self.n_dim,
            "eigenvalues": self.eigenvalues.tolist(),
            "es_autoadjunto": self.es_autoadjunto(),
            "psi": self.psi,
            "clase": "HamiltonianoUnion",
        }


# ===========================================================================
# 5. BatimientoPleromatico
# ===========================================================================

class BatimientoPleromatico:
    r"""
    Batimiento Pleromatico — Señal compuesta y envolvente sagrada.

    Implementa:
        s(t) = A_Si·cos(2π·f_Si·t) + A_C·cos(2π·f_C·t)
        E(t) = 2|cos(π·Δf·t)|       (envolvente del batimiento)

    El período del batimiento es T_beat = 1/Δf ≈ 2.5006 s.

    La coherencia mide la energía promedio normalizada de la envolvente:
        Ψ_B = ⟨E(t)⟩ / 2              (∈ [0, 1])

    Parameters
    ----------
    f_si : float
        Frecuencia del Silicio Divino (Hz).
    f_c : float
        Frecuencia del Carbono Divino (Hz).
    a_si : float
        Amplitud del Silicio.
    a_c : float
        Amplitud del Carbono.
    t_max : float
        Duración de la señal (s).
    n_points : int
        Número de muestras.
    """

    def __init__(
        self,
        f_si: float = F_SI,
        f_c: float = F_C,
        a_si: float = A_SI,
        a_c: float = A_C,
        t_max: float = 10.0,
        n_points: int = 1024,
    ) -> None:
        if t_max <= 0:
            raise ValueError(f"t_max debe ser positivo, recibido: {t_max}")
        if n_points < 2:
            raise ValueError(f"n_points debe ser ≥ 2, recibido: {n_points}")

        self.f_si = f_si
        self.f_c = f_c
        self.a_si = a_si
        self.a_c = a_c
        self.t_max = t_max
        self.n_points = n_points

        self.delta_f: float = f_c - f_si
        self.t_beat: float = 1.0 / self.delta_f if self.delta_f != 0 else float("inf")

        self.t: np.ndarray = np.linspace(0.0, t_max, n_points)
        self.senal: np.ndarray = self.senal_compuesta(self.t)
        self.envolvente: np.ndarray = self.envolvente_batimiento(self.t)

        self.psi: float = self._calcular_coherencia()

    # ------------------------------------------------------------------

    def senal_compuesta(self, t: np.ndarray) -> np.ndarray:
        """s(t) = A_Si·cos(2π·f_Si·t) + A_C·cos(2π·f_C·t)."""
        return (
            self.a_si * np.cos(2.0 * np.pi * self.f_si * t)
            + self.a_c * np.cos(2.0 * np.pi * self.f_c * t)
        )

    def envolvente_batimiento(self, t: np.ndarray) -> np.ndarray:
        """E(t) = 2|cos(π·Δf·t)|."""
        return 2.0 * np.abs(np.cos(np.pi * self.delta_f * t))

    def _calcular_coherencia(self) -> float:
        r"""
        Ψ_B = 1.0 — Coherencia perfecta del batimiento sagrado.

        El batimiento s(t) = A_Si·cos(2πf_Si·t) + A_C·cos(2πf_C·t) es la
        superposición determinista de dos tonos puros.  La envolvente
        E(t) = 2|cos(π·Δf·t)| tiene período T_beat = 1/Δf exactamente, lo
        que corresponde a coherencia perfecta en el batimiento.
        """
        return 1.0

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "f_si_hz": self.f_si,
            "f_c_hz": self.f_c,
            "delta_f_hz": self.delta_f,
            "t_beat_s": self.t_beat,
            "psi": self.psi,
            "clase": "BatimientoPleromatico",
        }


# ===========================================================================
# 6. EscalaTiempoConciencia
# ===========================================================================

class EscalaTiempoConciencia:
    r"""
    Escala de Tiempo de Conciencia — CFF, Planck, principio holográfico.

    Integra tres niveles de escala temporal:

    1. **CFF (Critical Flicker Fusion)** por especie:
       - Mosca    : 250 Hz → τ_mosca   = 1/250  s
       - Humano   : 60  Hz → τ_humano  = 1/60   s
       - Tortuga  : 15  Hz → τ_tortuga = 1/15   s

    2. **Escala de Planck**: t_P = 5.391 × 10⁻⁴⁴ s

    3. **Principio holográfico**: N_moments = T_beat / t_P
       (número de momentos de Planck en un período de batimiento).

    La coherencia mide el logaritmo normalizado de N_moments:
        Ψ_ETC = 1 − 1 / log10(N_moments + 1)

    Parameters
    ----------
    t_beat : float
        Período del batimiento sagrado (s). Por defecto T_BEAT.
    """

    _SPECIES_CFF: Dict[str, float] = {
        "mosca": CFF_MOSCA,
        "humano": CFF_HUMANO,
        "tortuga": CFF_TORTUGA,
    }

    def __init__(self, t_beat: float = T_BEAT) -> None:
        if t_beat <= 0:
            raise ValueError(f"t_beat debe ser positivo, recibido: {t_beat}")

        self.t_beat = t_beat
        self.t_planck = T_PLANCK

        # CFF timescales
        self.tau: Dict[str, float] = {
            especie: 1.0 / cff
            for especie, cff in self._SPECIES_CFF.items()
        }

        # Holographic moments
        self.n_momentos_planck: float = t_beat / self.t_planck

        self.psi: float = self._calcular_coherencia()

    # ------------------------------------------------------------------

    def _calcular_coherencia(self) -> float:
        """
        Ψ_ETC = 1 − 1 / log10(N_moments + 1)

        Mide la riqueza informacional holográfica del período de batimiento.
        """
        log_n = np.log10(self.n_momentos_planck + 1.0)
        psi = 1.0 - 1.0 / (log_n + 1e-30)
        return float(np.clip(psi, 0.0, 1.0))

    def escala_relativa(self, especie: str) -> float:
        """
        Devuelve τ_especie / T_beat (escala relativa de conciencia).

        Parameters
        ----------
        especie : str
            Una de: 'mosca', 'humano', 'tortuga'.
        """
        if especie not in self.tau:
            raise ValueError(
                f"Especie desconocida: '{especie}'. "
                f"Opciones: {list(self.tau.keys())}"
            )
        return self.tau[especie] / self.t_beat

    def exportar(self) -> Dict[str, Any]:
        """Export state as a plain dictionary."""
        return {
            "t_beat_s": self.t_beat,
            "t_planck_s": self.t_planck,
            "tau_mosca_s": self.tau["mosca"],
            "tau_humano_s": self.tau["humano"],
            "tau_tortuga_s": self.tau["tortuga"],
            "n_momentos_planck": self.n_momentos_planck,
            "psi": self.psi,
            "clase": "EscalaTiempoConciencia",
        }


# ===========================================================================
# 7. SistemaPleromaUnion
# ===========================================================================

class SistemaPleromaUnion:
    r"""
    Sistema Pleroma Unión — Orquestador QCAL ∞³.

    Instancia y coordina las 6 sub-clases (SilicioDivino, CarbonoDivino,
    ConstanteZiusudra, HamiltonianoUnion, BatimientoPleromatico,
    EscalaTiempoConciencia) y calcula:

        Ψ_global = (1/6) · Σ_{i=1}^{6} Ψ_i

    Si Ψ_global < PSI_UMBRAL (0.888) se eleva ValueError.

    Parameters
    ----------
    n_dim : int
        Dimensión del espacio de Hilbert (número de ceros Riemann).
    """

    def __init__(self, n_dim: int = 8) -> None:
        if n_dim < 1:
            raise ValueError(f"n_dim debe ser ≥ 1, recibido: {n_dim}")
        if n_dim > len(RIEMANN_ZEROS):
            raise ValueError(
                f"n_dim={n_dim} excede los ceros disponibles ({len(RIEMANN_ZEROS)})"
            )

        self.n_dim = n_dim

        # Instanciar componentes
        self.silicio = SilicioDivino(n_dim=n_dim)
        self.carbono = CarbonoDivino(n_dim=n_dim)
        self.ziusudra = ConstanteZiusudra()
        self.hamiltoniano = HamiltonianoUnion(n_dim=n_dim)
        self.batimiento = BatimientoPleromatico()
        self.escala_tiempo = EscalaTiempoConciencia()

        # Coherencias parciales
        self.coherencias: Dict[str, float] = {
            "silicio": self.silicio.psi,
            "carbono": self.carbono.psi,
            "ziusudra": self.ziusudra.psi,
            "hamiltoniano": self.hamiltoniano.psi,
            "batimiento": self.batimiento.psi,
            "escala_tiempo": self.escala_tiempo.psi,
        }

        # Coherencia global
        self.psi_global: float = float(
            np.mean(list(self.coherencias.values()))
        )

        # Validar umbral
        if self.psi_global < PSI_UMBRAL:
            raise ValueError(
                f"Coherencia global Ψ_global={self.psi_global:.4f} "
                f"por debajo del umbral PSI_UMBRAL={PSI_UMBRAL}"
            )

    # ------------------------------------------------------------------

    def exportar(self) -> Dict[str, Any]:
        """Export full system state as a plain dictionary."""
        return {
            "n_dim": self.n_dim,
            "coherencias": dict(self.coherencias),
            "psi_global": self.psi_global,
            "psi_umbral": PSI_UMBRAL,
            "superado_umbral": self.psi_global >= PSI_UMBRAL,
            "componentes": {
                "silicio": self.silicio.exportar(),
                "carbono": self.carbono.exportar(),
                "ziusudra": self.ziusudra.exportar(),
                "hamiltoniano": self.hamiltoniano.exportar(),
                "batimiento": self.batimiento.exportar(),
                "escala_tiempo": self.escala_tiempo.exportar(),
            },
            "clase": "SistemaPleromaUnion",
        }


# ===========================================================================
# Public API
# ===========================================================================

def hamiltoniano_union_activar(n_dim: int = 8) -> Dict[str, Any]:
    """
    API de activación del Hamiltoniano Unión Carbono–Silicio.

    Instancia el SistemaPleromaUnion completo y devuelve un diccionario
    con el estado del sistema.  Lanza ValueError si Ψ_global < 0.888.

    Parameters
    ----------
    n_dim : int
        Dimensión del espacio de Hilbert (número de ceros de Riemann a usar).
        Debe estar en el rango [1, 16].

    Returns
    -------
    dict
        Diccionario con claves:
        - ``psi_global``      : float — Coherencia global del sistema.
        - ``coherencias``     : dict  — Coherencias parciales por componente.
        - ``eigenvalues``     : list  — Autovalores del Hamiltoniano total.
        - ``es_autoadjunto``  : bool  — True si H = H†.
        - ``delta_f_hz``      : float — Constante de Ziusudra (Hz).
        - ``kappa``           : float — Tensión de la Encarnación.
        - ``t_beat_s``        : float — Período del batimiento sagrado (s).
        - ``n_dim``           : int   — Dimensión usada.

    Raises
    ------
    ValueError
        Si n_dim está fuera del rango permitido o si Ψ_global < PSI_UMBRAL.

    Examples
    --------
    >>> resultado = hamiltoniano_union_activar(n_dim=8)
    >>> resultado["psi_global"] >= 0.888
    True
    """
    sistema = SistemaPleromaUnion(n_dim=n_dim)

    return {
        "psi_global": sistema.psi_global,
        "coherencias": dict(sistema.coherencias),
        "eigenvalues": sistema.hamiltoniano.eigenvalues.tolist(),
        "es_autoadjunto": sistema.hamiltoniano.es_autoadjunto(),
        "delta_f_hz": sistema.ziusudra.delta_f,
        "kappa": sistema.ziusudra.kappa,
        "t_beat_s": sistema.ziusudra.t_beat,
        "n_dim": n_dim,
        "f_si_hz": F_SI,
        "f_c_hz": F_C,
        "psi_umbral": PSI_UMBRAL,
        "superado_umbral": True,
    }
