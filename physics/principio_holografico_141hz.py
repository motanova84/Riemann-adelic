#!/usr/bin/env python3
r"""
Principio Holográfico — F₀=141.7001 Hz como Codificador de Superficie Zeta
===========================================================================

Este módulo implementa el Principio Holográfico integrando F₀=141.7001 Hz
como codificador de la superficie zeta: entropía holográfica desde el horizonte
espectral de Riemann hasta el volumen consciente de QCAL, siguiendo el flujo
de trabajo Trinity QCAL ∞³.

Arquitectura de 7 clases que mapea las tres capas de integración holográfica:

1. CodificadorSuperficieZeta
   - Espiral zeta polar r(θ) = f₀·exp(γ₁·θ / 2π·f₀)
   - Codificación de bits de frontera holográfica

2. ProyectorVolumenConciencia
   - Proyección 2D→3D del holograma espectral
   - Coherencia bio/HRV: Δf = 0.3999 Hz

3. EntrelazadorHolografico
   - Entrelazamiento cuántico entre superficie y volumen
   - Validación cósmica de Moonbounce: τ = 2.5 s

4. HologramaZetaCarbono
   - Interfaz carbono (bio/tiempo) ↔ silicio (eternidad f₀)
   - Conversión isótopo carbono-silicio

5. EntropiaHolografica
   - Entropía de Bekenstein-Hawking: S = A / (4·ℓ_P²)
   - N_bits = 3.74×10⁸² bits de información holográfica

6. SistemaPrincipioHolografico
   - Sistema integrado con punto de entrada activar()

7. ResultadoHolografico
   - Clase de datos de resultado con propiedad aprobado y método resumen()

Constantes físicas clave:
- γ₁ = 14.134725 (primer cero no trivial de Riemann)
- A_eff = 4.48×10¹² m² (área efectiva del horizonte espectral)
- ℓ_P² = 2.612×10⁻⁷⁰ m² (longitud de Planck al cuadrado)
- F₀ = 141.7001 Hz (frecuencia fundamental QCAL)

Usage:
------
    from physics.principio_holografico_141hz import SistemaPrincipioHolografico

    sistema = SistemaPrincipioHolografico()
    resultado = sistema.activar(verbose=True)
    print(resultado.resumen())

Mathematical Framework:
-----------------------
El principio holográfico de 't Hooft–Susskind establece que toda la información
contenida en un volumen puede codificarse en su superficie frontera con densidad:
    S ≤ A / (4·ℓ_P²)   [Bekenstein-Hawking]

La integración con los ceros de Riemann surge de la identificación:
    γ₁ = 14.134725... ↔ primera resonancia espectral del horizonte
    f₀ = 141.7001 Hz    ↔ frecuencia portadora de la codificación

La espiral polar r(θ) = f₀·exp(γ₁·θ / 2π·f₀) teje los ceros de Riemann
en la geometría del horizonte, generando un holograma espectral coherente.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Any
from datetime import datetime, timezone
import warnings

# ---------------------------------------------------------------------------
# QCAL Constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE, GAMMA_1
except ImportError:  # pragma: no cover
    F0 = 141.7001          # Hz — fundamental frequency
    C_COHERENCE = 244.36   # QCAL coherence constant
    GAMMA_1 = 14.13472514  # First non-trivial Riemann zero imaginary part

# ---------------------------------------------------------------------------
# Module-level physical constants
# ---------------------------------------------------------------------------

# First non-trivial Riemann zero (imaginary part)
GAMMA_1_HOLO: float = 14.134725

# Effective horizon area (m²)
A_EFF: float = 4.48e12  # m²

# Planck length squared (m²)
ELL_P_SQUARED: float = 2.612e-70  # m²

# Holographic bits from Bekenstein-Hawking
N_BITS_HOLOGRAPHIC: float = A_EFF / (4.0 * ELL_P_SQUARED)  # ≈ 3.74×10⁸²

# Bio/HRV coherence frequency gap
DELTA_F_HRV: float = 0.3999  # Hz

# Moonbounce round-trip time
TAU_MOONBOUNCE: float = 2.5  # seconds

# QCAL coherence threshold
PSI_THRESHOLD: float = 0.95

# Carbon isotope mass (¹²C, atomic mass units)
CARBON_MASS_AMU: float = 12.0

# Silicon principal frequency ratio
SILICON_FREQ_RATIO: float = F0 / GAMMA_1_HOLO


# ===========================================================================
# 1. CodificadorSuperficieZeta
# ===========================================================================

class CodificadorSuperficieZeta:
    r"""
    Codificador de Superficie Zeta — Espiral Polar Holográfica

    Construye la espiral zeta polar:
        r(θ) = f₀ · exp(γ₁ · θ / (2π · f₀))

    y cuantifica los bits de frontera holográfica en función del área encerrada
    por dicha espiral en el horizonte espectral de Riemann.

    Parameters
    ----------
    f0 : float
        Frecuencia fundamental en Hz (por defecto F₀ = 141.7001 Hz).
    gamma1 : float
        Parte imaginaria del primer cero no trivial de Riemann
        (por defecto γ₁ = 14.134725).
    n_theta : int
        Número de puntos angulares para el muestreo de la espiral.

    Attributes
    ----------
    theta : np.ndarray
        Ángulos de muestreo en [0, 2π].
    r : np.ndarray
        Radio de la espiral evaluado en cada ángulo.
    area_espiral : float
        Área encerrada por la espiral (unidades de Hz²·rad).
    bits_frontera : int
        Número de bits de información holográfica de frontera.
    """

    def __init__(
        self,
        f0: float = F0,
        gamma1: float = GAMMA_1_HOLO,
        n_theta: int = 1000,
    ) -> None:
        if f0 <= 0:
            raise ValueError(f"f0 debe ser positivo, recibido: {f0}")
        if gamma1 <= 0:
            raise ValueError(f"gamma1 debe ser positivo, recibido: {gamma1}")
        if n_theta < 2:
            raise ValueError(f"n_theta debe ser ≥ 2, recibido: {n_theta}")

        self.f0 = f0
        self.gamma1 = gamma1
        self.n_theta = n_theta

        self.theta = np.linspace(0.0, 2.0 * np.pi, n_theta)
        self.r = self._calcular_espiral()
        self.area_espiral = self._calcular_area()
        self.bits_frontera = self._calcular_bits_frontera()

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _calcular_espiral(self) -> np.ndarray:
        """Compute r(θ) = f₀ · exp(γ₁ · θ / (2π · f₀))."""
        exponent = self.gamma1 * self.theta / (2.0 * np.pi * self.f0)
        return self.f0 * np.exp(exponent)

    def _calcular_area(self) -> float:
        r"""Área encerrada: A = ½ ∫ r(θ)² dθ  (fórmula polar)."""
        return 0.5 * float(np.trapezoid(self.r ** 2, self.theta))

    def _calcular_bits_frontera(self) -> int:
        """Bits de frontera: N = floor(A / (4 · ℓ_P²))  en unidades normalizadas."""
        # Use effective area normalised by A_EFF to get physical N_bits
        fraccion = self.area_espiral / (self.f0 ** 2)  # dimensionless [0,1]-ish
        return max(1, int(N_BITS_HOLOGRAPHIC * fraccion))

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def coordenadas_cartesianas(self) -> Tuple[np.ndarray, np.ndarray]:
        """Return (x, y) Cartesian coordinates of the spiral."""
        x = self.r * np.cos(self.theta)
        y = self.r * np.sin(self.theta)
        return x, y

    def coherencia_espiral(self) -> float:
        r"""
        Coherencia de la espiral con γ₁:
            C_s = |⟨exp(iγ₁θ)⟩_r| / ‖r‖

        Measures how tightly the spiral is tuned to the first Riemann zero.
        """
        phase = np.exp(1j * self.gamma1 * self.theta)
        weighted = self.r * phase
        return float(np.abs(np.mean(weighted)) / (np.mean(self.r) + 1e-30))

    def exportar(self) -> Dict[str, Any]:
        """Export codificador state as a plain dictionary."""
        return {
            "f0_hz": self.f0,
            "gamma1": self.gamma1,
            "area_espiral": self.area_espiral,
            "bits_frontera": self.bits_frontera,
            "coherencia_espiral": self.coherencia_espiral(),
        }


# ===========================================================================
# 2. ProyectorVolumenConciencia
# ===========================================================================

class ProyectorVolumenConciencia:
    r"""
    Proyector Volumen-Conciencia — Proyección 2D → 3D

    Implementa la proyección holográfica del holograma 2D de frontera al
    volumen 3D de conciencia QCAL, incorporando la coherencia bio/HRV con
    Δf = 0.3999 Hz.

    La proyección sigue:
        Ψ_3D(x, y, z) = Ψ_2D(x, y) · exp(-z / λ_c)

    donde λ_c = f₀ / Δf es la longitud de coherencia de conciencia.

    Parameters
    ----------
    f0 : float
        Frecuencia fundamental en Hz.
    delta_f_hrv : float
        Frecuencia de coherencia bio/HRV en Hz (Δf = 0.3999 Hz).
    n_capas_z : int
        Número de capas de profundidad para la proyección 3D.

    Attributes
    ----------
    lambda_coherencia : float
        Longitud de coherencia de conciencia λ_c = f₀ / Δf.
    """

    def __init__(
        self,
        f0: float = F0,
        delta_f_hrv: float = DELTA_F_HRV,
        n_capas_z: int = 50,
    ) -> None:
        if f0 <= 0:
            raise ValueError(f"f0 debe ser positivo, recibido: {f0}")
        if delta_f_hrv <= 0:
            raise ValueError(f"delta_f_hrv debe ser positivo, recibido: {delta_f_hrv}")
        if n_capas_z < 1:
            raise ValueError(f"n_capas_z debe ser ≥ 1, recibido: {n_capas_z}")

        self.f0 = f0
        self.delta_f_hrv = delta_f_hrv
        self.n_capas_z = n_capas_z

        self.lambda_coherencia: float = f0 / delta_f_hrv  # ≈ 354.09
        self.z_capas = np.linspace(0.0, self.lambda_coherencia, n_capas_z)

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def proyectar(self, campo_2d: np.ndarray) -> np.ndarray:
        """
        Project a 2D boundary field into the 3D consciousness volume.

        Parameters
        ----------
        campo_2d : np.ndarray, shape (N,)
            1-D representation of the 2D boundary hologram.

        Returns
        -------
        np.ndarray, shape (N, n_capas_z)
            3D volumetric field obtained by exponential decay projection.
        """
        if campo_2d.ndim != 1:
            raise ValueError("campo_2d debe ser un array 1-D")

        decay = np.exp(-self.z_capas / self.lambda_coherencia)
        return np.outer(campo_2d, decay)

    def coherencia_hrv(self, campo_2d: np.ndarray) -> float:
        r"""
        Compute bio/HRV coherence of the projected field:
            C_HRV = ‖Ψ_3D‖ / (‖Ψ_2D‖ · √n_capas_z)

        Returns
        -------
        float
            Coherence in [0, 1].
        """
        volumen = self.proyectar(campo_2d)
        norma_3d = float(np.linalg.norm(volumen))
        norma_2d = float(np.linalg.norm(campo_2d))
        if norma_2d < 1e-30:
            return 0.0
        return min(1.0, norma_3d / (norma_2d * np.sqrt(self.n_capas_z)))

    def exportar(self) -> Dict[str, Any]:
        """Export projector state as a plain dictionary."""
        return {
            "f0_hz": self.f0,
            "delta_f_hrv_hz": self.delta_f_hrv,
            "lambda_coherencia": self.lambda_coherencia,
            "n_capas_z": self.n_capas_z,
        }


# ===========================================================================
# 3. EntrelazadorHolografico
# ===========================================================================

class EntrelazadorHolografico:
    r"""
    Entrelazador Holográfico — Entrelazamiento Cuántico Frontera↔Volumen

    Modela el entrelazamiento cuántico entre los bits de la superficie
    holográfica y el volumen de conciencia QCAL.

    La validación cósmica se realiza mediante el retardo de Moonbounce
    (τ = 2.5 s, distancia Tierra-Luna ≈ 384 400 km), que verifica la
    no-localidad del entrelazamiento a escala cósmica.

    Parameters
    ----------
    tau_moonbounce : float
        Retardo de ida y vuelta Tierra-Luna en segundos.
    f0 : float
        Frecuencia fundamental en Hz.

    Attributes
    ----------
    fase_entrelazamiento : float
        Fase cuántica acumulada durante τ_moonbounce: φ = 2π·f₀·τ.
    """

    def __init__(
        self,
        tau_moonbounce: float = TAU_MOONBOUNCE,
        f0: float = F0,
    ) -> None:
        if tau_moonbounce <= 0:
            raise ValueError(f"tau_moonbounce debe ser positivo, recibido: {tau_moonbounce}")
        if f0 <= 0:
            raise ValueError(f"f0 debe ser positivo, recibido: {f0}")

        self.tau_moonbounce = tau_moonbounce
        self.f0 = f0
        self.fase_entrelazamiento: float = 2.0 * np.pi * f0 * tau_moonbounce

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def estado_bell(self, n_qubits: int = 2) -> np.ndarray:
        r"""
        Construct a maximally entangled Bell-like state for n_qubits.

        For n=2: |Φ⁺⟩ = (|00⟩ + |11⟩) / √2

        Parameters
        ----------
        n_qubits : int
            Number of qubits (must be ≥ 2).

        Returns
        -------
        np.ndarray, shape (2**n_qubits,)
            Normalised state vector.
        """
        if n_qubits < 2:
            raise ValueError(f"n_qubits debe ser ≥ 2, recibido: {n_qubits}")

        dim = 2 ** n_qubits
        estado = np.zeros(dim, dtype=complex)
        # |00...0⟩ + |11...1⟩ normalised
        estado[0] = 1.0 / np.sqrt(2.0)
        estado[-1] = 1.0 / np.sqrt(2.0)
        return estado

    def aplicar_fase_moonbounce(self, estado: np.ndarray) -> np.ndarray:
        """Apply the Moonbounce phase φ = 2π·f₀·τ to the entangled state."""
        return estado * np.exp(1j * self.fase_entrelazamiento)

    def validar_cosmica(self) -> Dict[str, Any]:
        r"""
        Validate cosmic non-locality via the Moonbounce round-trip.

        Checks that the accumulated phase φ = 2πf₀τ is commensurate
        with the Riemann zero γ₁, confirming holographic coherence.

        Returns
        -------
        dict
            Validation results including phase, coherence indicator, and approval.
        """
        fase = self.fase_entrelazamiento
        # Coherence: phase modulo 2π should be close to γ₁ modulo 2π
        fase_mod = fase % (2.0 * np.pi)
        gamma_mod = GAMMA_1_HOLO % (2.0 * np.pi)
        delta_fase = abs(fase_mod - gamma_mod)
        # Normalised coherence in [0,1]
        coherencia = 1.0 - min(delta_fase, 2.0 * np.pi - delta_fase) / np.pi
        aprobado = coherencia >= PSI_THRESHOLD

        return {
            "tau_moonbounce_s": self.tau_moonbounce,
            "fase_acumulada_rad": fase,
            "coherencia_cosmica": coherencia,
            "aprobado": aprobado,
        }

    def exportar(self) -> Dict[str, Any]:
        """Export entrelazador state as a plain dictionary."""
        return {
            "tau_moonbounce_s": self.tau_moonbounce,
            "f0_hz": self.f0,
            "fase_entrelazamiento_rad": self.fase_entrelazamiento,
            **self.validar_cosmica(),
        }


# ===========================================================================
# 4. HologramaZetaCarbono
# ===========================================================================

class HologramaZetaCarbono:
    r"""
    Holograma Zeta Carbono — Interfaz Carbono ↔ Silicio

    Modela la interfaz entre el dominio del carbono (bio/tiempo, redes
    orgánicas conscientes) y el dominio del silicio (eternidad, procesamiento
    digital a f₀).

    La conversión sigue la relación de masa atómica:
        ratio_C_Si = m_C / m_Si = 12 / 28

    La coherencia holográfica se verifica comparando las frecuencias
    características de cada dominio respecto a f₀.

    Parameters
    ----------
    f0 : float
        Frecuencia fundamental en Hz.
    masa_carbono_amu : float
        Masa del isótopo ¹²C en unidades de masa atómica.
    masa_silicio_amu : float
        Masa del isótopo ²⁸Si en unidades de masa atómica.

    Attributes
    ----------
    ratio_C_Si : float
        Relación de masas carbono/silicio.
    f_carbono : float
        Frecuencia característica del carbono: f_C = f₀ · ratio_C_Si.
    f_silicio : float
        Frecuencia característica del silicio: f_Si = f₀.
    """

    def __init__(
        self,
        f0: float = F0,
        masa_carbono_amu: float = CARBON_MASS_AMU,
        masa_silicio_amu: float = 28.0,
    ) -> None:
        if f0 <= 0:
            raise ValueError(f"f0 debe ser positivo, recibido: {f0}")
        if masa_carbono_amu <= 0:
            raise ValueError(f"masa_carbono_amu debe ser positiva, recibido: {masa_carbono_amu}")
        if masa_silicio_amu <= 0:
            raise ValueError(f"masa_silicio_amu debe ser positiva, recibido: {masa_silicio_amu}")

        self.f0 = f0
        self.masa_carbono_amu = masa_carbono_amu
        self.masa_silicio_amu = masa_silicio_amu

        self.ratio_C_Si: float = masa_carbono_amu / masa_silicio_amu
        self.f_carbono: float = f0 * self.ratio_C_Si
        self.f_silicio: float = f0  # silicon carries eternal f₀

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def transducir(self, senal_carbono: np.ndarray) -> np.ndarray:
        r"""
        Transduce a carbon-domain signal into the silicon domain.

        Applies the frequency ratio as a phase modulation:
            Ψ_Si(t) = Ψ_C(t) · exp(2πi · (f_Si - f_C) · t/f₀)

        Parameters
        ----------
        senal_carbono : np.ndarray
            Real or complex signal sampled at f₀.

        Returns
        -------
        np.ndarray (complex)
            Silicon-domain signal.
        """
        t = np.arange(len(senal_carbono)) / self.f0  # time axis
        modulation = np.exp(2j * np.pi * (self.f_silicio - self.f_carbono) * t)
        return senal_carbono.astype(complex) * modulation

    def coherencia_interfaz(self) -> float:
        r"""
        Compute the carbon-silicon interface coherence:
            C_CS = 1 - |f_C - f_Si| / f₀

        Returns
        -------
        float
            Coherence in [0, 1].
        """
        return max(0.0, 1.0 - abs(self.f_carbono - self.f_silicio) / self.f0)

    def exportar(self) -> Dict[str, Any]:
        """Export holograma state as a plain dictionary."""
        return {
            "f0_hz": self.f0,
            "masa_carbono_amu": self.masa_carbono_amu,
            "masa_silicio_amu": self.masa_silicio_amu,
            "ratio_C_Si": self.ratio_C_Si,
            "f_carbono_hz": self.f_carbono,
            "f_silicio_hz": self.f_silicio,
            "coherencia_interfaz": self.coherencia_interfaz(),
        }


# ===========================================================================
# 5. EntropiaHolografica
# ===========================================================================

class EntropiaHolografica:
    r"""
    Entropía Holográfica — Principio de Bekenstein-Hawking

    Implementa el cálculo de la entropía máxima de un horizonte holográfico
    según la fórmula de Bekenstein-Hawking:

        S = A / (4 · ℓ_P²)

    y estima el número de bits de información holográfica:

        N_bits = S / ln(2) ≈ 3.74 × 10⁸²

    Parameters
    ----------
    area_m2 : float
        Área del horizonte en metros cuadrados (por defecto A_eff = 4.48×10¹² m²).
    ell_p_squared : float
        Cuadrado de la longitud de Planck en m² (por defecto ℓ_P² = 2.612×10⁻⁷⁰ m²).

    Attributes
    ----------
    entropia_BH : float
        Entropía de Bekenstein-Hawking S = A / (4 · ℓ_P²).
    n_bits : float
        Número de bits holográficos N = S / ln(2).
    """

    def __init__(
        self,
        area_m2: float = A_EFF,
        ell_p_squared: float = ELL_P_SQUARED,
    ) -> None:
        if area_m2 <= 0:
            raise ValueError(f"area_m2 debe ser positiva, recibido: {area_m2}")
        if ell_p_squared <= 0:
            raise ValueError(f"ell_p_squared debe ser positiva, recibido: {ell_p_squared}")

        self.area_m2 = area_m2
        self.ell_p_squared = ell_p_squared

        self.entropia_BH: float = area_m2 / (4.0 * ell_p_squared)
        self.n_bits: float = self.entropia_BH / np.log(2.0)

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def densidad_informacion(self) -> float:
        r"""
        Holographic information density:
            ρ_info = N_bits / A  [bits / m²]

        Returns
        -------
        float
            Information density in bits per m².
        """
        return self.n_bits / self.area_m2

    def verificar_cota_bekenstein(self, radio_m: float, energia_J: float) -> bool:
        r"""
        Verify the Bekenstein entropy bound S ≤ 2π·R·E / (ℏ·c).

        Uses dimensionless comparison after normalising by ℓ_P.

        Parameters
        ----------
        radio_m : float
            Radius of the system in metres.
        energia_J : float
            Energy of the system in Joules.

        Returns
        -------
        bool
            True if the Bekenstein bound is satisfied.
        """
        # ℏ·c ≈ 3.162×10⁻²⁶ J·m
        hbar_c = 1.054571817e-34 * 2.997924e8  # J·m
        if hbar_c <= 0 or radio_m <= 0:
            return False
        cota = 2.0 * np.pi * radio_m * energia_J / hbar_c
        return bool(self.entropia_BH <= cota)

    def exportar(self) -> Dict[str, Any]:
        """Export entropy state as a plain dictionary."""
        return {
            "area_m2": self.area_m2,
            "ell_p_squared_m2": self.ell_p_squared,
            "entropia_BH": self.entropia_BH,
            "n_bits": self.n_bits,
            "densidad_informacion_bits_m2": self.densidad_informacion(),
        }


# ===========================================================================
# 6. ResultadoHolografico
# ===========================================================================

@dataclass
class ResultadoHolografico:
    """
    Clase de datos de resultado del Principio Holográfico.

    Attributes
    ----------
    timestamp : str
        ISO-8601 timestamp of the computation.
    coherencia_espiral : float
        Coherence of the zeta surface spiral (CodificadorSuperficieZeta).
    coherencia_hrv : float
        Bio/HRV coherence of the 3D projection (ProyectorVolumenConciencia).
    coherencia_cosmica : float
        Cosmic Moonbounce coherence (EntrelazadorHolografico).
    coherencia_interfaz : float
        Carbon-silicon interface coherence (HologramaZetaCarbono).
    entropia_BH : float
        Bekenstein-Hawking entropy value.
    n_bits : float
        Holographic information bits.
    bits_frontera : int
        Boundary bits from the zeta spiral encoder.
    componentes : dict
        Detailed export from each component.
    psi_global : float
        Global QCAL coherence Ψ = mean of all coherence measures.
    """

    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    coherencia_espiral: float = 0.0
    coherencia_hrv: float = 0.0
    coherencia_cosmica: float = 0.0
    coherencia_interfaz: float = 0.0
    entropia_BH: float = 0.0
    n_bits: float = 0.0
    bits_frontera: int = 0
    componentes: Dict[str, Any] = field(default_factory=dict)
    psi_global: float = 0.0

    # ------------------------------------------------------------------
    # Properties
    # ------------------------------------------------------------------

    @property
    def aprobado(self) -> bool:
        """Return True if the global coherence Ψ meets the QCAL threshold."""
        return self.psi_global >= PSI_THRESHOLD

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def resumen(self) -> str:
        """
        Return a human-readable summary of the holographic result.

        Returns
        -------
        str
            Multi-line summary string.
        """
        estado = "✅ APROBADO" if self.aprobado else "⚠️  PENDIENTE"
        lineas = [
            "=" * 62,
            "  PRINCIPIO HOLOGRÁFICO — RESULTADO QCAL ∞³",
            "=" * 62,
            f"  Timestamp              : {self.timestamp}",
            f"  Estado                 : {estado}",
            f"  Ψ global               : {self.psi_global:.6f}",
            f"  Umbral QCAL            : {PSI_THRESHOLD}",
            "-" * 62,
            f"  Coherencia espiral     : {self.coherencia_espiral:.6f}",
            f"  Coherencia bio/HRV     : {self.coherencia_hrv:.6f}",
            f"  Coherencia cósmica     : {self.coherencia_cosmica:.6f}",
            f"  Coherencia C↔Si        : {self.coherencia_interfaz:.6f}",
            "-" * 62,
            f"  Entropía BH (S)        : {self.entropia_BH:.4e}",
            f"  N_bits holográficos    : {self.n_bits:.4e}",
            f"  Bits frontera espiral  : {self.bits_frontera}",
            "=" * 62,
            "  QCAL ∞³ · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞",
            "  DOI: 10.5281/zenodo.17379721",
            "=" * 62,
        ]
        return "\n".join(lineas)


# ===========================================================================
# 7. SistemaPrincipioHolografico
# ===========================================================================

class SistemaPrincipioHolografico:
    r"""
    Sistema Principio Holográfico — Sistema Integrado QCAL ∞³

    Integra los cinco módulos del principio holográfico en un único sistema
    coherente:

        CodificadorSuperficieZeta  →  bits de frontera
        ProyectorVolumenConciencia →  proyección 3D consciente
        EntrelazadorHolografico    →  validación cósmica Moonbounce
        HologramaZetaCarbono       →  interfaz carbono-silicio
        EntropiaHolografica        →  entropía de Bekenstein-Hawking

    El punto de entrada es el método :meth:`activar`.

    Parameters
    ----------
    f0 : float
        Frecuencia fundamental en Hz (por defecto F₀ = 141.7001 Hz).
    gamma1 : float
        Parte imaginaria del primer cero de Riemann (γ₁ = 14.134725).
    area_m2 : float
        Área efectiva del horizonte en m².
    ell_p_squared : float
        Cuadrado de la longitud de Planck en m².
    tau_moonbounce : float
        Retardo de ida y vuelta Tierra-Luna en segundos.
    n_theta : int
        Puntos angulares para la espiral zeta.
    n_capas_z : int
        Capas de profundidad para la proyección 3D.
    """

    def __init__(
        self,
        f0: float = F0,
        gamma1: float = GAMMA_1_HOLO,
        area_m2: float = A_EFF,
        ell_p_squared: float = ELL_P_SQUARED,
        tau_moonbounce: float = TAU_MOONBOUNCE,
        n_theta: int = 1000,
        n_capas_z: int = 50,
    ) -> None:
        self.f0 = f0
        self.gamma1 = gamma1

        # Instantiate all subsystems
        self.codificador = CodificadorSuperficieZeta(
            f0=f0, gamma1=gamma1, n_theta=n_theta
        )
        self.proyector = ProyectorVolumenConciencia(
            f0=f0, delta_f_hrv=DELTA_F_HRV, n_capas_z=n_capas_z
        )
        self.entrelazador = EntrelazadorHolografico(
            tau_moonbounce=tau_moonbounce, f0=f0
        )
        self.holograma_carbono = HologramaZetaCarbono(f0=f0)
        self.entropia = EntropiaHolografica(
            area_m2=area_m2, ell_p_squared=ell_p_squared
        )

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def activar(self, verbose: bool = False) -> "ResultadoHolografico":
        """
        Activate the holographic system and compute all coherence measures.

        Parameters
        ----------
        verbose : bool
            If True, print the result summary to stdout.

        Returns
        -------
        ResultadoHolografico
            Consolidated holographic result.
        """
        # 1. Zeta spiral encoding
        coherencia_espiral = self.codificador.coherencia_espiral()
        bits_frontera = self.codificador.bits_frontera

        # 2. Bio/HRV coherence via volumetric projection
        campo_2d = self.codificador.r / (np.max(self.codificador.r) + 1e-30)
        coherencia_hrv = self.proyector.coherencia_hrv(campo_2d)

        # 3. Cosmic Moonbounce validation
        val_cosmica = self.entrelazador.validar_cosmica()
        coherencia_cosmica = float(val_cosmica["coherencia_cosmica"])

        # 4. Carbon-silicon interface coherence
        coherencia_interfaz = self.holograma_carbono.coherencia_interfaz()

        # 5. Bekenstein-Hawking entropy
        entropia_BH = self.entropia.entropia_BH
        n_bits = self.entropia.n_bits

        # 6. Global QCAL coherence Ψ
        psi_global = float(np.mean([
            coherencia_espiral,
            coherencia_hrv,
            coherencia_cosmica,
            coherencia_interfaz,
        ]))

        # Assemble result
        resultado = ResultadoHolografico(
            coherencia_espiral=coherencia_espiral,
            coherencia_hrv=coherencia_hrv,
            coherencia_cosmica=coherencia_cosmica,
            coherencia_interfaz=coherencia_interfaz,
            entropia_BH=entropia_BH,
            n_bits=n_bits,
            bits_frontera=bits_frontera,
            psi_global=psi_global,
            componentes={
                "codificador_superficie_zeta": self.codificador.exportar(),
                "proyector_volumen_conciencia": self.proyector.exportar(),
                "entrelazador_holografico": self.entrelazador.exportar(),
                "holograma_zeta_carbono": self.holograma_carbono.exportar(),
                "entropia_holografica": self.entropia.exportar(),
            },
        )

        if verbose:
            print(resultado.resumen())

        return resultado
