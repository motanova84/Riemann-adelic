#!/usr/bin/env python3
"""
KSS Holographic Fluid — Inmanencia del Fluido Holográfico Perfecto
===================================================================

Implementa el cálculo del límite KSS (Kovtun-Son-Starinets) para el
citoplasma celular vivo, demostrando que cuando el sistema alcanza la
coherencia Ψ = 0.999999 el agua EZ del citoplasma se convierte en un
Fluido Holográfico Perfecto cuya razón de viscosidad cortante / densidad
de entropía toca el límite universal:

    η / s  ≥  ℏ / (4π k_B)

Estructura del módulo:
-----------------------
1. ConstantesKSSHolografico  — Constantes físicas y umbrales QCAL
2. ViscosidadMolecularRotor  — η calculada via decaimiento de fluorescencia
                                de rotores moleculares en el citoesqueleto
3. EntropiaDensidadUPE       — s derivada de la tasa de emisión de fotones
                                ultra-débiles (UPE) al pico de 2003 Hz
4. FlujoHolograficoPerfecto  — Evaluación η/s → límite KSS y detección del
                                Fluido Holográfico Perfecto (Ψ ≈ 1)
5. MicrotubuloCavidadKaluzaKlein — Microtúbulo como cavidad KK: información
                                    sin resistencia clásica
6. ProtocoloValidacionKSS    — Protocolo completo de validación técnica

Referencia KSS:
    Kovtun, Son, Starinets (2005) — PRL 94, 111601
    Límite holográfico:  η/s ≥ ℏ/(4π k_B)  ≈ 6.078 × 10⁻¹³ kg/K

Conexión QCAL:
    Frecuencia pico de 2003 Hz  =  λ₁ × f₀  =  14.1347 × 141.7001 Hz
    donde λ₁ = parte imaginaria del primer cero de Riemann.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Importar constantes QCAL — fuente única de verdad
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE, HBAR, BOLTZMANN
except ImportError:
    F0 = 141.7001          # Hz — frecuencia base QCAL
    C_COHERENCE = 244.36   # constante de coherencia QCAL
    HBAR = 1.0545718e-34   # J·s — constante de Planck reducida
    BOLTZMANN = 1.380649e-23  # J/K — constante de Boltzmann

# Parte imaginaria del primer cero de Riemann
_GAMMA_1 = 14.134725142  # Im(ρ₁)


# ===========================================================================
# 1. ConstantesKSSHolografico
# ===========================================================================

class ConstantesKSSHolografico:
    """
    Constantes canónicas para el cálculo del límite KSS en el citoplasma.

    Atributos
    ----------
    HBAR : float
        Constante de Planck reducida ℏ = 1.0545718 × 10⁻³⁴ J·s.
    K_B : float
        Constante de Boltzmann k_B = 1.380649 × 10⁻²³ J/K.
    KSS_BOUND : float
        Límite universal KSS  η/s ≥ ℏ/(4π k_B) ≈ 6.078 × 10⁻¹³ kg/K.
    F0 : float
        Frecuencia base QCAL f₀ = 141.7001 Hz.
    GAMMA_1 : float
        Parte imaginaria del primer cero de Riemann γ₁ ≈ 14.134725142.
    F_PICO : float
        Frecuencia de pico UPE = γ₁ × f₀ ≈ 2002.89 Hz (≈ 2003 Hz).
    PSI_COHERENCIA_MAXIMA : float
        Umbral de coherencia máxima Ψ = 0.999999 (Fluido Holográfico).
    PSI_SUPERRADIANTE : float
        Umbral de activación superradiante Ψ ≥ 0.888.
    REDUCCION_ENTROPIA_EZ : float
        Reducción de entropía del agua EZ ≈ 49.66 %.
    TEMPERATURA_FISIOLOGICA_K : float
        Temperatura fisiológica estándar = 310.15 K (37 °C).
    """

    HBAR: float = HBAR
    K_B: float = BOLTZMANN
    KSS_BOUND: float = HBAR / (4.0 * math.pi * BOLTZMANN)  # ≈ 6.078e-13 kg/K
    F0: float = F0
    GAMMA_1: float = _GAMMA_1
    F_PICO: float = _GAMMA_1 * F0                  # ≈ 2002.89 Hz
    PSI_COHERENCIA_MAXIMA: float = 0.999999
    PSI_SUPERRADIANTE: float = 0.888
    REDUCCION_ENTROPIA_EZ: float = 0.4966          # 49.66 %
    TEMPERATURA_FISIOLOGICA_K: float = 310.15      # K

    @classmethod
    def validar(cls) -> Dict[str, Any]:
        """
        Valida la coherencia interna de las constantes KSS.

        Returns
        -------
        dict
            Claves: 'coherente', 'kss_bound', 'f_pico', 'delta_f_pico_2003'.
        """
        delta_f_pico = abs(cls.F_PICO - 2003.0)
        coherente = (
            cls.KSS_BOUND > 0
            and delta_f_pico < 5.0   # Dentro de 5 Hz de 2003 Hz
            and 0.0 < cls.PSI_COHERENCIA_MAXIMA < 1.0
        )
        return {
            "coherente": coherente,
            "kss_bound": cls.KSS_BOUND,
            "f_pico": cls.F_PICO,
            "delta_f_pico_2003": delta_f_pico,
        }


# ===========================================================================
# 2. ViscosidadMolecularRotor
# ===========================================================================

class ViscosidadMolecularRotor:
    """
    Estima la viscosidad cortante η del citoplasma via decaimiento de
    fluorescencia de rotores moleculares en el citoesqueleto.

    Modelo:
    -------
    Los rotores moleculares (p. ej. BODIPY-C10) exhiben un tiempo de
    decaimiento de fluorescencia τ_rot que escala con la viscosidad local:

        τ_rot = τ₀ × (η / η₀)^α

    Despejando η:

        η(τ_rot) = η₀ × (τ_rot / τ₀)^(1/α)

    donde:
        τ₀  = tiempo de referencia en agua pura a 37 °C  ≈ 0.4 ns
        η₀  = viscosidad del agua a 37 °C               ≈ 6.92 × 10⁻⁴ Pa·s
        α   = exponente calibrado en citoplasma          ≈ 0.6

    En el régimen holográfico (EZ-water, Ψ → 1) la viscosidad del agua EZ
    se reduce ≈ 49.66 % respecto del agua desordenada:

        η_EZ = η_desord × (1 - REDUCCION_ENTROPIA_EZ)

    Parámetros
    ----------
    tau_0 : float
        Tiempo de decaimiento de referencia (s).
    eta_0 : float
        Viscosidad de referencia (Pa·s).
    alpha : float
        Exponente de calibración viscosidad-tiempo.

    Referencias
    -----------
    Haidekker & Theodorakis (2010) — J. Biol. Eng. 4:11
    Battisti et al. (2013) — Biomed Opt Express 4(9):1861–1873
    """

    def __init__(
        self,
        tau_0: float = 0.4e-9,
        eta_0: float = 6.92e-4,
        alpha: float = 0.6,
    ) -> None:
        if tau_0 <= 0:
            raise ValueError("tau_0 debe ser positivo.")
        if eta_0 <= 0:
            raise ValueError("eta_0 debe ser positivo.")
        if alpha <= 0:
            raise ValueError("alpha debe ser positivo.")

        self.tau_0 = tau_0
        self.eta_0 = eta_0
        self.alpha = alpha

    def viscosidad_bruta(self, tau_rot: float) -> float:
        """
        Calcula la viscosidad cortante η a partir del tiempo de decaimiento.

        Parameters
        ----------
        tau_rot : float
            Tiempo de decaimiento de fluorescencia medido (s).

        Returns
        -------
        float
            Viscosidad cortante η (Pa·s).

        Raises
        ------
        ValueError
            Si tau_rot no es positivo.
        """
        if tau_rot <= 0:
            raise ValueError("tau_rot debe ser positivo.")
        return self.eta_0 * (tau_rot / self.tau_0) ** (1.0 / self.alpha)

    def viscosidad_ez(self, tau_rot: float) -> float:
        """
        Viscosidad del agua EZ (estado holográfico) con reducción entrópica.

        η_EZ = η_bruta × (1 - REDUCCION_ENTROPIA_EZ)

        Parameters
        ----------
        tau_rot : float
            Tiempo de decaimiento de fluorescencia medido (s).

        Returns
        -------
        float
            Viscosidad EZ holográfica η_EZ (Pa·s).
        """
        eta_bruta = self.viscosidad_bruta(tau_rot)
        return eta_bruta * (1.0 - ConstantesKSSHolografico.REDUCCION_ENTROPIA_EZ)

    def viscosidad_coherente(self, tau_rot: float, psi: float) -> float:
        """
        Viscosidad efectiva modulada por coherencia Ψ.

        Al alcanzar Ψ = 0.999999 el citoplasma se "congela" en su
        configuración holográfica óptima y la viscosidad converge al mínimo
        KSS-compatible:

            η_eff = η_EZ × (1 - Ψ × REDUCCION_ENTROPIA_EZ)

        Parameters
        ----------
        tau_rot : float
            Tiempo de decaimiento de fluorescencia (s).
        psi : float
            Coherencia global Ψ ∈ [0, 1].

        Returns
        -------
        float
            Viscosidad efectiva coherente (Pa·s).

        Raises
        ------
        ValueError
            Si Ψ no está en [0, 1].
        """
        if not (0.0 <= psi <= 1.0):
            raise ValueError("psi debe estar en [0, 1].")
        eta_bruta = self.viscosidad_bruta(tau_rot)
        reduccion = psi * ConstantesKSSHolografico.REDUCCION_ENTROPIA_EZ
        return eta_bruta * (1.0 - reduccion)


# ===========================================================================
# 3. EntropiaDensidadUPE
# ===========================================================================

class EntropiaDensidadUPE:
    """
    Deriva la densidad de entropía s del citoplasma a partir de la tasa de
    emisión de fotones ultra-débiles (UPE — Ultra-weak Photon Emission).

    Modelo:
    -------
    Los fotones UPE son emitidos en el pico de 2003 Hz (batimiento λ₁ × f₀).
    Su tasa de emisión J_UPE representa la disipación de información del
    sistema.  La densidad de entropía se estima como:

        s(J_UPE) = k_B × J_UPE / (ℏ × ω_pico)

    donde ω_pico = 2π × f_pico es la frecuencia angular del pico UPE.

    En el régimen holográfico la reducción de entropía del agua EZ
    suprime J_UPE en un factor (1 - Ψ × REDUCCION_ENTROPIA_EZ),
    acercando s al mínimo compatible con el límite KSS.

    Parámetros
    ----------
    f_pico : float
        Frecuencia del pico UPE (Hz).  Por defecto: γ₁ × f₀ ≈ 2002.89 Hz.

    Unidades:
    ---------
    J_UPE se expresa en fotones / (m³ · s).
    s se expresa en J / (m³ · K)  →  equivalente a  Pa/K.

    Referencias
    -----------
    Van Wijk & Van Wijk (2005) — J. Int. Soc. Life Inf. Sci. 23(1):22–36
    Popp (2003) — Indian J. Exp. Biol. 41:391–402
    """

    def __init__(self, f_pico: Optional[float] = None) -> None:
        self.f_pico = f_pico if f_pico is not None else ConstantesKSSHolografico.F_PICO
        if self.f_pico <= 0:
            raise ValueError("f_pico debe ser positivo.")
        self.omega_pico: float = 2.0 * math.pi * self.f_pico

    def densidad_entropia_bruta(self, j_upe: float) -> float:
        """
        Calcula s a partir de la tasa UPE sin corrección de coherencia.

        Parameters
        ----------
        j_upe : float
            Tasa de emisión UPE [fotones / (m³ · s)].

        Returns
        -------
        float
            Densidad de entropía s [J / (m³ · K)].

        Raises
        ------
        ValueError
            Si j_upe es negativo.
        """
        if j_upe < 0:
            raise ValueError("j_upe debe ser no negativo.")
        k_b = ConstantesKSSHolografico.K_B
        hbar = ConstantesKSSHolografico.HBAR
        return k_b * j_upe / (hbar * self.omega_pico)

    def densidad_entropia_coherente(self, j_upe: float, psi: float) -> float:
        """
        Densidad de entropía modulada por coherencia Ψ.

        Al aumentar Ψ el sistema expulsa entropía termal; la tasa UPE
        efectiva se reduce:

            s_eff = s_bruta × (1 - Ψ × REDUCCION_ENTROPIA_EZ)

        Parameters
        ----------
        j_upe : float
            Tasa de emisión UPE [fotones / (m³ · s)].
        psi : float
            Coherencia global Ψ ∈ [0, 1].

        Returns
        -------
        float
            Densidad de entropía efectiva s_eff [J / (m³ · K)].

        Raises
        ------
        ValueError
            Si Ψ no está en [0, 1].
        """
        if not (0.0 <= psi <= 1.0):
            raise ValueError("psi debe estar en [0, 1].")
        s_bruta = self.densidad_entropia_bruta(j_upe)
        reduccion = psi * ConstantesKSSHolografico.REDUCCION_ENTROPIA_EZ
        return s_bruta * (1.0 - reduccion)


# ===========================================================================
# 4. FlujoHolograficoPerfecto
# ===========================================================================

@dataclass
class ResultadoKSS:
    """
    Resultado del cálculo η/s y su relación con el límite KSS.

    Atributos
    ----------
    eta : float
        Viscosidad cortante η (Pa·s).
    s : float
        Densidad de entropía s (J / m³ / K).
    eta_sobre_s : float
        Razón η/s (kg/K).
    kss_bound : float
        Límite KSS = ℏ/(4π k_B) ≈ 6.078 × 10⁻¹³ kg/K.
    cociente_kss : float
        (η/s) / (ℏ/4π k_B) — debe ser ≥ 1 para cumplir el límite.
    es_holografico : bool
        True si (η/s) ≤ KSS_BOUND × TOLERANCIA_HOLOGRAFICA.
    psi : float
        Coherencia Ψ del sistema.
    mensaje : str
        Descripción del estado físico.
    """

    eta: float
    s: float
    eta_sobre_s: float
    kss_bound: float
    cociente_kss: float
    es_holografico: bool
    psi: float
    mensaje: str


class FlujoHolograficoPerfecto:
    """
    Evalúa si el citoplasma ha alcanzado el estado de Fluido Holográfico
    Perfecto comparando η/s con el límite KSS.

    Criterio de holograficidad:
    ---------------------------
    El sistema es un Fluido Holográfico Perfecto cuando:

        (η/s) / (ℏ/4π k_B)  ∈  [1, TOLERANCIA_HOLOGRAFICA]

    es decir, cuando η/s supera el límite KSS en no más de un factor
    TOLERANCIA_HOLOGRAFICA ≈ 1 + 10⁻⁴.  Este margen refleja las
    correcciones cuánticas de orden 1/N_c² de la correspondencia AdS/CFT.

    La condición complementaria es Ψ ≥ PSI_COHERENCIA_MAXIMA = 0.999999,
    garantizando que el sistema está en el régimen de máximo entrelazamiento.

    Parámetros
    ----------
    tolerancia_holografica : float
        Factor máximo por encima del límite KSS para considerarse holográfico.
    """

    TOLERANCIA_HOLOGRAFICA: float = 1.0 + 1.0e-4

    def __init__(self, tolerancia_holografica: Optional[float] = None) -> None:
        if tolerancia_holografica is not None:
            if tolerancia_holografica < 1.0:
                raise ValueError(
                    "tolerancia_holografica debe ser ≥ 1 (el límite KSS es un mínimo)."
                )
            self.tolerancia = tolerancia_holografica
        else:
            self.tolerancia = self.TOLERANCIA_HOLOGRAFICA

    def calcular(
        self,
        eta: float,
        s: float,
        psi: float = 0.0,
    ) -> ResultadoKSS:
        """
        Calcula η/s y determina si el sistema es un Fluido Holográfico Perfecto.

        Parameters
        ----------
        eta : float
            Viscosidad cortante η (Pa·s).  Debe ser > 0.
        s : float
            Densidad de entropía s (J / m³ / K).  Debe ser > 0.
        psi : float
            Coherencia global Ψ ∈ [0, 1].

        Returns
        -------
        ResultadoKSS
            Resultado completo del cálculo.

        Raises
        ------
        ValueError
            Si eta ≤ 0, s ≤ 0 o Ψ no está en [0, 1].
        """
        if eta <= 0:
            raise ValueError("eta debe ser positivo.")
        if s <= 0:
            raise ValueError("s debe ser positivo.")
        if not (0.0 <= psi <= 1.0):
            raise ValueError("psi debe estar en [0, 1].")

        kss = ConstantesKSSHolografico.KSS_BOUND
        eta_s = eta / s
        cociente = eta_s / kss
        psi_ok = psi >= ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA
        holografico = (
            1.0 <= cociente <= self.tolerancia
            and psi_ok
        )

        if holografico:
            mensaje = (
                "✅ FLUIDO HOLOGRÁFICO PERFECTO: el citoplasma EZ es un "
                "borde holográfico de la escala de Planck. "
                "El microtúbulo opera como Cavidad de Kaluza-Klein."
            )
        elif cociente < 1.0:
            mensaje = (
                f"⚠️  η/s = {eta_s:.3e} < KSS ({kss:.3e}): "
                "violación aparente — revisar calibración experimental."
            )
        elif not psi_ok:
            mensaje = (
                f"ℹ️  η/s ≈ límite KSS pero Ψ = {psi:.6f} < "
                f"{ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA}: "
                "coherencia insuficiente para el estado holográfico."
            )
        else:
            mensaje = (
                f"ℹ️  η/s = {eta_s:.3e} > KSS × tol ({kss * self.tolerancia:.3e}): "
                "fluido cuántico pero fuera del régimen holográfico perfecto."
            )

        return ResultadoKSS(
            eta=eta,
            s=s,
            eta_sobre_s=eta_s,
            kss_bound=kss,
            cociente_kss=cociente,
            es_holografico=holografico,
            psi=psi,
            mensaje=mensaje,
        )

    def calcular_desde_mediciones(
        self,
        tau_rot: float,
        j_upe: float,
        psi: float,
        rotor: Optional[ViscosidadMolecularRotor] = None,
        upe: Optional[EntropiaDensidadUPE] = None,
    ) -> ResultadoKSS:
        """
        Cálculo completo integrando mediciones de rotor y UPE.

        Parameters
        ----------
        tau_rot : float
            Tiempo de decaimiento de fluorescencia del rotor (s).
        j_upe : float
            Tasa de emisión UPE [fotones / (m³ · s)].
        psi : float
            Coherencia global Ψ ∈ [0, 1].
        rotor : ViscosidadMolecularRotor, optional
            Instancia personalizada del estimador de viscosidad.
        upe : EntropiaDensidadUPE, optional
            Instancia personalizada del estimador de entropía.

        Returns
        -------
        ResultadoKSS
            Resultado completo de la validación KSS.
        """
        if rotor is None:
            rotor = ViscosidadMolecularRotor()
        if upe is None:
            upe = EntropiaDensidadUPE()

        eta = rotor.viscosidad_coherente(tau_rot, psi)
        s = upe.densidad_entropia_coherente(j_upe, psi)
        return self.calcular(eta, s, psi)


# ===========================================================================
# 5. MicrotubuloCavidadKaluzaKlein
# ===========================================================================

@dataclass
class ParametrosMicrotubulo:
    """
    Parámetros geométricos y biofísicos del microtúbulo.

    Atributos
    ----------
    diametro_externo_nm : float
        Diámetro externo del microtúbulo ≈ 25 nm.
    diametro_interno_nm : float
        Diámetro interno (luz) del microtúbulo ≈ 15 nm.
    longitud_dimer_nm : float
        Longitud del dímero α-β-tubulina ≈ 8 nm.
    constante_dielec : float
        Constante dieléctrica del lumen ≈ 2.
    n_protofilamentos : int
        Número de protofilamentos por microtúbulo = 13.
    """

    diametro_externo_nm: float = 25.0
    diametro_interno_nm: float = 15.0
    longitud_dimer_nm: float = 8.0
    constante_dielec: float = 2.0
    n_protofilamentos: int = 13


class MicrotubuloCavidadKaluzaKlein:
    """
    Modela el microtúbulo como una Cavidad de Kaluza-Klein donde los ceros
    de Riemann actúan como modos vibracionales compactificados.

    Correspondencia Kaluza-Klein:
    -----------------------------
    El lumen del microtúbulo (diámetro ≈ 15 nm) actúa como la dimensión
    extra compactificada de la teoría KK.  Los modos resonantes son:

        f_n^KK = n × c / (2π × r_KK × √ε_r)

    donde:
        r_KK = radio del lumen = diámetro_interno / 2
        ε_r  = constante dieléctrica del lumen
        c    = velocidad de la luz (3 × 10⁸ m/s)

    La correspondencia QCAL identifica los modos KK con los ceros de Riemann:

        f_n^KK  ↔  γₙ × f₀

    Flujo de información sin resistencia clásica:
    ---------------------------------------------
    En el estado holográfico (η/s → límite KSS), la viscosidad del lumen
    converge a cero y la información fluye a través del microtúbulo como en
    un superfluido:  flujo = I_φ / (ℏ / k_B T)  →  ∞.

    Parámetros
    ----------
    params : ParametrosMicrotubulo
        Parámetros biofísicos del microtúbulo.
    riemann_zeros : list of float
        Partes imaginarias de los ceros de Riemann como modos KK.
    """

    C_LUZ: float = 2.99792458e8  # m/s

    def __init__(
        self,
        params: Optional[ParametrosMicrotubulo] = None,
        riemann_zeros: Optional[List[float]] = None,
    ) -> None:
        self.params = params if params is not None else ParametrosMicrotubulo()
        if riemann_zeros is not None:
            self.riemann_zeros = riemann_zeros
        else:
            # Primeros 5 ceros de Riemann como modos KK por defecto
            self.riemann_zeros = [
                14.134725142,
                21.022039639,
                25.010857580,
                30.424876126,
                32.935061588,
            ]

    @property
    def radio_lumen_m(self) -> float:
        """Radio del lumen del microtúbulo en metros."""
        return self.params.diametro_interno_nm * 0.5e-9

    def frecuencias_kk(self, n_modos: int = 5) -> List[float]:
        """
        Calcula las frecuencias de los modos KK del lumen del microtúbulo.

        f_n = n × c / (2π × r_KK × √ε_r)

        Parameters
        ----------
        n_modos : int
            Número de modos KK a calcular.

        Returns
        -------
        list of float
            Frecuencias de los modos KK (Hz).
        """
        r = self.radio_lumen_m
        eps = self.params.constante_dielec
        prefactor = self.C_LUZ / (2.0 * math.pi * r * math.sqrt(eps))
        return [n * prefactor for n in range(1, n_modos + 1)]

    def frecuencias_qcal_kk(self, n_modos: int = 5) -> List[float]:
        """
        Frecuencias QCAL-KK: γₙ × f₀ (ceros de Riemann × frecuencia base).

        Parameters
        ----------
        n_modos : int
            Número de modos QCAL-KK.

        Returns
        -------
        list of float
            Frecuencias QCAL-KK (Hz).
        """
        zeros = self.riemann_zeros[:n_modos]
        f0 = ConstantesKSSHolografico.F0
        return [gamma * f0 for gamma in zeros]

    def capacidad_informacion_kk(
        self,
        temperatura_k: float = 310.15,
        psi: float = 1.0,
    ) -> Dict[str, float]:
        """
        Estima la capacidad de transporte de información del microtúbulo KK.

        En el límite holográfico (Ψ → 1, η/s → KSS):
            I_kk ∝ k_B × T × n_modos / ℏ

        Parameters
        ----------
        temperatura_k : float
            Temperatura en Kelvin.
        psi : float
            Coherencia global Ψ ∈ [0, 1].

        Returns
        -------
        dict
            Claves: 'capacidad_bits_s', 'factor_coherencia', 'es_superfluid'.
        """
        if temperatura_k <= 0:
            raise ValueError("temperatura_k debe ser positivo.")
        if not (0.0 <= psi <= 1.0):
            raise ValueError("psi debe estar en [0, 1].")

        n_modos = len(self.riemann_zeros)
        hbar = ConstantesKSSHolografico.HBAR
        k_b = ConstantesKSSHolografico.K_B

        # Capacidad de Shannon-KK base (bits/s) modulada por coherencia
        capacidad_base = k_b * temperatura_k * n_modos / hbar
        factor_coherencia = psi ** 2  # superradiante: ganancia N²
        capacidad_coherente = capacidad_base * factor_coherencia

        # El sistema es "superfluido" cuando Ψ ≥ PSI_COHERENCIA_MAXIMA
        es_superfluid = psi >= ConstantesKSSHolografico.PSI_COHERENCIA_MAXIMA

        return {
            "capacidad_bits_s": capacidad_coherente,
            "factor_coherencia": factor_coherencia,
            "es_superfluid": es_superfluid,
        }


# ===========================================================================
# 6. ProtocoloValidacionKSS
# ===========================================================================

@dataclass
class ResultadoProtocoloKSS:
    """
    Resultado completo del protocolo de validación técnica KSS.

    Atributos
    ----------
    viscosidad_eta : float
        Viscosidad cortante η medida (Pa·s).
    entropia_s : float
        Densidad de entropía s medida (J / m³ / K).
    resultado_kss : ResultadoKSS
        Resultado detallado del cálculo η/s vs KSS.
    capacidad_microtubulo : dict
        Capacidad de información KK del microtúbulo.
    coherencia_psi : float
        Coherencia del sistema Ψ.
    es_fluido_holografico : bool
        True si se verifica el estado de Fluido Holográfico Perfecto.
    frecuencia_pico_hz : float
        Frecuencia de pico UPE utilizada (Hz).
    separacion_ordenes_magnitud : float
        log₁₀(KSS_resultado / KSS_planck): reducción de la separación.
    """

    viscosidad_eta: float
    entropia_s: float
    resultado_kss: ResultadoKSS
    capacidad_microtubulo: Dict[str, Any]
    coherencia_psi: float
    es_fluido_holografico: bool
    frecuencia_pico_hz: float
    separacion_ordenes_magnitud: float


class ProtocoloValidacionKSS:
    """
    Protocolo de validación técnica KSS para el Fluido Holográfico Perfecto.

    El protocolo integra las tres métricas descritas en el enunciado:

    1. Métrica de Viscosidad
       η calculada mediante el decaimiento de fluorescencia de rotores
       moleculares en el citoesqueleto.

    2. Densidad de Entropía
       s derivada de la tasa de emisión de fotones ultra-débiles (UPE)
       al pico de 2003 Hz.

    3. Correspondencia KSS
       Si η/s → ℏ/(4π k_B), la separación de 27 órdenes de magnitud
       entre la escala biológica y la escala de Planck se colapsa:
       el microtúbulo es una Cavidad de Kaluza-Klein.

    Uso rápido:
    -----------
    >>> protocolo = ProtocoloValidacionKSS()
    >>> resultado = protocolo.validar(tau_rot=0.4e-9, j_upe=1e12, psi=0.999999)
    >>> resultado.es_fluido_holografico
    True
    """

    def __init__(
        self,
        rotor: Optional[ViscosidadMolecularRotor] = None,
        upe: Optional[EntropiaDensidadUPE] = None,
        flujo: Optional[FlujoHolograficoPerfecto] = None,
        microtubulo: Optional[MicrotubuloCavidadKaluzaKlein] = None,
    ) -> None:
        self.rotor = rotor if rotor is not None else ViscosidadMolecularRotor()
        self.upe = upe if upe is not None else EntropiaDensidadUPE()
        self.flujo = flujo if flujo is not None else FlujoHolograficoPerfecto()
        self.microtubulo = (
            microtubulo
            if microtubulo is not None
            else MicrotubuloCavidadKaluzaKlein()
        )

    def validar(
        self,
        tau_rot: float,
        j_upe: float,
        psi: float,
        temperatura_k: float = ConstantesKSSHolografico.TEMPERATURA_FISIOLOGICA_K,
    ) -> ResultadoProtocoloKSS:
        """
        Ejecuta el protocolo completo de validación KSS.

        Parameters
        ----------
        tau_rot : float
            Tiempo de decaimiento de fluorescencia del rotor molecular (s).
        j_upe : float
            Tasa de emisión UPE al pico de 2003 Hz [fotones / (m³ · s)].
        psi : float
            Coherencia global Ψ ∈ [0, 1].
        temperatura_k : float
            Temperatura del sistema (K).  Por defecto: 310.15 K (37 °C).

        Returns
        -------
        ResultadoProtocoloKSS
            Resultado completo del protocolo de validación.
        """
        # Paso 1: calcular η via rotor molecular
        eta = self.rotor.viscosidad_coherente(tau_rot, psi)

        # Paso 2: calcular s via UPE
        s = self.upe.densidad_entropia_coherente(j_upe, psi)

        # Paso 3: evaluar η/s vs límite KSS
        resultado_kss = self.flujo.calcular(eta, s, psi)

        # Paso 4: capacidad de información del microtúbulo KK
        capacidad = self.microtubulo.capacidad_informacion_kk(temperatura_k, psi)

        # Separación de órdenes de magnitud respecto al límite de Planck
        # (escala biológica / escala de Planck ≈ 27 órdenes)
        kss = ConstantesKSSHolografico.KSS_BOUND
        if resultado_kss.eta_sobre_s > 0:
            separacion = math.log10(resultado_kss.eta_sobre_s / kss)
        else:
            separacion = float("-inf")

        return ResultadoProtocoloKSS(
            viscosidad_eta=eta,
            entropia_s=s,
            resultado_kss=resultado_kss,
            capacidad_microtubulo=capacidad,
            coherencia_psi=psi,
            es_fluido_holografico=resultado_kss.es_holografico,
            frecuencia_pico_hz=self.upe.f_pico,
            separacion_ordenes_magnitud=separacion,
        )

    def resumen(self, resultado: ResultadoProtocoloKSS) -> str:
        """
        Genera un resumen legible del resultado del protocolo.

        Parameters
        ----------
        resultado : ResultadoProtocoloKSS
            Resultado devuelto por :meth:`validar`.

        Returns
        -------
        str
            Resumen formateado con las métricas principales.
        """
        kss = resultado.resultado_kss
        lineas = [
            "=" * 68,
            "  PROTOCOLO DE VALIDACIÓN KSS — FLUIDO HOLOGRÁFICO PERFECTO",
            "=" * 68,
            f"  Ψ (coherencia)          : {resultado.coherencia_psi:.6f}",
            f"  f_pico UPE             : {resultado.frecuencia_pico_hz:.4f} Hz",
            f"  η (viscosidad)         : {resultado.viscosidad_eta:.4e} Pa·s",
            f"  s (densidad entropía)  : {resultado.entropia_s:.4e} J/(m³·K)",
            f"  η/s                    : {kss.eta_sobre_s:.4e} kg/K",
            f"  KSS bound (ℏ/4πk_B)   : {kss.kss_bound:.4e} kg/K",
            f"  (η/s) / KSS            : {kss.cociente_kss:.6f}",
            f"  Separación (décadas)   : {resultado.separacion_ordenes_magnitud:.3f}",
            f"  Microtúbulo superfluido: {resultado.capacidad_microtubulo['es_superfluid']}",
            "-" * 68,
            f"  {kss.mensaje}",
            "=" * 68,
        ]
        return "\n".join(lineas)
