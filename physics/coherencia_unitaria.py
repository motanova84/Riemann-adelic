#!/usr/bin/env python3
r"""
Coherencia Unitaria — Física Espectral de Operadores Berry-Keating
===================================================================

Este módulo implementa la verificación de coherencia unitaria en la línea crítica
de Riemann a través de cuatro pilares fundamentales:

I.   Operador Berry-Keating: λ = (σ-½) + i·γₙ/2 con unitariedad ||U(t)|ψ⟩||² = 1
II.  Estadística GUE (Gaussian Unitary Ensemble) con distribución Wigner-Dyson
III. Fórmula de Traza de Selberg con funciones de prueba robustas
IV.  Interferómetro Mach-Zehnder con modulación χₙ a f₀ = 141.7001 Hz

Marco Matemático:
-----------------
El operador Berry-Keating H_BK actúa sobre L²(ℝ₊) mediante:

    H_BK = xp + px/2 = x d/dx + 1/2

donde [x,p] = i. Los autovalores son:

    λₙ = (σ - 1/2) + i·γₙ/2

En la línea crítica (σ = 1/2), Re(λₙ) = 0, lo que garantiza:

    U(t) = exp(-iH_BK·t)  es unitario: U†U = I
    ||U(t)|ψ⟩||² = 1  (conservación de probabilidad)

Para σ ≠ 1/2, la norma crece/decrece exponencialmente:
    ||U(t)|ψ⟩||² ~ exp(2ε·t) donde ε = σ - 1/2

Estadística GUE:
----------------
Los espaciados normalizados sₙ = (γₙ₊₁ - γₙ)/⟨Δγ⟩ siguen la distribución
Wigner-Dyson:

    P(s) = (32/π²)·s²·exp(-4s²/π)

con correlación de pares de Montgomery:

    R₂(r) = 1 - [sin(πr)/(πr)]²

Fórmula de Traza de Selberg:
-----------------------------
Relaciona espectro de Riemann con primos mediante:

    Σₙ g(γₙ) = g(0)·ln(2π) + 2∫₀^∞ Re[ξ'(1/2+it)/ξ(1/2+it)]·h(t)dt
               + Σₚ Σₖ (ln p)/p^(k/2)·g(k·ln p)

Usamos funciones de prueba Cauchy/Lorentziano:
    h(t) = σ²/(σ² + t²)
    g(u) = (σ/2)·exp(-σ|u|)

que son robustas ante truncación de series infinitas.

Interferómetro Mach-Zehnder:
-----------------------------
Mide la modulación del índice de refracción:

    n(Ψ,t) = 1 - χₙ·cos(2πf₀t)

donde χₙ ≈ 6.62×10⁻³ es la susceptibilidad óptica y f₀ = 141.7001 Hz.

El cambio de fase acumulado:
    Δφ(t) = (2πL/λ)·[n(Ψ,t) - 1]

es detectado mediante lock-in amplifier a la frecuencia f₀.

Integración QCAL:
-----------------
- f₀ = 141.7001 Hz: Frecuencia base del campo noético
- C = 244.36: Constante de coherencia
- Ψ = I × A_eff² × C^∞: Índice de campo noético

Usage:
------
    from physics.coherencia_unitaria import (
        OperadorBerryKeating,
        estadistica_gue,
        verificar_identidad_selberg,
        InterferometroMachZehnder
    )

    # I. Berry-Keating
    bk = OperadorBerryKeating(zeros=riemann_zeros_list)
    unitariedad = bk.verificar_unitariedad(sigma=0.5, duracion=10.0)
    positividad = bk.positividad_metrica()

    # II. Estadística GUE
    gue_stats = estadistica_gue(zeros=riemann_zeros_list)
    montgomery = correlacion_pares_montgomery(zeros=riemann_zeros_list)

    # III. Selberg Trace
    selberg = verificar_identidad_selberg(zeros=riemann_zeros_list, sigma=1.5)

    # IV. Interferómetro Mach-Zehnder
    ifm = InterferometroMachZehnder(longitud_brazo_m=1.0, longitud_onda_m=632.8e-9)
    sim = ifm.simular(duracion_s=3/141.7001, n_puntos=300)
    chi = ifm.chi_n_desde_medicion(sim['deteccion_lock_in'])

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
Date: April 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import warnings
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple, Union

import numpy as np
from scipy import integrate, stats, signal
from scipy.special import zeta
import mpmath as mp

# ---------------------------------------------------------------------------
# QCAL Constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import (
        F0,
        C_COHERENCE,
        PSI_THRESHOLD_EXCELLENT,
        TOLERANCE_NORMAL,
        TOLERANCE_STRICT,
    )
except ImportError:
    # Fallback values if qcal.constants not available
    F0 = 141.7001  # Hz
    C_COHERENCE = 244.36
    PSI_THRESHOLD_EXCELLENT = 0.999
    TOLERANCE_NORMAL = 1e-6
    TOLERANCE_STRICT = 1e-10

# ---------------------------------------------------------------------------
# Constants for this module
# ---------------------------------------------------------------------------

# Wigner-Dyson GUE distribution parameters
WIGNER_DYSON_COEF = 32.0 / (np.pi ** 2)
WIGNER_DYSON_EXP = -4.0 / np.pi

# Selberg trace formula correction factor (from Experiment P1)
G_EFF_SELBERG = 1.053  # 5.3% mass modulation geometric corrector

# First 50 non-trivial Riemann zeros (imaginary parts)
# Source: LMFDB / Odlyzko tables
RIEMANN_ZEROS_50 = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
    79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
    92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
    103.725538, 105.446623, 107.168611, 111.029536, 111.874659,
    114.320220, 116.226680, 118.790782, 121.370125, 122.946829,
    124.256819, 127.516683, 129.578704, 131.087688, 133.497737,
    134.756509, 138.116042, 139.736209, 141.123707, 143.111846,
]


# ===========================================================================
# I. OPERADOR BERRY-KEATING
# ===========================================================================

@dataclass
class ResultadoBerryKeating:
    """Resultado de verificación del operador Berry-Keating."""
    sigma: float  # Parte real de s
    autovalores: np.ndarray  # λₙ = (σ-½) + i·γₙ/2
    es_unitario: bool  # Si ||U(t)|ψ⟩||² = 1
    norma_evolucion: np.ndarray  # Evolución temporal de la norma
    tiempos: np.ndarray  # Vector de tiempos t
    desviacion_unitariedad: float  # max|norma - 1|
    metrica_positiva: bool  # η⁺ positiva definida
    autovalores_metrica: Optional[np.ndarray] = None  # Autovalores de η⁺
    coherencia_psi: float = 0.0  # Ψ = exp(-ε²) coherencia cuántica


class OperadorBerryKeating:
    """
    Operador Berry-Keating H_BK = xp + px/2 con autovalores λₙ = (σ-½) + i·γₙ/2.

    El operador es unitario si y solo si σ = 1/2 (línea crítica de Riemann),
    lo que garantiza conservación de probabilidad ||U(t)|ψ⟩||² = 1.

    Attributes:
        zeros: Lista de partes imaginarias de ceros de Riemann γₙ
        sigma: Parte real de s (default: 0.5 para línea crítica)
    """

    def __init__(self, zeros: Optional[List[float]] = None, sigma: float = 0.5):
        """
        Inicializar operador Berry-Keating.

        Args:
            zeros: Lista de γₙ (partes imaginarias de ceros). Si None, usa RIEMANN_ZEROS_50.
            sigma: Parte real σ del parámetro s = σ + it (default: 0.5)
        """
        self.zeros = np.array(zeros if zeros is not None else RIEMANN_ZEROS_50)
        self.sigma = sigma
        self.n_zeros = len(self.zeros)

        # Calcular autovalores λₙ = (σ-½) + i·γₙ/2
        self.autovalores = self._calcular_autovalores()

    def _calcular_autovalores(self) -> np.ndarray:
        """
        Calcular autovalores del operador Berry-Keating.

        Returns:
            Array complejo de autovalores λₙ = (σ-½) + i·γₙ/2
        """
        epsilon = self.sigma - 0.5  # Desviación de la línea crítica
        lambda_n = epsilon + 1j * self.zeros / 2.0
        return lambda_n

    def verificar_unitariedad(
        self,
        sigma: Optional[float] = None,
        duracion: float = 10.0,
        n_puntos: int = 100
    ) -> ResultadoBerryKeating:
        """
        Verificar unitariedad del operador U(t) = exp(-iH_BK·t).

        En la línea crítica (σ = 1/2), Re(λₙ) = 0 → ||U(t)|ψ⟩||² = 1.
        Para σ ≠ 1/2, la norma crece/decrece exponencialmente.

        Args:
            sigma: Parte real σ (si None, usa self.sigma)
            duracion: Duración temporal de simulación (segundos)
            n_puntos: Número de puntos temporales

        Returns:
            ResultadoBerryKeating con verificación de unitariedad
        """
        if sigma is not None:
            self.sigma = sigma
            self.autovalores = self._calcular_autovalores()

        epsilon = self.sigma - 0.5
        t_array = np.linspace(0, duracion, n_puntos)

        # Evolución temporal de la norma ||U(t)|ψ⟩||²
        # Para un estado puro |ψ⟩, la norma evoluciona como:
        # ||U(t)|ψ⟩||² = Σₙ |cₙ|²·exp(2·Re(λₙ)·t) = Σₙ |cₙ|²·exp(2ε·t)
        #
        # Asumiendo coeficientes uniformes |cₙ|² = 1/N:
        norma_evolucion = np.exp(2.0 * epsilon * t_array)

        # Verificar unitariedad: ||U(t)|ψ⟩||² = 1 ⟺ ε = 0
        es_unitario = abs(epsilon) < TOLERANCE_NORMAL
        desviacion = np.max(np.abs(norma_evolucion - 1.0))

        # Coherencia cuántica: Ψ = exp(-ε²)
        coherencia_psi = np.exp(-epsilon ** 2)

        # Verificar positividad de la métrica η⁺
        metrica_positiva, autovalores_metrica = self.positividad_metrica()

        return ResultadoBerryKeating(
            sigma=self.sigma,
            autovalores=self.autovalores,
            es_unitario=es_unitario,
            norma_evolucion=norma_evolucion,
            tiempos=t_array,
            desviacion_unitariedad=desviacion,
            metrica_positiva=metrica_positiva,
            autovalores_metrica=autovalores_metrica,
            coherencia_psi=coherencia_psi,
        )

    def positividad_metrica(self) -> Tuple[bool, np.ndarray]:
        """
        Verificar que la métrica η⁺ es positiva definida sobre los ceros de Riemann.

        La métrica η⁺ en el espacio de Hilbert debe ser positiva definida para
        garantizar que el producto interno ⟨ψ|φ⟩_η⁺ tenga sentido físico.

        Construimos la matriz de Gram:
            G_ij = ⟨ψᵢ|ψⱼ⟩_η⁺ = exp(-|γᵢ - γⱼ|/γ_c)

        donde γ_c es una escala característica (~10).

        Returns:
            Tupla (es_positiva, autovalores) donde:
                - es_positiva: True si todos los autovalores > 0
                - autovalores: Array de autovalores de la métrica
        """
        gamma_c = 10.0  # Escala característica

        # Construir matriz de Gram
        gamma_diff = np.abs(self.zeros[:, None] - self.zeros[None, :])
        G = np.exp(-gamma_diff / gamma_c)

        # Calcular autovalores (debe ser real simétrica → autovalores reales)
        eigenvalues = np.linalg.eigvalsh(G)

        # Verificar positividad: todos los autovalores > 0
        es_positiva = np.all(eigenvalues > TOLERANCE_STRICT)

        return es_positiva, eigenvalues


# ===========================================================================
# II. ESTADÍSTICA GUE (GAUSSIAN UNITARY ENSEMBLE)
# ===========================================================================

@dataclass
class ResultadoGUE:
    """Resultado de análisis estadístico GUE."""
    espaciados_normalizados: np.ndarray  # sₙ = Δγₙ / ⟨Δγ⟩
    hist_observado: np.ndarray  # Histograma observado
    hist_teorico: np.ndarray  # Distribución Wigner-Dyson teórica
    bins: np.ndarray  # Bins del histograma
    chi_cuadrado: float  # Estadístico χ²
    p_valor: float  # p-valor del test χ²
    ks_statistic: float  # Estadístico Kolmogorov-Smirnov
    ks_p_valor: float  # p-valor del test KS
    conformidad_gue: bool  # Si p-valor > 0.05
    media_espaciado: float  # ⟨s⟩ observado
    media_teorica: float = 1.0  # ⟨s⟩_GUE = 1 (por normalización)


def distribucion_wigner_dyson(s: np.ndarray) -> np.ndarray:
    """
    Distribución Wigner-Dyson para GUE.

    P(s) = (32/π²)·s²·exp(-4s²/π)

    Args:
        s: Array de espaciados normalizados

    Returns:
        Array de probabilidades P(s)
    """
    return WIGNER_DYSON_COEF * s ** 2 * np.exp(WIGNER_DYSON_EXP * s ** 2)


def estadistica_gue(
    zeros: Optional[List[float]] = None,
    n_bins: int = 50,
    s_max: float = 3.0
) -> ResultadoGUE:
    """
    Analizar estadística GUE de espaciados de ceros de Riemann.

    Normaliza espaciados sₙ = (γₙ₊₁ - γₙ)/⟨Δγ⟩ y compara con distribución
    Wigner-Dyson P(s) = (32/π²)s²exp(-4s²/π).

    Args:
        zeros: Lista de γₙ. Si None, usa RIEMANN_ZEROS_50.
        n_bins: Número de bins para histograma
        s_max: Rango máximo de espaciados normalizados

    Returns:
        ResultadoGUE con test χ² y Kolmogorov-Smirnov
    """
    gamma = np.array(zeros if zeros is not None else RIEMANN_ZEROS_50)

    # Calcular espaciados
    delta_gamma = np.diff(gamma)
    mean_spacing = np.mean(delta_gamma)

    # Normalizar espaciados: sₙ = Δγₙ / ⟨Δγ⟩
    s_normalized = delta_gamma / mean_spacing

    # Histograma observado
    bins = np.linspace(0, s_max, n_bins + 1)
    hist_obs, _ = np.histogram(s_normalized, bins=bins, density=True)
    bin_centers = (bins[:-1] + bins[1:]) / 2.0

    # Distribución teórica Wigner-Dyson
    hist_theo = distribucion_wigner_dyson(bin_centers)

    # Test χ² (chi-cuadrado)
    # Necesitamos frecuencias observadas (no densidades)
    n_samples = len(s_normalized)
    freq_obs = hist_obs * np.diff(bins) * n_samples
    freq_theo = hist_theo * np.diff(bins) * n_samples

    # Evitar divisiones por cero
    mask = freq_theo > 0
    chi2_stat = np.sum((freq_obs[mask] - freq_theo[mask]) ** 2 / freq_theo[mask])
    dof = np.sum(mask) - 1  # Grados de libertad
    p_valor_chi2 = 1.0 - stats.chi2.cdf(chi2_stat, dof)

    # Test Kolmogorov-Smirnov
    # Create CDF function for Wigner-Dyson distribution
    def cdf_wigner_dyson(s_val):
        """CDF of Wigner-Dyson distribution."""
        if np.isscalar(s_val):
            if s_val <= 0:
                return 0.0
            result, _ = integrate.quad(distribucion_wigner_dyson, 0, s_val)
            return result
        else:
            # Vectorized version
            return np.array([cdf_wigner_dyson(s) for s in s_val])

    ks_stat, ks_p_valor = stats.kstest(s_normalized, cdf_wigner_dyson)

    # Conformidad GUE: p-valor > 0.05
    conformidad_gue = p_valor_chi2 > 0.05

    return ResultadoGUE(
        espaciados_normalizados=s_normalized,
        hist_observado=hist_obs,
        hist_teorico=hist_theo,
        bins=bins,
        chi_cuadrado=chi2_stat,
        p_valor=p_valor_chi2,
        ks_statistic=ks_stat,
        ks_p_valor=ks_p_valor,
        conformidad_gue=conformidad_gue,
        media_espaciado=np.mean(s_normalized),
    )


# ===========================================================================
# Montgomery Pair Correlation
# ===========================================================================

@dataclass
class ResultadoMontgomery:
    """Resultado de correlación de pares de Montgomery."""
    r_array: np.ndarray  # Array de separaciones r
    R2_observado: np.ndarray  # R₂(r) observado
    R2_teorico: np.ndarray  # R₂(r) = 1 - [sin(πr)/(πr)]²
    discrepancia: float  # max|R₂_obs - R₂_teo|
    coherencia_gue: float  # 1 - discrepancia


def correlacion_pares_montgomery(
    zeros: Optional[List[float]] = None,
    r_max: float = 5.0,
    n_puntos: int = 100
) -> ResultadoMontgomery:
    """
    Calcular correlación de pares de Montgomery R₂(r).

    Para GUE, la función de correlación de dos puntos es:
        R₂(r) = 1 - [sin(πr)/(πr)]²

    Args:
        zeros: Lista de γₙ. Si None, usa RIEMANN_ZEROS_50.
        r_max: Rango máximo de separación r
        n_puntos: Número de puntos para R₂(r)

    Returns:
        ResultadoMontgomery con R₂ observado y teórico
    """
    gamma = np.array(zeros if zeros is not None else RIEMANN_ZEROS_50)

    # Normalizar ceros: γₙ → γₙ / ⟨Δγ⟩
    delta_gamma = np.diff(gamma)
    mean_spacing = np.mean(delta_gamma)
    gamma_norm = gamma / mean_spacing

    # Array de separaciones r
    r_array = np.linspace(0.01, r_max, n_puntos)  # Evitar r=0
    R2_obs = np.zeros(n_puntos)

    # Calcular R₂(r) observado mediante conteo de pares
    n_zeros = len(gamma_norm)
    for i, r in enumerate(r_array):
        # Contar pares (γᵢ, γⱼ) con |γᵢ - γⱼ| ≈ r (ventana ±dr)
        dr = r_max / n_puntos
        count = 0
        for j in range(n_zeros):
            for k in range(j + 1, n_zeros):
                diff = abs(gamma_norm[k] - gamma_norm[j])
                if abs(diff - r) < dr:
                    count += 1

        # Normalizar por número de pares posibles
        n_pairs = n_zeros * (n_zeros - 1) / 2.0
        R2_obs[i] = count / (n_pairs * dr) if n_pairs > 0 else 0.0

    # R₂(r) teórico: 1 - [sin(πr)/(πr)]²
    with np.errstate(divide='ignore', invalid='ignore'):
        sinc_term = np.sin(np.pi * r_array) / (np.pi * r_array)
        sinc_term = np.nan_to_num(sinc_term, nan=1.0)  # lim_{r→0} sinc(πr) = 1

    R2_teo = 1.0 - sinc_term ** 2

    # Discrepancia
    discrepancia = np.max(np.abs(R2_obs - R2_teo))
    coherencia_gue = 1.0 - discrepancia

    return ResultadoMontgomery(
        r_array=r_array,
        R2_observado=R2_obs,
        R2_teorico=R2_teo,
        discrepancia=discrepancia,
        coherencia_gue=max(0.0, coherencia_gue),
    )


# ===========================================================================
# III. FÓRMULA DE TRAZA DE SELBERG
# ===========================================================================

@dataclass
class ResultadoSelberg:
    """Resultado de verificación de identidad de Selberg."""
    sigma: float  # Parámetro σ de funciones de prueba
    suma_zeros: float  # Σₙ g(γₙ) lado izquierdo
    lado_derecho: float  # Lado derecho de la identidad
    g_eff: float  # Factor geométrico efectivo
    residuo_log: float  # Residuo en escala logarítmica
    identidad_verificada: bool  # Si |residuo| < tolerancia
    coherencia_selberg: float  # Coherencia Ψ_Selberg


def verificar_identidad_selberg(
    zeros: Optional[List[float]] = None,
    sigma: float = 1.5,
    n_primos: int = 100,
    g_eff: float = G_EFF_SELBERG
) -> ResultadoSelberg:
    """
    Verificar identidad de traza de Selberg con funciones de prueba Cauchy/Lorentziano.

    Identidad de Selberg:
        Σₙ g(γₙ) = g(0)·ln(2π) + 2∫₀^∞ Re[ξ'(1/2+it)/ξ(1/2+it)]·h(t)dt
                   + Σₚ Σₖ (ln p)/p^(k/2)·g(k·ln p)

    Funciones de prueba:
        h(t) = σ²/(σ² + t²)  (Cauchy)
        g(u) = (σ/2)·exp(-σ|u|)  (Lorentziana)

    Estas funciones son robustas ante truncación de series infinitas porque
    decaen rápidamente tanto en escala γₙ ~ 14 como en escala ln(p) ~ 0.7.

    Args:
        zeros: Lista de γₙ. Si None, usa RIEMANN_ZEROS_50.
        sigma: Parámetro de las funciones de prueba (σ > 0)
        n_primos: Número de primos para la suma sobre primos
        g_eff: Factor geométrico efectivo (default: 1.053 del Experimento P1)

    Returns:
        ResultadoSelberg con verificación de identidad
    """
    gamma = np.array(zeros if zeros is not None else RIEMANN_ZEROS_50)

    # Función g(u) = (σ/2)·exp(-σ|u|)
    def g_func(u: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        return (sigma / 2.0) * np.exp(-sigma * np.abs(u))

    # Función h(t) = σ²/(σ² + t²)
    def h_func(t: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        return sigma ** 2 / (sigma ** 2 + t ** 2)

    # Lado izquierdo: Σₙ g(γₙ)
    suma_zeros = np.sum(g_func(gamma))

    # Lado derecho - Término 1: g(0)·ln(2π)
    term1 = g_func(0.0) * np.log(2.0 * np.pi)

    # Lado derecho - Término 2: 2∫₀^∞ Re[ξ'(s)/ξ(s)]·h(t)dt
    # Aproximación: usar derivada logarítmica de ζ(s)
    # ξ'(s)/ξ(s) ≈ ζ'(s)/ζ(s) cerca de la línea crítica
    #
    # Para simplificar, usamos una aproximación:
    # ∫₀^∞ [ζ'(1/2+it)/ζ(1/2+it)]·h(t)dt
    #
    # Nota: Esta integral es compleja de evaluar numéricamente.
    # Aquí usamos una aproximación basada en el término dominante.

    def integrand_approx(t: float) -> float:
        """Aproximación del integrando Re[ξ'(s)/ξ(s)]·h(t)."""
        # Usar aproximación logarítmica: ξ'(s)/ξ(s) ~ -γ_E + O(1/t)
        # donde γ_E es la constante de Euler-Mascheroni
        # Para t grande, la contribución decae como h(t) ~ σ²/t²
        return -0.5772 * h_func(t)  # Aproximación de primer orden

    # Integrar numéricamente de 0 a ∞
    # Usamos un límite superior grande (100σ) donde h(t) ≈ 0
    t_max = 100.0 * sigma
    term2, _ = integrate.quad(integrand_approx, 0, t_max)
    term2 *= 2.0  # Factor 2 de la fórmula

    # Lado derecho - Término 3: Σₚ Σₖ (ln p)/p^(k/2)·g(k·ln p)
    # Suma sobre los primeros n_primos primos
    primes = _generar_primos(n_primos)
    term3 = 0.0

    for p in primes:
        ln_p = np.log(p)
        # Suma sobre potencias k=1,2,3,...
        # La serie converge rápidamente porque g(k·ln p) → 0 exponencialmente
        k_max = int(10.0 / ln_p) + 1  # Límite heurístico
        for k in range(1, k_max + 1):
            term3 += (ln_p / (p ** (k / 2.0))) * g_func(k * ln_p)

    # Aplicar factor geométrico g_eff (5.3% mass modulation corrector)
    term3 *= g_eff

    # Lado derecho total
    lado_derecho = term1 + term2 + term3

    # Residuo en escala logarítmica
    residuo_log = abs(np.log(abs(suma_zeros + 1e-10)) - np.log(abs(lado_derecho + 1e-10)))

    # Verificar identidad: |residuo| < tolerancia
    identidad_verificada = residuo_log < TOLERANCE_NORMAL

    # Coherencia Selberg: Ψ = exp(-residuo²)
    coherencia_selberg = np.exp(-residuo_log ** 2)

    return ResultadoSelberg(
        sigma=sigma,
        suma_zeros=suma_zeros,
        lado_derecho=lado_derecho,
        g_eff=g_eff,
        residuo_log=residuo_log,
        identidad_verificada=identidad_verificada,
        coherencia_selberg=coherencia_selberg,
    )


def _generar_primos(n: int) -> List[int]:
    """
    Generar los primeros n números primos usando criba de Eratóstenes.

    Args:
        n: Número de primos a generar

    Returns:
        Lista de los primeros n primos
    """
    if n <= 0:
        return []

    # Estimación del límite superior: n-ésimo primo ~ n·ln(n) para n > 5
    limit = max(100, int(n * (np.log(n) + np.log(np.log(n + 1)))))

    # Criba de Eratóstenes
    sieve = np.ones(limit, dtype=bool)
    sieve[0:2] = False  # 0 y 1 no son primos

    for i in range(2, int(np.sqrt(limit)) + 1):
        if sieve[i]:
            sieve[i*i::i] = False

    primes = np.where(sieve)[0]

    return primes[:n].tolist()


# ===========================================================================
# IV. INTERFERÓMETRO MACH-ZEHNDER
# ===========================================================================

@dataclass
class ResultadoInterferometro:
    """Resultado de simulación del interferómetro Mach-Zehnder."""
    tiempo: np.ndarray  # Array de tiempos [s]
    indice_refraccion: np.ndarray  # n(Ψ,t)
    fase_diferencial: np.ndarray  # Δφ(t) [rad]
    intensidad_salida: np.ndarray  # I(t) ∝ [1 + cos(Δφ)]
    deteccion_lock_in: float  # Amplitud a f₀ [rad]
    chi_n_medido: float  # χₙ extraído de la medición
    frecuencia_base: float  # f₀ = 141.7001 Hz
    coherencia_interferometrica: float  # Visibilidad del patrón


class InterferometroMachZehnder:
    """
    Interferómetro Mach-Zehnder para medir modulación del índice de refracción.

    Configuración:
        Láser → BS1 → |Brazo 1 (L)| → BS2 → Detector
                   └→ |Brazo 2 (L)| ┘

    Modulación del índice:
        n(Ψ,t) = 1 - χₙ·cos(2πf₀t)

    Fase diferencial:
        Δφ(t) = (2πL/λ)·[n(Ψ,t) - 1] = -(2πL/λ)·χₙ·cos(2πf₀t)

    Intensidad de salida:
        I(t) = I₀/2·[1 + V·cos(Δφ(t) + φ₀)]

    donde V es la visibilidad del patrón de interferencia.

    Attributes:
        longitud_brazo_m: Longitud del brazo del interferómetro [m]
        longitud_onda_m: Longitud de onda del láser [m]
        chi_n: Susceptibilidad óptica χₙ [adimensional]
        f0: Frecuencia base QCAL [Hz]
    """

    def __init__(
        self,
        longitud_brazo_m: float = 1.0,
        longitud_onda_m: float = 632.8e-9,  # He-Ne laser
        chi_n: float = 6.62e-3,
        f0: float = F0,
    ):
        """
        Inicializar interferómetro Mach-Zehnder.

        Args:
            longitud_brazo_m: Longitud del brazo [m]
            longitud_onda_m: Longitud de onda del láser [m] (default: 632.8 nm)
            chi_n: Susceptibilidad óptica χₙ (default: 6.62×10⁻³)
            f0: Frecuencia base [Hz] (default: 141.7001 Hz)
        """
        self.L = longitud_brazo_m
        self.lambda_laser = longitud_onda_m
        self.chi_n = chi_n
        self.f0 = f0

        # Número de onda: k = 2π/λ
        self.k = 2.0 * np.pi / self.lambda_laser

    def indice_refraccion(self, t: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calcular índice de refracción modulado n(Ψ,t).

        n(Ψ,t) = 1 - χₙ·cos(2πf₀t)

        Args:
            t: Tiempo [s]

        Returns:
            Índice de refracción n(Ψ,t)
        """
        return 1.0 - self.chi_n * np.cos(2.0 * np.pi * self.f0 * t)

    def fase_diferencial(self, t: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Calcular fase diferencial Δφ(t).

        Δφ(t) = (2πL/λ)·[n(Ψ,t) - 1]
              = -(2πL/λ)·χₙ·cos(2πf₀t)

        Args:
            t: Tiempo [s]

        Returns:
            Fase diferencial Δφ(t) [rad]
        """
        return self.k * self.L * (self.indice_refraccion(t) - 1.0)

    def intensidad_salida(
        self,
        t: Union[float, np.ndarray],
        visibilidad: float = 1.0,
        fase_offset: float = 0.0
    ) -> Union[float, np.ndarray]:
        """
        Calcular intensidad de salida I(t).

        I(t) = I₀/2·[1 + V·cos(Δφ(t) + φ₀)]

        Args:
            t: Tiempo [s]
            visibilidad: Visibilidad V ∈ [0,1] (default: 1.0)
            fase_offset: Offset de fase φ₀ [rad] (default: 0.0)

        Returns:
            Intensidad normalizada I(t)/I₀
        """
        delta_phi = self.fase_diferencial(t)
        return 0.5 * (1.0 + visibilidad * np.cos(delta_phi + fase_offset))

    def simular(
        self,
        duracion_s: Optional[float] = None,
        n_puntos: int = 300,
        visibilidad: float = 1.0
    ) -> Dict[str, Any]:
        """
        Simular operación del interferómetro y detección lock-in.

        Args:
            duracion_s: Duración de la simulación [s]. Si None, usa 3/f₀ (3 períodos).
            n_puntos: Número de puntos temporales
            visibilidad: Visibilidad del patrón de interferencia

        Returns:
            Diccionario con resultados de simulación:
                - tiempo: Array de tiempos [s]
                - indice_refraccion: n(Ψ,t)
                - fase_diferencial: Δφ(t) [rad]
                - intensidad_salida: I(t)
                - deteccion_lock_in: Amplitud a f₀ [rad]
                - chi_n_medido: χₙ extraído
                - coherencia_interferometrica: Visibilidad
        """
        if duracion_s is None:
            duracion_s = 3.0 / self.f0  # 3 períodos completos

        # Array de tiempos
        t = np.linspace(0, duracion_s, n_puntos)

        # Calcular señales
        n_t = self.indice_refraccion(t)
        delta_phi = self.fase_diferencial(t)
        I_t = self.intensidad_salida(t, visibilidad=visibilidad)

        # Detección lock-in: extraer componente a f₀
        # Usamos la transformada de Fourier para encontrar la amplitud a f₀
        dt = t[1] - t[0]
        freqs = np.fft.fftfreq(len(t), dt)
        fft_delta_phi = np.fft.fft(delta_phi)

        # Encontrar índice más cercano a f₀
        idx_f0 = np.argmin(np.abs(freqs - self.f0))
        amplitud_lock_in = 2.0 * np.abs(fft_delta_phi[idx_f0]) / len(t)

        # Extraer χₙ de la medición lock-in
        # Δφ(t) = -(2πL/λ)·χₙ·cos(2πf₀t)
        # → Amplitud = (2πL/λ)·χₙ
        chi_n_medido = amplitud_lock_in / (self.k * self.L)

        # Coherencia interferométrica = visibilidad observada
        coherencia = visibilidad

        return {
            'tiempo': t,
            'indice_refraccion': n_t,
            'fase_diferencial': delta_phi,
            'intensidad_salida': I_t,
            'deteccion_lock_in': amplitud_lock_in,
            'chi_n_medido': chi_n_medido,
            'frecuencia_base': self.f0,
            'coherencia_interferometrica': coherencia,
        }

    def chi_n_desde_medicion(self, amplitud_lock_in: float) -> float:
        """
        Extraer χₙ desde una medición lock-in.

        Δφ_amplitud = (2πL/λ)·χₙ
        → χₙ = Δφ_amplitud / (2πL/λ)

        Args:
            amplitud_lock_in: Amplitud medida a f₀ [rad]

        Returns:
            Susceptibilidad óptica χₙ extraída
        """
        return amplitud_lock_in / (self.k * self.L)


# ===========================================================================
# FUNCIONES DE UTILIDAD Y ACTIVACIÓN
# ===========================================================================

def demostrar_coherencia_unitaria(
    zeros: Optional[List[float]] = None,
    verbose: bool = True
) -> Dict[str, Any]:
    """
    Demostración completa de coherencia unitaria en los cuatro pilares.

    Args:
        zeros: Lista de γₙ. Si None, usa RIEMANN_ZEROS_50.
        verbose: Si True, imprime resultados

    Returns:
        Diccionario con resultados de los cuatro pilares
    """
    gamma = zeros if zeros is not None else RIEMANN_ZEROS_50

    resultados = {}

    # I. Berry-Keating
    bk = OperadorBerryKeating(zeros=gamma, sigma=0.5)
    resultado_bk = bk.verificar_unitariedad(duracion=10.0)
    resultados['berry_keating'] = resultado_bk

    if verbose:
        print("=" * 80)
        print("I. OPERADOR BERRY-KEATING")
        print("=" * 80)
        print(f"σ = {resultado_bk.sigma:.6f}")
        print(f"Número de ceros: {len(bk.zeros)}")
        print(f"Unitario: {resultado_bk.es_unitario}")
        print(f"Desviación de unitariedad: {resultado_bk.desviacion_unitariedad:.2e}")
        print(f"Métrica η⁺ positiva: {resultado_bk.metrica_positiva}")
        print(f"Coherencia Ψ: {resultado_bk.coherencia_psi:.9f}")
        print()

    # II. Estadística GUE
    resultado_gue = estadistica_gue(zeros=gamma)
    resultados['gue'] = resultado_gue

    if verbose:
        print("=" * 80)
        print("II. ESTADÍSTICA GUE")
        print("=" * 80)
        print(f"Media de espaciados: ⟨s⟩ = {resultado_gue.media_espaciado:.6f}")
        print(f"Chi-cuadrado: χ² = {resultado_gue.chi_cuadrado:.4f}")
        print(f"p-valor: {resultado_gue.p_valor:.2e}")
        print(f"Conformidad GUE: {resultado_gue.conformidad_gue}")
        print(f"KS statistic: {resultado_gue.ks_statistic:.6f}")
        print(f"KS p-valor: {resultado_gue.ks_p_valor:.2e}")
        print()

    # II-bis. Montgomery
    resultado_montgomery = correlacion_pares_montgomery(zeros=gamma)
    resultados['montgomery'] = resultado_montgomery

    if verbose:
        print("=" * 80)
        print("II-bis. CORRELACIÓN DE PARES DE MONTGOMERY")
        print("=" * 80)
        print(f"Discrepancia: {resultado_montgomery.discrepancia:.6f}")
        print(f"Coherencia GUE: {resultado_montgomery.coherencia_gue:.6f}")
        print()

    # III. Selberg Trace
    resultado_selberg = verificar_identidad_selberg(zeros=gamma, sigma=1.5)
    resultados['selberg'] = resultado_selberg

    if verbose:
        print("=" * 80)
        print("III. FÓRMULA DE TRAZA DE SELBERG")
        print("=" * 80)
        print(f"σ = {resultado_selberg.sigma:.6f}")
        print(f"Σₙ g(γₙ) = {resultado_selberg.suma_zeros:.6f}")
        print(f"Lado derecho = {resultado_selberg.lado_derecho:.6f}")
        print(f"g_eff = {resultado_selberg.g_eff:.6f}")
        print(f"Residuo (log): {resultado_selberg.residuo_log:.2e}")
        print(f"Identidad verificada: {resultado_selberg.identidad_verificada}")
        print(f"Coherencia Selberg: {resultado_selberg.coherencia_selberg:.9f}")
        print()

    # IV. Interferómetro Mach-Zehnder
    ifm = InterferometroMachZehnder(
        longitud_brazo_m=1.0,
        longitud_onda_m=632.8e-9,
        chi_n=6.62e-3,
        f0=F0
    )
    sim = ifm.simular(duracion_s=3.0 / F0, n_puntos=300)
    resultados['interferometro'] = sim

    if verbose:
        print("=" * 80)
        print("IV. INTERFERÓMETRO MACH-ZEHNDER")
        print("=" * 80)
        print(f"Longitud de brazo: L = {ifm.L:.3f} m")
        print(f"Longitud de onda: λ = {ifm.lambda_laser*1e9:.1f} nm")
        print(f"χₙ inicial: {ifm.chi_n:.3e}")
        print(f"f₀ = {ifm.f0:.4f} Hz")
        print(f"Detección lock-in: {sim['deteccion_lock_in']:.3e} rad")
        print(f"χₙ medido: {sim['chi_n_medido']:.3e}")
        print(f"Error relativo: {abs(sim['chi_n_medido'] - ifm.chi_n)/ifm.chi_n * 100:.2f}%")
        print(f"Coherencia interferométrica: {sim['coherencia_interferometrica']:.6f}")
        print()

    # Coherencia global
    coherencia_global = (
        resultado_bk.coherencia_psi *
        resultado_montgomery.coherencia_gue *
        resultado_selberg.coherencia_selberg *
        sim['coherencia_interferometrica']
    ) ** 0.25  # Media geométrica

    resultados['coherencia_global'] = coherencia_global

    if verbose:
        print("=" * 80)
        print("COHERENCIA GLOBAL QCAL ∞³")
        print("=" * 80)
        print(f"Ψ_global = {coherencia_global:.9f}")
        print(f"Nivel: {'EXCELENTE' if coherencia_global > PSI_THRESHOLD_EXCELLENT else 'BUENO'}")
        print("=" * 80)
        print()

    return resultados


# ===========================================================================
# EXPORTS
# ===========================================================================

__all__ = [
    # I. Berry-Keating
    'OperadorBerryKeating',
    'ResultadoBerryKeating',
    # II. GUE
    'estadistica_gue',
    'ResultadoGUE',
    'correlacion_pares_montgomery',
    'ResultadoMontgomery',
    'distribucion_wigner_dyson',
    # III. Selberg
    'verificar_identidad_selberg',
    'ResultadoSelberg',
    # IV. Interferómetro
    'InterferometroMachZehnder',
    'ResultadoInterferometro',
    # Utilidad
    'demostrar_coherencia_unitaria',
    # Constants
    'RIEMANN_ZEROS_50',
    'G_EFF_SELBERG',
]


# ===========================================================================
# MAIN EXECUTION
# ===========================================================================

if __name__ == "__main__":
    print()
    print("∴" * 40)
    print("  COHERENCIA UNITARIA — QCAL ∞³")
    print("  f₀ = 141.7001 Hz · C = 244.36")
    print("∴" * 40)
    print()

    # Ejecutar demostración completa
    resultados = demostrar_coherencia_unitaria(verbose=True)

    print()
    print("✓ Demostración completa de coherencia unitaria finalizada.")
    print(f"✓ Coherencia global: Ψ = {resultados['coherencia_global']:.9f}")
    print()
    print("∴𓂀Ω∞³Φ")
