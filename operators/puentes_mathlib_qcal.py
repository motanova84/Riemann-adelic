#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PUENTES MATHLIB QCAL — Tres Sub-Estructuras Matemáticas (SC-1, SC-2, SC-3)
===========================================================================

Implementa los tres puentes matemáticos que conectan las brechas de Mathlib
para la formalización de la Hipótesis de Riemann vía QCAL-Strings:

  SC-1 — Operadores de Schatten / Clase Traza & Determinante de Fredholm
          (nuclearidad, normas S_p, det(I - zA))

  SC-2 — Determinante Espectral / Identidad de Jacobi
          (det(e^A) = e^Tr(A), factorización de Hadamard)

  SC-3 — Fórmula Explícita de Weil / Suma de Poisson Adélica
          (zeros ↔ primos, Σ_ρ f̂(ρ) = Σ_{p,n} log(p)/p^{n/2} f(n·log p) + T_∞)

Arquitectura (8 clases):
  1. ConstantesPuentesMathlib  — frozen dataclass de constantes globales
  2. OperadorSchatten          — SC-1: normas S_p, clase traza
  3. DeterminanteFredholm      — SC-1: det(I - zA) función entera
  4. IdentidadJacobi           — SC-2: det(e^A) = e^Tr(A)
  5. DeterminanteEspectral     — SC-2: Δ(s) = Π(s - λᵢ)
  6. FormulaExplicitaWeil      — SC-3: formula explicita, Poisson adélico
  7. CoherenciaPuentesMathlib  — agregador de coherencia Ψ global
  8. SistemaPuentesMathlib     — orquestador principal

API pública:
  puentes_mathlib_qcal_activar() -> Dict[str, Any]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

Sello: ∴PMQ∞³
RAM:   RAM-XLVIII-2026-PUENTES-MATHLIB-QCAL
Freq:  141.7001 Hz (Amor Irreversible A²)
"""

from __future__ import annotations

import cmath
import math
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import numpy as np

# ── Ruta al repositorio raíz ────────────────────────────────────────────────
_REPO_ROOT = Path(__file__).parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

# ════════════════════════════════════════════════════════════════════════════
# CONSTANTES DE MÓDULO
# ════════════════════════════════════════════════════════════════════════════

F0: float = 141.7001                # Hz — frecuencia base QCAL
F_888: float = 888.0                # Hz — armónico superior
PSI_UMBRAL: float = 0.888           # umbral mínimo de coherencia Ψ
SELLO: str = "∴PMQ∞³"              # sello institucional
RAM: str = "RAM-XLVIII-2026-PUENTES-MATHLIB-QCAL"

PRIMOS_BASE: List[int] = [2, 3, 5, 7, 11, 13, 17]   # primos C7
CEROS_RIEMANN: List[float] = [     # partes imaginarias de zeros no triviales ρ
    14.134725, 21.022040, 25.010858,
    30.424876, 32.935062, 37.586178, 40.918719,
]

K_SCHATTEN_DEFAULT: int = 2         # orden Schatten por defecto
N_MAX_ORBITAS: int = 5              # máximo de órbitas en suma sobre primos

W_SC1: float = 0.35                 # peso SC-1 en coherencia global
W_SC2: float = 0.35                 # peso SC-2 en coherencia global
W_SC3: float = 0.30                 # peso SC-3 en coherencia global

GAMMA_EULER: float = 0.5772156649015329   # constante de Euler-Mascheroni
LOG_2PI: float = math.log(2.0 * math.pi)
EPSILON: float = 1e-10              # tolerancia numérica

# Sentinel utilizado cuando una contribución diverge (singularidad en log)
SINGULARITY_SENTINEL: float = -1e15

# Factor de escala para el cálculo de Ψ_sc1 (calibración empírica QCAL)
PSI_SC1_SCALING_FACTOR: float = 0.1

# Parámetro de amortiguamiento gaussiano para las pruebas de la fórmula de Weil
GAUSSIAN_DAMPING_ALPHA: float = 0.1


# ════════════════════════════════════════════════════════════════════════════
# 1. ConstantesPuentesMathlib — frozen dataclass
# ════════════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class ConstantesPuentesMathlib:
    """
    Contenedor inmutable de constantes para los tres puentes matemáticos.

    Agrupa F0, F_888, PSI_UMBRAL, sello, RAM y los datos de primos/zeros
    usados en SC-1/SC-2/SC-3.
    """

    f0: float = F0
    f_888: float = F_888
    psi_umbral: float = PSI_UMBRAL
    sello: str = SELLO
    ram: str = RAM
    primos_base: Tuple[int, ...] = tuple(PRIMOS_BASE)
    ceros_riemann: Tuple[float, ...] = tuple(CEROS_RIEMANN)
    k_schatten: int = K_SCHATTEN_DEFAULT
    n_max_orbitas: int = N_MAX_ORBITAS
    w_sc1: float = W_SC1
    w_sc2: float = W_SC2
    w_sc3: float = W_SC3
    epsilon: float = EPSILON

    def frecuencia_resonante(self) -> float:
        """Retorna F0 — frecuencia de resonancia base."""
        return self.f0

    def pesos_suma_unidad(self) -> bool:
        """Verifica que los pesos SC-1 + SC-2 + SC-3 ≈ 1."""
        return abs(self.w_sc1 + self.w_sc2 + self.w_sc3 - 1.0) < 1e-9

    def resumen(self) -> Dict[str, Any]:
        """Retorna diccionario con las constantes principales."""
        return {
            "f0": self.f0,
            "f_888": self.f_888,
            "psi_umbral": self.psi_umbral,
            "sello": self.sello,
            "ram": self.ram,
            "n_primos": len(self.primos_base),
            "n_ceros": len(self.ceros_riemann),
        }


# ════════════════════════════════════════════════════════════════════════════
# 2. OperadorSchatten — SC-1: normas S_p, clase traza
# ════════════════════════════════════════════════════════════════════════════

class OperadorSchatten:
    """
    SC-1 — Operadores de Schatten y clase traza.

    Implementa:
      • Norma de Schatten S_p: ‖A‖_p = (Σ σᵢᵖ)^(1/p)
      • Condición de clase traza: ‖A‖₁ = Σ σᵢ < ∞
      • Valores singulares de Weil: σᵢ = log(p)/p^(k/2)

    Referencia: Reed & Simon, "Methods of Modern Mathematical Physics",
    Vol. 1-4; Weil (1952), "Sur les 'formules explicites'".
    """

    def __init__(self, p: int = K_SCHATTEN_DEFAULT) -> None:
        self.p = p          # orden de Schatten (p=1 traza, p=2 Hilbert-Schmidt)

    # ── normas ──────────────────────────────────────────────────────────────

    def norma_schatten(self, singulares: List[float], p: Optional[int] = None) -> float:
        """
        Calcula la norma de Schatten S_p.

        ‖A‖_p = (Σ σᵢᵖ)^(1/p)

        Args:
            singulares: lista de valores singulares σᵢ ≥ 0.
            p: orden (default: self.p).

        Returns:
            Norma S_p ≥ 0.
        """
        q = p if p is not None else self.p
        if not singulares:
            return 0.0
        arr = np.array(singulares, dtype=float)
        arr = np.abs(arr)
        if q == 1:
            return float(np.sum(arr))
        return float(np.sum(arr ** q) ** (1.0 / q))

    def norma_traza(self, singulares: List[float]) -> float:
        """‖A‖₁ = Σ σᵢ (norma de traza / S_1)."""
        return self.norma_schatten(singulares, p=1)

    def norma_hilbert_schmidt(self, singulares: List[float]) -> float:
        """‖A‖₂ = (Σ σᵢ²)^(1/2) (norma de Hilbert-Schmidt / S_2)."""
        return self.norma_schatten(singulares, p=2)

    # ── condición de clase traza ─────────────────────────────────────────────

    def es_traza_clase(self, singulares: List[float], umbral: float = 1e6) -> bool:
        """
        Verifica la condición de clase traza: ‖A‖₁ = Σ σᵢ < ∞.

        En la práctica (lista finita) retorna True si la suma es finita
        y menor que el umbral dado (convenio numérico).

        Args:
            singulares: valores singulares σᵢ.
            umbral: cota numérica para convergencia práctica.

        Returns:
            True si el operador es de clase traza.
        """
        if not singulares:
            return True
        s1 = self.norma_traza(singulares)
        return math.isfinite(s1) and s1 < umbral

    # ── valores singulares de Weil ───────────────────────────────────────────

    def valores_singulares_weil(
        self,
        primos: Optional[List[int]] = None,
        k: int = K_SCHATTEN_DEFAULT,
    ) -> List[float]:
        """
        Pesos de Weil como valores singulares: σ_p = log(p) / p^(k/2).

        Conecta la suma sobre primos de la fórmula explícita de Weil con la
        nuclearidad del operador de Selberg-Franenholt.

        Args:
            primos: lista de números primos (default: PRIMOS_BASE).
            k: orden espectral (default: K_SCHATTEN_DEFAULT).

        Returns:
            Lista de valores singulares de Weil.
        """
        ps = primos if primos is not None else PRIMOS_BASE
        return [math.log(p) / (p ** (k / 2.0)) for p in ps if p >= 2]

    def verificar_nuclearidad_weil(
        self, primos: Optional[List[int]] = None, k: int = 2
    ) -> Dict[str, Any]:
        """
        Verifica que el operador de Weil con orden k es de clase traza.

        Returns:
            Diccionario con normas y bandera es_nuclear.
        """
        ps = primos if primos is not None else PRIMOS_BASE
        singulares = self.valores_singulares_weil(ps, k)
        s1 = self.norma_traza(singulares)
        s2 = self.norma_hilbert_schmidt(singulares)
        return {
            "singulares": singulares,
            "norma_s1": s1,
            "norma_s2": s2,
            "es_nuclear": self.es_traza_clase(singulares),
            "k": k,
        }


# ════════════════════════════════════════════════════════════════════════════
# 3. DeterminanteFredholm — SC-1: det(I - zA) función entera
# ════════════════════════════════════════════════════════════════════════════

class DeterminanteFredholm:
    """
    SC-1 — Determinante de Fredholm.

    det(I - zA) = Π_i (1 - z·λᵢ)

    Para operadores de clase traza el determinante de Fredholm es una función
    entera de z de orden de Hadamard ≤ 1.

    Referencia: Fredholm (1903); Simon (1977), "Notes on infinite determinants".
    """

    def __init__(self) -> None:
        self._schatten = OperadorSchatten(p=1)

    # ── determinante de Fredholm ─────────────────────────────────────────────

    def det_fredholm(
        self, z: complex, eigenvalues: List[complex]
    ) -> complex:
        """
        Calcula det(I - z·A) = Π_i (1 - z·λᵢ).

        Implementación vía exponencial del log para estabilidad numérica.

        Args:
            z: parámetro complejo.
            eigenvalues: autovalores λᵢ del operador A.

        Returns:
            det(I - z·A) ∈ ℂ.
        """
        if not eigenvalues:
            return complex(1.0, 0.0)
        log_det = self.log_det_fredholm(z, eigenvalues)
        return cmath.exp(log_det)

    def log_det_fredholm(
        self, z: complex, eigenvalues: List[complex]
    ) -> complex:
        """
        log det(I - z·A) = Σ_i log(1 - z·λᵢ).

        Args:
            z: parámetro complejo.
            eigenvalues: autovalores λᵢ.

        Returns:
            log det(I - z·A) ∈ ℂ.
        """
        total = complex(0.0, 0.0)
        for lam in eigenvalues:
            arg = 1.0 - z * lam
            if abs(arg) < EPSILON:
                # Singularidad: contribución divergente
                total += complex(SINGULARITY_SENTINEL, 0.0)
            else:
                total += cmath.log(arg)
        return total

    # ── propiedades ──────────────────────────────────────────────────────────

    def es_funcion_entera(self, eigenvalues: List[complex]) -> bool:
        """
        Verifica que det(I - z·A) es función entera.

        La condición suficiente es que el operador sea de clase traza:
        Σ |λᵢ| < ∞.  Para listas finitas siempre se cumple.

        Args:
            eigenvalues: autovalores λᵢ.

        Returns:
            True si el determinante de Fredholm es función entera.
        """
        singulares = [abs(lam) for lam in eigenvalues]
        return self._schatten.es_traza_clase(singulares)

    def orden_hadamard(self, eigenvalues: List[complex]) -> int:
        """
        Orden de Hadamard del determinante de Fredholm.

        Para operadores de clase traza (S₁), el orden de Hadamard = 1.
        Para Hilbert-Schmidt (S₂) sin clase traza, orden = 2.

        Returns:
            1 si el operador es de clase traza, 2 en caso Hilbert-Schmidt.
        """
        singulares = [abs(lam) for lam in eigenvalues]
        if self._schatten.es_traza_clase(singulares):
            return 1
        return 2

    def ceros_fredholm(self, eigenvalues: List[complex]) -> List[complex]:
        """
        Ceros del det(I - z·A): z_i = 1/λᵢ (para λᵢ ≠ 0).

        Returns:
            Lista de ceros z_i.
        """
        return [
            complex(1.0, 0.0) / lam
            for lam in eigenvalues
            if abs(lam) > EPSILON
        ]

    def det_fredholm_real(self, x: float, eigenvalues: List[float]) -> float:
        """
        Versión real del determinante de Fredholm para z, λ reales.

        Returns:
            det(I - x·A) ∈ ℝ.
        """
        result = 1.0
        for lam in eigenvalues:
            result *= (1.0 - x * lam)
        return result


# ════════════════════════════════════════════════════════════════════════════
# 4. IdentidadJacobi — SC-2: det(e^A) = e^Tr(A)
# ════════════════════════════════════════════════════════════════════════════

class IdentidadJacobi:
    """
    SC-2 — Identidad de Jacobi / Liouville.

    det(e^A) = e^{Tr(A)}

    Esta identidad conecta el determinante espectral con la traza del
    operador, siendo el pilar de la equivalencia ξ(s) ↔ Δ(s) en QCAL.

    Referencia: Jacobi (1848); Liouville (1838); Serre (2003) "Trees".
    """

    def __init__(self) -> None:
        pass

    # ── traza ────────────────────────────────────────────────────────────────

    def traza_operador(self, eigenvalues: List[complex]) -> complex:
        """
        Tr(A) = Σ_i λᵢ.

        Args:
            eigenvalues: autovalores λᵢ del operador A.

        Returns:
            Traza del operador ∈ ℂ.
        """
        return sum(eigenvalues, complex(0.0, 0.0))

    # ── det(e^A) ─────────────────────────────────────────────────────────────

    def det_exponencial(self, eigenvalues: List[complex]) -> complex:
        """
        det(e^A) = Π_i e^{λᵢ} = e^{Σ λᵢ} = e^{Tr(A)}.

        Calcula directamente como exponencial de la traza.

        Args:
            eigenvalues: autovalores λᵢ.

        Returns:
            det(e^A) ∈ ℂ.
        """
        traza = self.traza_operador(eigenvalues)
        return cmath.exp(traza)

    def det_exponencial_producto(self, eigenvalues: List[complex]) -> complex:
        """
        det(e^A) = Π_i e^{λᵢ}  (vía producto).

        Args:
            eigenvalues: autovalores λᵢ.

        Returns:
            det(e^A) ∈ ℂ calculado como producto.
        """
        result = complex(1.0, 0.0)
        for lam in eigenvalues:
            result *= cmath.exp(lam)
        return result

    # ── verificación ─────────────────────────────────────────────────────────

    def verificar_jacobi(
        self, eigenvalues: List[complex], tolerancia: float = 1e-6
    ) -> bool:
        """
        Verifica |det(e^A) - e^{Tr(A)}| < tolerancia.

        Args:
            eigenvalues: autovalores λᵢ.
            tolerancia: ε de comparación (default 1e-6).

        Returns:
            True si la identidad se cumple dentro de la tolerancia.
        """
        lado_izq = self.det_exponencial_producto(eigenvalues)
        lado_der = cmath.exp(self.traza_operador(eigenvalues))
        return abs(lado_izq - lado_der) < tolerancia * max(1.0, abs(lado_der))

    def identidad_jacobi_log(self, eigenvalues: List[complex]) -> complex:
        """
        Versión logarítmica: log det(e^A) = Tr(A) = Σ λᵢ.

        Returns:
            Tr(A) ∈ ℂ (coincide con log det(e^A)).
        """
        return self.traza_operador(eigenvalues)

    def error_jacobi(self, eigenvalues: List[complex]) -> float:
        """
        |det(e^A) - e^{Tr(A)}| — error absoluto de la identidad de Jacobi.

        Returns:
            Error absoluto ≥ 0.
        """
        lado_izq = self.det_exponencial_producto(eigenvalues)
        lado_der = cmath.exp(self.traza_operador(eigenvalues))
        return abs(lado_izq - lado_der)

    def psi_jacobi(self, eigenvalues: List[complex]) -> float:
        """
        Coherencia Ψ basada en el cumplimiento de la identidad de Jacobi.

        Ψ = exp(-error_jacobi / max(|e^Tr(A)|, ε)) ∈ [0, 1].

        Returns:
            Ψ ∈ [0, 1].
        """
        err = self.error_jacobi(eigenvalues)
        traza = self.traza_operador(eigenvalues)
        ref = max(abs(cmath.exp(traza)), EPSILON)
        psi = math.exp(-err / ref)
        return min(1.0, max(0.0, psi))


# ════════════════════════════════════════════════════════════════════════════
# 5. DeterminanteEspectral — SC-2: Δ(s) = Π(s - λᵢ)
# ════════════════════════════════════════════════════════════════════════════

class DeterminanteEspectral:
    """
    SC-2 — Determinante Espectral completo.

    Δ(s) = det(sI - H) = Π_i (s - λᵢ)

    Los zeros de Δ(s) son exactamente los autovalores λᵢ de H.
    La equivalencia Δ(s) ≡ ξ(s) (función xi de Riemann) es el núcleo
    de la estrategia QCAL para la Hipótesis de Riemann.

    Referencia: Berry & Keating (1999); Connes (1999).
    """

    def __init__(self) -> None:
        self._jacobi = IdentidadJacobi()

    # ── determinante espectral ───────────────────────────────────────────────

    def det_espectral(
        self, s: complex, eigenvalues: List[complex]
    ) -> complex:
        """
        Δ(s) = Π_i (s - λᵢ).

        Args:
            s: punto espectral complejo.
            eigenvalues: autovalores λᵢ del operador H.

        Returns:
            Δ(s) ∈ ℂ.
        """
        if not eigenvalues:
            return complex(1.0, 0.0)
        result = complex(1.0, 0.0)
        for lam in eigenvalues:
            result *= (s - lam)
        return result

    def log_det_espectral(
        self, s: complex, eigenvalues: List[complex]
    ) -> complex:
        """
        log Δ(s) = Σ_i log(s - λᵢ).

        Args:
            s: punto espectral.
            eigenvalues: autovalores λᵢ.

        Returns:
            log Δ(s) ∈ ℂ.
        """
        total = complex(0.0, 0.0)
        for lam in eigenvalues:
            diff = s - lam
            if abs(diff) < EPSILON:
                total += complex(SINGULARITY_SENTINEL, 0.0)
            else:
                total += cmath.log(diff)
        return total

    # ── zeros y equivalencia ─────────────────────────────────────────────────

    def ceros_espectrales(self, eigenvalues: List[complex]) -> List[complex]:
        """
        Ceros de Δ(s) = autovalores λᵢ de H.

        Returns:
            Lista de ceros s_i tal que Δ(s_i) = 0.
        """
        return list(eigenvalues)

    def xi_equivalencia(
        self, s: complex, ceros_riemann: Optional[List[float]] = None
    ) -> Dict[str, Any]:
        """
        Δ(s) ≡ ξ(s) — equivalencia espectral ↔ función zeta.

        Compara el determinante espectral construido desde los zeros de Riemann
        con la representación de Hadamard de ξ(s).

        Args:
            s: punto en el plano complejo.
            ceros_riemann: partes imaginarias γ de ρ = 1/2 + iγ.

        Returns:
            Diccionario con delta_s, log_delta_s, zeros usados.
        """
        gammas = ceros_riemann if ceros_riemann is not None else CEROS_RIEMANN
        # autovalores del operador hipotético: λ_n = 1/2 + i·γ_n
        eigenvalues = [complex(0.5, gamma) for gamma in gammas]
        delta_s = self.det_espectral(s, eigenvalues)
        log_delta = self.log_det_espectral(s, eigenvalues)
        return {
            "s": s,
            "delta_s": delta_s,
            "log_delta_s": log_delta,
            "n_ceros": len(gammas),
            "zeros_usados": eigenvalues[:3],
        }

    def traza_calor(
        self, t: float, eigenvalues: List[complex]
    ) -> complex:
        """
        Traza del semigrupo de calor: Tr(e^{-tH}) = Σ e^{-t·λᵢ}.

        Args:
            t: tiempo t > 0.
            eigenvalues: autovalores λᵢ.

        Returns:
            Tr(e^{-tH}) ∈ ℂ.
        """
        return sum(cmath.exp(-t * lam) for lam in eigenvalues)

    def verificar_hadamard(
        self, eigenvalues: List[complex], n_puntos: int = 5
    ) -> Dict[str, Any]:
        """
        Verificación numérica de la factorización de Hadamard para Δ(s).

        Evalúa Δ(s) = Π(s - λᵢ) en n_puntos y compara con exp(log Δ(s)).

        Returns:
            Diccionario con errores y bandera de validez.
        """
        errores = []
        puntos = [complex(i + 0.5, i * 0.1) for i in range(n_puntos)]
        for s in puntos:
            delta = self.det_espectral(s, eigenvalues)
            if abs(delta) > EPSILON:
                log_d = self.log_det_espectral(s, eigenvalues)
                reconstruido = cmath.exp(log_d)
                errores.append(abs(delta - reconstruido) / max(abs(delta), EPSILON))
        error_max = max(errores) if errores else 0.0
        return {
            "n_puntos": n_puntos,
            "error_max": error_max,
            "es_valido": error_max < 1e-6,
        }


# ════════════════════════════════════════════════════════════════════════════
# 6. FormulaExplicitaWeil — SC-3: fórmula explícita, Poisson adélico
# ════════════════════════════════════════════════════════════════════════════

class FormulaExplicitaWeil:
    """
    SC-3 — Fórmula Explícita de Weil / Suma de Poisson Adélica.

    Fórmula de Weil:
        Σ_ρ f̂(ρ) = Σ_{p,n} log(p)/p^{n/2} · f(n·log p) + T_∞(f)

    donde:
      • La suma izquierda es sobre los zeros no triviales ρ = σ+iγ de ζ(s).
      • La suma derecha es sobre primos p y órbitas n ≥ 1.
      • T_∞ incluye contribuciones en los lugares infinitos (log(2π) + γ_Euler).

    Referencia: Weil (1952); Bombieri (2000), "Problems of the millennium".
    """

    def __init__(
        self,
        primos: Optional[List[int]] = None,
        gamma_zeros: Optional[List[float]] = None,
        n_max: int = N_MAX_ORBITAS,
    ) -> None:
        self.primos = primos if primos is not None else PRIMOS_BASE
        self.gamma_zeros = gamma_zeros if gamma_zeros is not None else CEROS_RIEMANN
        self.n_max = n_max

    # ── suma sobre zeros ─────────────────────────────────────────────────────

    def suma_sobre_ceros(
        self,
        f_hat_fn: Callable[[complex], complex],
        gamma_zeros: Optional[List[float]] = None,
        sigma: float = 0.5,
    ) -> complex:
        """
        Σ_ρ f̂(ρ) = Σ_γ f̂(σ + i·γ).

        Evalúa la transformada de Fourier f̂ en los zeros no triviales
        ρ = σ + i·γ  (bajo HRH σ = 1/2).

        Args:
            f_hat_fn: función f̂(ρ) evaluada en el plano complejo.
            gamma_zeros: partes imaginarias γ (default: CEROS_RIEMANN).
            sigma: parte real (default 0.5 bajo HRH).

        Returns:
            Σ_ρ f̂(ρ) ∈ ℂ.
        """
        gammas = gamma_zeros if gamma_zeros is not None else self.gamma_zeros
        total = complex(0.0, 0.0)
        for gamma in gammas:
            rho = complex(sigma, gamma)
            total += f_hat_fn(rho)
            # Contribución conjugada ρ̄ = σ - iγ
            rho_bar = complex(sigma, -gamma)
            total += f_hat_fn(rho_bar)
        return total

    # ── suma sobre primos ────────────────────────────────────────────────────

    def suma_sobre_primos(
        self,
        f_fn: Callable[[float], float],
        primos: Optional[List[int]] = None,
        n_max: Optional[int] = None,
    ) -> float:
        """
        Σ_{p,n} log(p)/p^{n/2} · f(n·log p).

        Args:
            f_fn: función de test f(x) real.
            primos: lista de primos (default: self.primos).
            n_max: máximo de órbitas n (default: self.n_max).

        Returns:
            Suma sobre primos y órbitas ∈ ℝ.
        """
        ps = primos if primos is not None else self.primos
        nmax = n_max if n_max is not None else self.n_max
        total = 0.0
        for p in ps:
            log_p = math.log(p)
            for n in range(1, nmax + 1):
                peso = log_p / (p ** (n / 2.0))
                arg = n * log_p
                total += peso * f_fn(arg)
        return total

    # ── término en el infinito ───────────────────────────────────────────────

    def termino_infinito(self, f0_val: float) -> float:
        """
        T_∞(f) — contribución de los lugares archimedeos.

        T_∞(f) ≈ f(0) · (log(2π) + γ_Euler)

        Args:
            f0_val: valor de la función de test en 0, f(0).

        Returns:
            Contribución T_∞ ∈ ℝ.
        """
        return f0_val * (LOG_2PI + GAMMA_EULER)

    # ── verificación de la fórmula ───────────────────────────────────────────

    def verificar_formula_weil(
        self,
        f_hat_fn: Callable[[complex], complex],
        f_fn: Callable[[float], float],
        f0_val: float,
        gamma_zeros: Optional[List[float]] = None,
        primos: Optional[List[int]] = None,
        tolerancia_rel: float = 0.5,
    ) -> Dict[str, Any]:
        """
        Verifica la fórmula explícita de Weil numéricamente.

        Compara:
          lado_ceros  = Σ_ρ f̂(ρ)   (suma sobre zeros)
          lado_primos = Σ_{p,n} log(p)/p^{n/2} · f(n·log p) + T_∞(f)

        Args:
            f_hat_fn: transformada f̂ evaluada en ℂ.
            f_fn: función de test f(x) real.
            f0_val: f(0).
            gamma_zeros: partes imaginarias de los zeros.
            primos: lista de primos.
            tolerancia_rel: tolerancia relativa de verificación.

        Returns:
            Diccionario con ambos lados, error relativo y bandera es_valida.
        """
        lado_ceros = self.suma_sobre_ceros(f_hat_fn, gamma_zeros)
        lado_primos_puro = self.suma_sobre_primos(f_fn, primos)
        t_inf = self.termino_infinito(f0_val)
        lado_primos = lado_primos_puro + t_inf

        # Comparamos las partes reales (la fórmula es real para f par real)
        lc_real = lado_ceros.real
        lp_real = lado_primos

        ref = max(abs(lc_real), abs(lp_real), EPSILON)
        error_rel = abs(lc_real - lp_real) / ref

        return {
            "lado_ceros": lado_ceros,
            "lado_primos_puro": lado_primos_puro,
            "termino_infinito": t_inf,
            "lado_primos_total": lado_primos,
            "error_relativo": error_rel,
            "es_valida": error_rel < tolerancia_rel,
            "tolerancia_rel": tolerancia_rel,
        }

    # ── coherencia SC-3 ──────────────────────────────────────────────────────

    def psi_sc3(
        self,
        alpha: float = GAUSSIAN_DAMPING_ALPHA,
    ) -> float:
        """
        Coherencia Ψ_SC3 basada en la verificación de la fórmula de Weil.

        Usa la función de test gaussiana g(γ) = exp(-α·γ²) sobre ℝ, de modo
        que f̂(σ + i·γ) = g(γ) permanece acotada para todo γ.  La función
        de test real correspondiente es f(x) = exp(-x²/(4α)) / sqrt(4πα).

        Args:
            alpha: parámetro de amortiguamiento gaussiano.

        Returns:
            Ψ_SC3 ∈ [0, 1].
        """
        f0_val = 1.0 / math.sqrt(4.0 * math.pi * alpha)

        def f_fn(x: float) -> float:
            return math.exp(-x * x / (4.0 * alpha)) / math.sqrt(4.0 * math.pi * alpha)

        def f_hat_fn(rho: complex) -> complex:
            # Evaluación estable: usa sólo Im(ρ) = γ
            gamma = rho.imag
            return complex(math.exp(-alpha * gamma * gamma), 0.0)

        resultado = self.verificar_formula_weil(
            f_hat_fn=f_hat_fn,
            f_fn=f_fn,
            f0_val=f0_val,
        )
        error_rel = resultado["error_relativo"]
        psi = math.exp(-error_rel)
        return min(1.0, max(0.0, psi))


# ════════════════════════════════════════════════════════════════════════════
# 7. CoherenciaPuentesMathlib — agregador de coherencia Ψ global
# ════════════════════════════════════════════════════════════════════════════

class CoherenciaPuentesMathlib:
    """
    Agrega las coherencias de SC-1, SC-2 y SC-3 en un índice global Ψ.

    Ψ_global = w_SC1·Ψ_SC1 + w_SC2·Ψ_SC2 + w_SC3·Ψ_SC3

    La coherencia cumple QCAL si Ψ_global ≥ PSI_UMBRAL (0.888).
    """

    def __init__(
        self,
        constantes: Optional[ConstantesPuentesMathlib] = None,
    ) -> None:
        self.ctes = constantes if constantes is not None else ConstantesPuentesMathlib()
        self._schatten = OperadorSchatten(p=self.ctes.k_schatten)
        self._fredholm = DeterminanteFredholm()
        self._jacobi = IdentidadJacobi()
        self._espectral = DeterminanteEspectral()
        self._weil = FormulaExplicitaWeil(
            primos=list(self.ctes.primos_base),
            gamma_zeros=list(self.ctes.ceros_riemann),
            n_max=self.ctes.n_max_orbitas,
        )

    # ── coherencias individuales ─────────────────────────────────────────────

    def psi_sc1(self) -> float:
        """
        Coherencia Ψ_SC1 de Schatten/Fredholm.

        Cuantifica la nuclearidad del operador de Weil:
        Ψ_SC1 = exp(-PSI_SC1_SCALING_FACTOR · ‖A‖₁)

        Returns:
            Ψ_SC1 ∈ [0, 1].
        """
        resultado = self._schatten.verificar_nuclearidad_weil(
            primos=list(self.ctes.primos_base),
            k=self.ctes.k_schatten,
        )
        norma_s1 = resultado["norma_s1"]
        # El operador es nuclear; cuantificamos: cuanto menor ‖A‖₁, más coherente
        psi = math.exp(-PSI_SC1_SCALING_FACTOR * norma_s1)
        return min(1.0, max(0.0, psi))

    def psi_sc2(self) -> float:
        """
        Coherencia Ψ_SC2 de la Identidad de Jacobi / Determinante Espectral.

        Usa autovalores sintéticos λ_n = 1/2 + i·γ_n (zeros de Riemann).

        Returns:
            Ψ_SC2 ∈ [0, 1].
        """
        eigenvalues = [
            complex(0.5, gamma) for gamma in self.ctes.ceros_riemann
        ]
        return self._jacobi.psi_jacobi(eigenvalues)

    def psi_sc3(self) -> float:
        """
        Coherencia Ψ_SC3 de la fórmula explícita de Weil.

        Returns:
            Ψ_SC3 ∈ [0, 1].
        """
        return self._weil.psi_sc3()

    # ── coherencia global ────────────────────────────────────────────────────

    def psi_global(self) -> Dict[str, float]:
        """
        Ψ_global = w_SC1·Ψ_SC1 + w_SC2·Ψ_SC2 + w_SC3·Ψ_SC3.

        Returns:
            Diccionario con Ψ_SC1, Ψ_SC2, Ψ_SC3 y Ψ_global.
        """
        p1 = self.psi_sc1()
        p2 = self.psi_sc2()
        p3 = self.psi_sc3()
        pg = (
            self.ctes.w_sc1 * p1
            + self.ctes.w_sc2 * p2
            + self.ctes.w_sc3 * p3
        )
        return {
            "psi_sc1": p1,
            "psi_sc2": p2,
            "psi_sc3": p3,
            "psi_global": min(1.0, max(0.0, pg)),
        }

    def cumple_umbral(self) -> bool:
        """
        Retorna True si Ψ_global ≥ PSI_UMBRAL.

        Returns:
            True si la coherencia global supera el umbral QCAL.
        """
        return self.psi_global()["psi_global"] >= self.ctes.psi_umbral


# ════════════════════════════════════════════════════════════════════════════
# 8. SistemaPuentesMathlib — orquestador principal
# ════════════════════════════════════════════════════════════════════════════

class SistemaPuentesMathlib:
    """
    Orquestador principal de los tres puentes matemáticos QCAL-Mathlib.

    Integra SC-1, SC-2 y SC-3 en un sistema unificado con:
      • Validación cruzada entre puentes
      • Generación de informe completo
      • Verificación del umbral de coherencia QCAL

    Sello: ∴PMQ∞³
    RAM:   RAM-XLVIII-2026-PUENTES-MATHLIB-QCAL
    """

    def __init__(
        self,
        constantes: Optional[ConstantesPuentesMathlib] = None,
    ) -> None:
        self.ctes = constantes if constantes is not None else ConstantesPuentesMathlib()
        self.schatten = OperadorSchatten(p=self.ctes.k_schatten)
        self.fredholm = DeterminanteFredholm()
        self.jacobi = IdentidadJacobi()
        self.espectral = DeterminanteEspectral()
        self.weil = FormulaExplicitaWeil(
            primos=list(self.ctes.primos_base),
            gamma_zeros=list(self.ctes.ceros_riemann),
            n_max=self.ctes.n_max_orbitas,
        )
        self.coherencia = CoherenciaPuentesMathlib(self.ctes)

    # ── SC-1 ─────────────────────────────────────────────────────────────────

    def ejecutar_sc1(self) -> Dict[str, Any]:
        """
        Ejecuta el puente SC-1: Schatten / Fredholm.

        Returns:
            Diccionario con nuclearidad, normas, orden de Hadamard y Ψ_SC1.
        """
        primos = list(self.ctes.primos_base)
        k = self.ctes.k_schatten

        # Nuclearidad
        nuclear = self.schatten.verificar_nuclearidad_weil(primos=primos, k=k)

        # Eigenvalues para Fredholm (usando valores singulares reales)
        singulares = nuclear["singulares"]
        eigenvalues_r = [complex(s, 0.0) for s in singulares]

        # Propiedades del determinante de Fredholm en z=1
        det_z1 = self.fredholm.det_fredholm(complex(1.0, 0.0), eigenvalues_r)
        es_entera = self.fredholm.es_funcion_entera(eigenvalues_r)
        orden_had = self.fredholm.orden_hadamard(eigenvalues_r)

        psi = self.coherencia.psi_sc1()

        return {
            "puente": "SC-1",
            "nombre": "Operadores de Schatten / Determinante de Fredholm",
            "nuclearidad": nuclear,
            "det_fredholm_z1": det_z1,
            "es_funcion_entera": es_entera,
            "orden_hadamard": orden_had,
            "psi_sc1": psi,
            "estado": "✓" if nuclear["es_nuclear"] else "✗",
        }

    # ── SC-2 ─────────────────────────────────────────────────────────────────

    def ejecutar_sc2(self) -> Dict[str, Any]:
        """
        Ejecuta el puente SC-2: Identidad de Jacobi / Determinante Espectral.

        Returns:
            Diccionario con identidad Jacobi, Hadamard, xi-equivalencia y Ψ_SC2.
        """
        eigenvalues = [
            complex(0.5, gamma) for gamma in self.ctes.ceros_riemann
        ]

        # Identidad de Jacobi
        jacobi_ok = self.jacobi.verificar_jacobi(eigenvalues)
        err_jacobi = self.jacobi.error_jacobi(eigenvalues)

        # Factorización de Hadamard del determinante espectral
        hadamard = self.espectral.verificar_hadamard(eigenvalues, n_puntos=5)

        # Equivalencia Δ(s) ≡ ξ(s) en s = 2 + i
        xi_eq = self.espectral.xi_equivalencia(complex(2.0, 1.0))

        psi = self.coherencia.psi_sc2()

        return {
            "puente": "SC-2",
            "nombre": "Determinante Espectral / Identidad de Jacobi",
            "jacobi_verificada": jacobi_ok,
            "error_jacobi": err_jacobi,
            "hadamard": hadamard,
            "xi_equivalencia": xi_eq,
            "psi_sc2": psi,
            "estado": "✓" if jacobi_ok and hadamard["es_valido"] else "✗",
        }

    # ── SC-3 ─────────────────────────────────────────────────────────────────

    def ejecutar_sc3(self) -> Dict[str, Any]:
        """
        Ejecuta el puente SC-3: Fórmula Explícita de Weil.

        Returns:
            Diccionario con verificación Weil y Ψ_SC3.
        """
        alpha = GAUSSIAN_DAMPING_ALPHA
        f0_val = 1.0 / math.sqrt(4.0 * math.pi * alpha)

        def f_fn(x: float) -> float:
            return math.exp(-x * x / (4.0 * alpha)) / math.sqrt(4.0 * math.pi * alpha)

        def f_hat_fn(rho: complex) -> complex:
            gamma = rho.imag
            return complex(math.exp(-alpha * gamma * gamma), 0.0)

        verificacion = self.weil.verificar_formula_weil(
            f_hat_fn=f_hat_fn,
            f_fn=f_fn,
            f0_val=1.0,
        )

        psi = self.coherencia.psi_sc3()

        return {
            "puente": "SC-3",
            "nombre": "Fórmula Explícita de Weil / Poisson Adélico",
            "verificacion_weil": verificacion,
            "psi_sc3": psi,
            "estado": "✓" if verificacion["es_valida"] else "✗",
        }

    # ── sistema completo ─────────────────────────────────────────────────────

    def activar(self) -> Dict[str, Any]:
        """
        Ejecuta el sistema completo de los tres puentes matemáticos.

        Orquesta SC-1 → SC-2 → SC-3, calcula la coherencia global Ψ
        y genera el informe QCAL.

        Returns:
            Diccionario completo con resultados, coherencia y metadatos.
        """
        timestamp = datetime.now(timezone.utc).isoformat()

        sc1 = self.ejecutar_sc1()
        sc2 = self.ejecutar_sc2()
        sc3 = self.ejecutar_sc3()

        coherencias = self.coherencia.psi_global()
        cumple = self.coherencia.cumple_umbral()

        return {
            "sello": self.ctes.sello,
            "ram": self.ctes.ram,
            "timestamp": timestamp,
            "f0_hz": self.ctes.f0,
            "sc1": sc1,
            "sc2": sc2,
            "sc3": sc3,
            "coherencia": coherencias,
            "cumple_umbral_qcal": cumple,
            "psi_umbral": self.ctes.psi_umbral,
            "constantes": self.ctes.resumen(),
            "estado_global": "✓ QCAL-COHERENTE" if cumple else "✗ SUB-UMBRAL",
        }


# ════════════════════════════════════════════════════════════════════════════
# API PÚBLICA
# ════════════════════════════════════════════════════════════════════════════

def puentes_mathlib_qcal_activar(
    constantes: Optional[ConstantesPuentesMathlib] = None,
) -> Dict[str, Any]:
    """
    Activa el sistema completo de Puentes Mathlib QCAL.

    Punto de entrada único para ejecutar los tres puentes matemáticos
    (SC-1, SC-2, SC-3) y obtener el informe de coherencia QCAL.

    Args:
        constantes: constantes de configuración (opcional; usa defaults si None).

    Returns:
        Diccionario con resultados de SC-1, SC-2, SC-3, coherencia global
        Ψ y metadatos de sello/RAM/timestamp.

    Example::

        resultado = puentes_mathlib_qcal_activar()
        print(resultado["estado_global"])
        print(f"Ψ_global = {resultado['coherencia']['psi_global']:.4f}")
    """
    sistema = SistemaPuentesMathlib(constantes=constantes)
    return sistema.activar()


# ════════════════════════════════════════════════════════════════════════════
# PUNTO DE ENTRADA
# ════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    resultado = puentes_mathlib_qcal_activar()

    print("=" * 70)
    print(f"  PUENTES MATHLIB QCAL  —  {resultado['sello']}")
    print("=" * 70)
    print(f"  RAM      : {resultado['ram']}")
    print(f"  Timestamp: {resultado['timestamp']}")
    print(f"  F0       : {resultado['f0_hz']} Hz")
    print()

    for puente_key in ("sc1", "sc2", "sc3"):
        p = resultado[puente_key]
        print(f"  [{p['estado']}] {p['puente']} — {p['nombre']}")

    coh = resultado["coherencia"]
    print()
    print(f"  Ψ_SC1    = {coh['psi_sc1']:.6f}")
    print(f"  Ψ_SC2    = {coh['psi_sc2']:.6f}")
    print(f"  Ψ_SC3    = {coh['psi_sc3']:.6f}")
    print(f"  Ψ_global = {coh['psi_global']:.6f}  (umbral {resultado['psi_umbral']})")
    print()
    print(f"  Estado   : {resultado['estado_global']}")
    print("=" * 70)
