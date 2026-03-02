"""
riemann_operator_H_corrected.py
================================
Extensión del operador Wu-Sprung con corrección oscilatoria:

    V(x) = V_Abel(x) + ε · V_osc(x)

donde V_osc(x) es la corrección de primos truncada (ansatz de Gutzwiller/Berry-Keating):

    V_osc(x) = Σ_{p ≤ P prime}  (log p / √p) · cos(x · log p)

Esta corrección NO usa ceros de ζ — se construye únicamente con los primos mediante
la criba de Eratóstenes.

Contenido
---------
  primes_up_to(P)              : criba de Eratóstenes
  V_osc_prime_sum(x, primes)   : corrección oscilatoria punto a punto
  V_osc_array(x_grid, primes)  : corrección vectorizada sobre una rejilla
  CorrectedWuSprungOperator    : V = V_Abel + ε·V_osc, discretización tridiagonal
  SpacingAnalysis              : análisis de espaciado de niveles vs. GUE (Wigner-Dyson)
  epsilon_sweep                : búsqueda del ε óptimo minimizando el error espectral
  N_sweep                      : convergencia del error frente al tamaño de rejilla
  run_corrected_analysis       : pipeline completo de demostración

Autor: JMMB Ψ (Trinity QCAL ∞³)
DOI: 10.5281/zenodo.17379721
"""
from __future__ import annotations

import math
from typing import Dict, List, Optional, Tuple

import numpy as np

from riemann_operator_H import (
    ZEROS_ZETA_REFERENCIA,
    N_smooth,
    WuSprungOperator,
    _EPS,
)

# ---------------------------------------------------------------------------
# Constantes del módulo
# ---------------------------------------------------------------------------
FRECUENCIA_TRUTH = 141.7001
COHERENCIA_UMBRAL = 0.888
_GUE_MEAN = math.sqrt(math.pi) / 2.0       # ≈ 0.8862 (Wigner-Dyson GUE)
_TOLERANCE_5PCT = 0.05                      # umbral de error relativo del 5 %
_FRACTION_SMALL_THRESHOLD = 0.2            # umbral para fraction_small_spacings


# ===========================================================================
# 1.  Criba de Eratóstenes
# ===========================================================================

def primes_up_to(P: int) -> List[int]:
    """
    Devuelve la lista de números primos p ≤ P mediante la criba de Eratóstenes.

    Args:
        P: Cota superior (inclusive).  Si P < 2, devuelve lista vacía.

    Returns:
        Lista ordenada de primos p con 2 ≤ p ≤ P.
        Lista vacía si P < 2.
    """
    if P < 2:
        return []
    sieve = bytearray([1]) * (P + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(P ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i, v in enumerate(sieve) if v]


# ===========================================================================
# 2.  Corrección oscilatoria V_osc
# ===========================================================================

def V_osc_prime_sum(x: float, primes: List[int]) -> float:
    """
    Calcula la corrección oscilatoria punto a punto:

        V_osc(x) = Σ_{p ∈ primes}  (log p / √p) · cos(x · log p)

    Motivación: ansatz de Gutzwiller/Berry-Keating — los primos son las
    "órbitas periódicas clásicas" del hamiltoniano xp, con período T_p = log p.

    Args:
        x:      Punto de evaluación.
        primes: Lista de primos obtenida con :func:`primes_up_to`.

    Returns:
        Valor real V_osc(x).
    """
    total = 0.0
    for p in primes:
        lp = math.log(p)
        total += (lp / math.sqrt(p)) * math.cos(x * lp)
    return total


def V_osc_array(x_grid: np.ndarray, primes: List[int]) -> np.ndarray:
    """
    Versión vectorizada de :func:`V_osc_prime_sum` sobre una rejilla.

    Args:
        x_grid: Array 1-D de posiciones.
        primes: Lista de primos.

    Returns:
        Array 1-D con V_osc evaluado en cada punto de la rejilla.
    """
    if len(primes) == 0:
        return np.zeros_like(x_grid, dtype=float)
    log_p = np.log(np.array(primes, dtype=float))        # (P,)
    weight = log_p / np.sqrt(np.array(primes, dtype=float))  # (P,)
    # x_grid[:, None] · log_p[None, :] → (N, P)
    phase = np.outer(x_grid, log_p)                      # (N, P)
    return (np.cos(phase) * weight[np.newaxis, :]).sum(axis=1)   # (N,)


# ===========================================================================
# 3.  Operador corregido
# ===========================================================================

class CorrectedWuSprungOperator:
    """
    Operador de Schrödinger con potencial corregido:

        H = −d²/dx² + V_Abel(x) + ε · V_osc(x)

    Discretización tridiagonal de Dirichlet en [0, x_max].

    Args:
        N:           Número de puntos interiores.
        x_max:       Extremo derecho del intervalo.
        epsilon:     Amplitud de la corrección oscilatoria.
        primes_upto: Primos p ≤ primes_upto usados en V_osc.
    """

    def __init__(
        self,
        N: int = 300,
        x_max: float = 13.0,
        epsilon: float = 0.0,
        primes_upto: int = 100,
    ) -> None:
        if N < 2:
            raise ValueError("N debe ser ≥ 2")
        if x_max <= 0:
            raise ValueError("x_max debe ser positivo")
        if epsilon < 0:
            raise ValueError("epsilon debe ser ≥ 0")

        self.N = N
        self.x_max = x_max
        self.epsilon = epsilon
        self.primes_upto = primes_upto

        self._dx = x_max / (N + 1)
        self._x_grid = np.linspace(self._dx, x_max - self._dx, N)
        self._primes = primes_up_to(primes_upto)

        # Potencial base (Wu-Sprung)
        base_op = WuSprungOperator(N=N, x_max=x_max)
        self._V_base = base_op.potential.copy()

        # Corrección oscilatoria
        self._V_osc = V_osc_array(self._x_grid, self._primes)

        # Potencial total
        self._V_total = self._V_base + epsilon * self._V_osc

        self._eigenvalues: Optional[np.ndarray] = None

    # ------------------------------------------------------------------
    # Propiedades
    # ------------------------------------------------------------------

    @property
    def x_grid(self) -> np.ndarray:
        return self._x_grid

    @property
    def potential(self) -> np.ndarray:
        """Potencial total V_Abel + ε·V_osc."""
        return self._V_total

    @property
    def potential_base(self) -> np.ndarray:
        """Potencial base V_Abel."""
        return self._V_base

    @property
    def potential_osc(self) -> np.ndarray:
        """Corrección oscilatoria V_osc (sin factor ε)."""
        return self._V_osc

    # ------------------------------------------------------------------
    # Diagonalización
    # ------------------------------------------------------------------

    def _build_matrix(self) -> np.ndarray:
        dx2 = self._dx ** 2
        diag_main = 2.0 / dx2 + self._V_total
        diag_off = -1.0 / dx2 * np.ones(self.N - 1)
        H = np.diag(diag_main) + np.diag(diag_off, 1) + np.diag(diag_off, -1)
        return H

    def eigenvalues(self, n_vals: Optional[int] = None) -> np.ndarray:
        """
        Calcula y cachea los autovalores del operador.

        Args:
            n_vals: Número de autovalores menores a devolver (None → todos).

        Returns:
            Array ordenado de autovalores.
        """
        if self._eigenvalues is None:
            H = self._build_matrix()
            self._eigenvalues = np.sort(np.linalg.eigvalsh(H))
        if n_vals is None:
            return self._eigenvalues.copy()
        return self._eigenvalues[:n_vals].copy()

    # ------------------------------------------------------------------
    # Comparación con ceros de referencia
    # ------------------------------------------------------------------

    def compare_to_zeros(
        self,
        refs: Optional[List[float]] = None,
    ) -> Tuple[np.ndarray, np.ndarray, float]:
        """
        Compara los autovalores con los ceros de ζ de referencia.

        Args:
            refs: Lista de ceros.  None → ZEROS_ZETA_REFERENCIA.

        Returns:
            Tupla (eigenvalues[:n], refs_array, mean_abs_error).
        """
        if refs is None:
            refs = ZEROS_ZETA_REFERENCIA
        n = len(refs)
        evals = self.eigenvalues(n)
        refs_arr = np.array(refs[:n])
        mae = float(np.mean(np.abs(evals[:n] - refs_arr)))
        return evals[:n], refs_arr, mae

    # ------------------------------------------------------------------
    # Número de repulsión de niveles
    # ------------------------------------------------------------------

    def fraction_small_spacings(
        self, threshold: float = _FRACTION_SMALL_THRESHOLD
    ) -> float:
        """
        Fracción de espaciados normalizados s_n < threshold.

        Un valor bajo indica repulsión de niveles (compatible con GUE).

        Args:
            threshold: Umbral de corte (por defecto :data:`_FRACTION_SMALL_THRESHOLD`).

        Returns:
            Fracción en [0, 1].
        """
        evals = self.eigenvalues()
        spacings = np.diff(evals)
        if len(spacings) == 0:
            return 0.0
        mean_s = float(np.mean(spacings))
        if mean_s < _EPS:
            return 0.0
        normalized = spacings / mean_s
        return float(np.mean(normalized < threshold))


# ===========================================================================
# 4.  Análisis de espaciado GUE (desdoblamiento con N_smooth)
# ===========================================================================

class SpacingAnalysis:
    """
    Análisis de espaciado de niveles espectrales frente a la distribución GUE.

    Realiza el **desdoblamiento** (unfolding) estándar:
        ξ_n = N_smooth(E_n)
    de modo que los espaciados s_n = ξ_{n+1} − ξ_n tienen media ≈ 1.

    Luego compara la distribución de espaciados con Wigner-Dyson GUE:
        p(s) = (π/2) s · exp(−π s² / 4)

    Args:
        eigenvalues: Array de autovalores (energías E_n).
    """

    def __init__(self, eigenvalues: np.ndarray) -> None:
        self._evals = np.sort(eigenvalues)
        self._unfolded: Optional[np.ndarray] = None
        self._spacings: Optional[np.ndarray] = None

    # ------------------------------------------------------------------
    # Desdoblamiento
    # ------------------------------------------------------------------

    def _unfold(self) -> np.ndarray:
        """Mapea E_n → ξ_n = N_smooth(E_n)."""
        return np.array([N_smooth(float(e)) for e in self._evals])

    @property
    def unfolded(self) -> np.ndarray:
        """Valores ξ_n tras el desdoblamiento."""
        if self._unfolded is None:
            self._unfolded = self._unfold()
        return self._unfolded

    @property
    def spacings(self) -> np.ndarray:
        """Espaciados normalizados s_n = ξ_{n+1} − ξ_n."""
        if self._spacings is None:
            xi = self.unfolded
            s = np.diff(xi)
            mean_s = float(np.mean(s)) if len(s) > 0 else 1.0
            if mean_s < _EPS:
                mean_s = 1.0
            self._spacings = s / mean_s
        return self._spacings

    # ------------------------------------------------------------------
    # Estadísticos frente a GUE
    # ------------------------------------------------------------------

    @staticmethod
    def wigner_dyson_pdf(s: np.ndarray) -> np.ndarray:
        """
        Densidad de probabilidad de Wigner-Dyson (GUE):

            p(s) = (π/2) · s · exp(−π s² / 4)

        Args:
            s: Array de valores s ≥ 0.

        Returns:
            Array de densidades p(s).
        """
        return (math.pi / 2.0) * s * np.exp(-math.pi * s ** 2 / 4.0)

    def mean_spacing(self) -> float:
        """Media de los espaciados normalizados (debe ser ≈ 1)."""
        s = self.spacings
        return float(np.mean(s)) if len(s) > 0 else 0.0

    def ks_statistic(self) -> float:
        """
        Estadístico de Kolmogorov-Smirnov entre la distribución empírica de
        espaciados y la CDF de Wigner-Dyson GUE.

        La CDF de Wigner-Dyson es:
            F(s) = 1 − exp(−π s² / 4)

        Returns:
            Estadístico KS en [0, 1].  Valores menores → mayor compatibilidad con GUE.
        """
        s = np.sort(self.spacings)
        if len(s) == 0:
            return 0.0
        n = len(s)
        # CDF teórica de Wigner-Dyson
        F_theory = 1.0 - np.exp(-math.pi * s ** 2 / 4.0)
        # CDF empírica
        F_emp = np.arange(1, n + 1) / n
        return float(np.max(np.abs(F_emp - F_theory)))

    def fraction_small_spacings(
        self, threshold: float = _FRACTION_SMALL_THRESHOLD
    ) -> float:
        """
        Fracción de espaciados normalizados s_n < threshold.

        Args:
            threshold: Umbral de corte.

        Returns:
            Fracción en [0, 1].
        """
        s = self.spacings
        if len(s) == 0:
            return 0.0
        return float(np.mean(s < threshold))


# ===========================================================================
# 5.  Barrido sobre ε (epsilon_sweep)
# ===========================================================================

def epsilon_sweep(
    epsilons: List[float],
    primes_upto: int = 100,
    N: int = 300,
    x_max: float = 13.0,
    refs: Optional[List[float]] = None,
) -> List[Dict]:
    """
    Calcula el error espectral para cada valor de ε en la lista.

    Args:
        epsilons:    Lista de valores de ε a evaluar.
        primes_upto: Primos usados en V_osc.
        N:           Puntos interiores de la rejilla.
        x_max:       Extremo del intervalo.
        refs:        Ceros de referencia (None → ZEROS_ZETA_REFERENCIA).

    Returns:
        Lista de dicts con claves:
          ``epsilon``, ``mean_abs_error``, ``n_within_1``, ``n_within_5pct``,
          ``improvement_vs_base``.
    """
    if refs is None:
        refs = ZEROS_ZETA_REFERENCIA

    # Error base (ε = 0)
    base_op = CorrectedWuSprungOperator(N=N, x_max=x_max, epsilon=0.0,
                                        primes_upto=primes_upto)
    _, refs_arr, base_error = base_op.compare_to_zeros(refs)

    results = []
    for eps in epsilons:
        op = CorrectedWuSprungOperator(N=N, x_max=x_max, epsilon=float(eps),
                                       primes_upto=primes_upto)
        evals, refs_arr, mae = op.compare_to_zeros(refs)
        n = len(refs_arr)
        errors = np.abs(evals[:n] - refs_arr[:n])
        results.append({
            "epsilon": float(eps),
            "mean_abs_error": mae,
            "n_within_1": int(np.sum(errors < 1.0)),
            "n_within_5pct": int(
                np.sum(errors / np.maximum(refs_arr[:n], _EPS) < _TOLERANCE_5PCT)
            ),
            "improvement_vs_base": float(base_error - mae),
        })
    return results


# ===========================================================================
# 6.  Barrido sobre N (N_sweep)
# ===========================================================================

def N_sweep(
    N_values: List[int],
    epsilon: float = 0.3,
    primes_upto: int = 100,
    x_max: float = 13.0,
    refs: Optional[List[float]] = None,
) -> List[Dict]:
    """
    Estudia la convergencia del error espectral al aumentar el tamaño de la rejilla.

    Para cada N calcula MAE_base (ε=0) y MAE_corrected (ε dado), y reporta la mejora.

    Args:
        N_values:    Lista de valores de N a evaluar.
        epsilon:     Amplitud de la corrección oscilatoria.
        primes_upto: Primos usados en V_osc.
        x_max:       Extremo del intervalo.
        refs:        Ceros de referencia.

    Returns:
        Lista de dicts con claves:
          ``N``, ``mae_base``, ``mae_corrected``, ``improvement``.
    """
    if refs is None:
        refs = ZEROS_ZETA_REFERENCIA

    results = []
    for n in N_values:
        base_op = CorrectedWuSprungOperator(N=n, x_max=x_max, epsilon=0.0,
                                            primes_upto=primes_upto)
        _, _, mae_base = base_op.compare_to_zeros(refs)

        corr_op = CorrectedWuSprungOperator(N=n, x_max=x_max, epsilon=epsilon,
                                            primes_upto=primes_upto)
        _, _, mae_corr = corr_op.compare_to_zeros(refs)

        results.append({
            "N": n,
            "mae_base": mae_base,
            "mae_corrected": mae_corr,
            "improvement": mae_base - mae_corr,
        })
    return results


# ===========================================================================
# 7.  Utilidades internas
# ===========================================================================

def _check_monotone_decreasing(values: List[float]) -> bool:
    """Devuelve True si la lista es no-creciente (cada valor ≤ al anterior)."""
    return all(values[i] >= values[i + 1] for i in range(len(values) - 1))


# ===========================================================================
# 8.  Pipeline completo de demostración
# ===========================================================================

def run_corrected_analysis(
    epsilon_sweep_values: Optional[List[float]] = None,
    N_sweep_values: Optional[List[int]] = None,
    best_epsilon: float = 0.3,
    best_primes_upto: int = 100,
    N_main: int = 500,
    x_max: float = 13.0,
) -> Dict:
    """
    Ejecuta el análisis completo de corrección oscilatoria.

    Pasos:
      1. Barrido en ε (epsilon_sweep).
      2. Barrido en N (N_sweep).
      3. Operador corregido óptimo + análisis de espaciado GUE.
      4. Comparación de KS: ceros de ζ vs. Wu-Sprung.

    Args:
        epsilon_sweep_values: Lista de ε para el barrido.
        N_sweep_values:       Lista de N para el barrido.
        best_epsilon:         ε óptimo para el análisis principal.
        best_primes_upto:     Primos usados en el análisis principal.
        N_main:               Tamaño de rejilla para el análisis principal.
        x_max:                Extremo del intervalo.

    Returns:
        Dict resumen con todas las métricas.
    """
    if epsilon_sweep_values is None:
        epsilon_sweep_values = [0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]
    if N_sweep_values is None:
        N_sweep_values = [100, 200, 300, 500, 700]

    # ----- Barrido ε -----
    eps_results = epsilon_sweep(
        epsilons=epsilon_sweep_values,
        primes_upto=best_primes_upto,
        N=300,
        x_max=x_max,
    )

    # ----- Barrido N -----
    n_results = N_sweep(
        N_values=N_sweep_values,
        epsilon=best_epsilon,
        primes_upto=best_primes_upto,
        x_max=x_max,
    )

    # ----- Análisis GUE con operador corregido -----
    main_op = CorrectedWuSprungOperator(
        N=N_main, x_max=x_max,
        epsilon=best_epsilon, primes_upto=best_primes_upto,
    )
    evals_corr = main_op.eigenvalues()
    sa_corr = SpacingAnalysis(evals_corr)

    base_op_main = CorrectedWuSprungOperator(
        N=N_main, x_max=x_max, epsilon=0.0, primes_upto=best_primes_upto,
    )
    evals_base = base_op_main.eigenvalues()
    sa_base = SpacingAnalysis(evals_base)

    # Ceros de referencia como espectro ideal
    sa_zeros = SpacingAnalysis(np.array(ZEROS_ZETA_REFERENCIA))

    ks_corr  = sa_corr.ks_statistic()
    ks_base  = sa_base.ks_statistic()
    ks_zeros = sa_zeros.ks_statistic()

    return {
        "epsilon_sweep": eps_results,
        "n_sweep": {
            "epsilon": best_epsilon,
            "primes_upto": best_primes_upto,
            "results": n_results,
            "monotone_convergence_base": _check_monotone_decreasing(
                [r["mae_base"] for r in n_results]
            ),
            "correction_always_improves": all(
                r["improvement"] > 0 for r in n_results
            ),
        },
        "gue_analysis": {
            "ks_corrected": ks_corr,
            "ks_base": ks_base,
            "ks_zeros_reference": ks_zeros,
            "mean_spacing_corrected": sa_corr.mean_spacing(),
            "mean_spacing_base": sa_base.mean_spacing(),
        },
    }
