"""
riemann_formula_avanzada.py
Tres métodos matemáticamente serios para aproximar la fórmula explícita
de Riemann *sin usar ceros precalculados*, más allá del truncado simple
en P ≤ 100.
────────────────────────────────────────────────────────────────────────
CONTEXTO
────────────────────────────────────────────────────────────────────────
La fórmula explícita de von Mangoldt:
    ψ(x) = x - Σ_ρ x^ρ/ρ  - log(2π) - ½ log(1 - x^{-2})
expresa ψ(x) mediante los ceros no-triviales ρ.  Agregar términos
oscilatorios primales directamente no es suficiente para cerrar RH:
se necesita autoadjunción global, control del dominio y equivalencia
espectral exacta.

MÉTODOS IMPLEMENTADOS
────────────────────────────────────────────────────────────────────────
A) WeilFuncionPrueba   – mollificación gaussiana exacta vía CDF normal
B) MellinExponencial   – regularización exponencial Σ_p (log p/√p)·e^{-p/P}
C) RiemannSiegelPrimos – ceros auto-generados vía suma Z(t) de Riemann–Siegel

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""
from __future__ import annotations

import math
from functools import cached_property
from typing import Optional

import mpmath
import numpy as np
from scipy.optimize import brentq
from scipy.special import ndtr  # Normal CDF

from riemann_explicit_formula import chebyshev_psi, _sieve, _prime_powers_up_to

# ---------------------------------------------------------------------------
# Constantes por defecto (públicas)
# ---------------------------------------------------------------------------
EPSILON_DEFAULT: float = 0.4
DELTA_WEIL_DEFAULT: float = 0.10
P_MELLIN_DEFAULT: float = 1000.0

# ---------------------------------------------------------------------------
# Constantes internas
# ---------------------------------------------------------------------------
# Umbral mínimo del denominador de C₀ para evitar división por cero
_C0_DENOM_THRESHOLD: float = 1e-8
# Umbral para descartar pesos exponenciales despreciables
_WEIGHT_THRESHOLD: float = 1e-15
# Separación mínima entre ceros para evitar duplicados
_ZERO_DUPLICATE_THRESHOLD: float = 0.01

# Primeros ceros conocidos de Z(t) (partes imaginarias de ceros no-triviales)
# γ_n: Im(ρ_n) con ρ_n = 1/2 + i γ_n
_REFERENCE_ZEROS = np.array([
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918720, 43.327073, 48.005150, 49.773832,
])


# ---------------------------------------------------------------------------
# Funciones auxiliares: θ(t) y Z(t) de Riemann–Siegel
# ---------------------------------------------------------------------------

def _theta_rs(t: float) -> float:
    """Función de fase θ(t) de Riemann–Siegel (valor exacto vía mpmath).

    θ(t) = Im(log Γ(¼ + it/2)) − (t/2)·log π

    Parameters
    ----------
    t : float
        Argumento real, t > 0.

    Returns
    -------
    float
        θ(t).

    Raises
    ------
    ValueError
        Si t ≤ 0.
    """
    if t <= 0.0:
        raise ValueError("t must be positive for _theta_rs")
    return float(mpmath.siegeltheta(t))
    # float() conversion: mpmath result has >50 dps, but all callers use
    # Python float arithmetic (math.cos, np.cos), so float64 is sufficient.


def _theta_rs_stirling(t: float) -> float:
    """Aproximación de Stirling de θ(t).

    θ(t) ≈ (t/2)·log(t/(2π)) − t/2 − π/8 + 1/(48t) + 7/(5760 t³)

    Parameters
    ----------
    t : float
        Argumento real, t > 0.

    Returns
    -------
    float
        Aproximación asintótica de θ(t).

    Raises
    ------
    ValueError
        Si t ≤ 0.
    """
    if t <= 0.0:
        raise ValueError("t must be positive for _theta_rs_stirling")
    half_t = t / 2.0
    return (
        half_t * math.log(t / (2.0 * math.pi))
        - half_t
        - math.pi / 8.0
        + 1.0 / (48.0 * t)
        + 7.0 / (5760.0 * t ** 3)
    )


def _Z_main_sum(t: float, N: Optional[int] = None) -> float:
    """Suma principal de Riemann–Siegel Z(t) con corrección C₀.

    Z(t) ≈ 2 Σ_{n=1}^{N} n^{-½} cos(θ(t) − t log n)
           + (−1)^{N−1} (t/2π)^{−¼} C₀(p)

    donde  N = ⌊√(t/2π)⌋,  p = {√(t/2π)} (parte fraccionaria),
    C₀(p) = cos(2π(p² − p − 1/16)) / cos(2πp).

    Se emplea θ(t) exacto de mpmath para máxima precisión cerca
    del primer cero γ₁ ≈ 14.1347.

    Parameters
    ----------
    t : float
        Argumento real, t ≥ 0.
    N : int, optional
        Número de términos en la suma. Por defecto ⌊√(t/2π)⌋.

    Returns
    -------
    float
        Valor aproximado de Z(t).
    """
    if t <= 0.0:
        return 0.0

    theta = _theta_rs(t)
    sqrt_t2pi = math.sqrt(t / (2.0 * math.pi))

    if N is None:
        N = int(sqrt_t2pi)

    if N == 0:
        return 0.0

    # Suma principal
    total = sum(
        n ** (-0.5) * math.cos(theta - t * math.log(n))
        for n in range(1, N + 1)
    )
    total *= 2.0

    # Corrección C₀ (primer término de la serie de resto de Riemann–Siegel)
    p_frac = sqrt_t2pi - int(sqrt_t2pi)
    denom = math.cos(2.0 * math.pi * p_frac)
    if abs(denom) > _C0_DENOM_THRESHOLD:
        C0 = math.cos(
            2.0 * math.pi * (p_frac ** 2 - p_frac - 1.0 / 16.0)
        ) / denom
        total += ((-1) ** (N - 1)) * (t / (2.0 * math.pi)) ** (-0.25) * C0

    return total


# ---------------------------------------------------------------------------
# A) Weil Función de Prueba  – mollificación gaussiana
# ---------------------------------------------------------------------------

class WeilFuncionPrueba:
    """Aproximación mollificada de ψ(x) mediante funciones de prueba de Weil.

    La mollificación gaussiana de ψ(x) es:
        ψ_δ(x) = Σ_{p^k} log(p) · Φ((x − p^k) / δ)

    donde Φ es la CDF normal estándar y δ > 0 es el parámetro de suavización.
    Para x ≤ 1 se devuelve 0 exactamente.

    Parameters
    ----------
    delta : float
        Ancho de la mollificación (σ del gaussiano), δ > 0.
    p_max : float
        Límite superior para la criba de potencias de primos.
    """

    def __init__(self, delta: float = DELTA_WEIL_DEFAULT, p_max: float = 500.0) -> None:
        if delta <= 0.0:
            raise ValueError("delta must be strictly positive")
        if p_max < 2:
            raise ValueError("p_max must be >= 2")
        self.delta = float(delta)
        self.p_max = float(p_max)

        pairs = _prime_powers_up_to(p_max)
        if pairs:
            pks, logps = zip(*pairs)
            self._pk = np.array(pks, dtype=float)
            self._logp = np.array(logps, dtype=float)
        else:
            self._pk = np.array([], dtype=float)
            self._logp = np.array([], dtype=float)

    @property
    def n_prime_powers(self) -> int:
        """Número de potencias de primos en [2, p_max]."""
        return len(self._pk)

    def evaluate(self, x: float) -> float:
        """ψ_δ(x) suavizada con función de prueba gaussiana.

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            ψ_δ(x).
        """
        if x <= 1.0:
            return 0.0
        if len(self._pk) == 0:
            return 0.0
        z = (x - self._pk) / self.delta
        return float(np.sum(self._logp * ndtr(z)))

    def evaluate_array(self, x_arr: np.ndarray) -> np.ndarray:
        """Versión vectorizada de evaluate.

        Parameters
        ----------
        x_arr : np.ndarray
            Array de puntos de evaluación.

        Returns
        -------
        np.ndarray
            Array de valores ψ_δ(x).
        """
        x_arr = np.asarray(x_arr, dtype=float)
        if len(self._pk) == 0:
            return np.zeros(len(x_arr))
        z = (x_arr[:, np.newaxis] - self._pk[np.newaxis, :]) / self.delta
        result = (self._logp[np.newaxis, :] * ndtr(z)).sum(axis=1)
        result[x_arr <= 1.0] = 0.0
        return result

    def convergence_bound(self, x: float) -> float:
        """Cota superior del error |ψ_δ(x) − ψ(x)|.

        Cota heurística: δ · √x · log²x / (2π) (proporcional al paso de
        suavización y a la densidad local de primos).

        Parameters
        ----------
        x : float
            Punto de evaluación (x > 1).

        Returns
        -------
        float
            Cota no-negativa del error de mollificación.
        """
        if x <= 1.0:
            return 0.0
        return self.delta * math.sqrt(x) * math.log(max(x, 2.0)) ** 2 / (2.0 * math.pi)


# ---------------------------------------------------------------------------
# B) Mellin Exponencial  – regularización exponencial de la suma de primos
# ---------------------------------------------------------------------------

class MellinExponencial:
    """Regularización exponencial (Laplace) de la suma oscilatoria primaria.

    La corrección exponencial es:
        V_mell(x; P, ε) = ε · Σ_p (log p / √p) · e^{−p/P} · cos(x log p)

    y la aproximación de ψ es: ψ(x) ≈ x + V_mell(x).

    Parameters
    ----------
    P : float
        Parámetro de corte exponencial (escala de amortiguamiento), P > 0.
    epsilon : float
        Factor de escala de la corrección (ε > 0).
    """

    def __init__(self, P: float = P_MELLIN_DEFAULT, epsilon: float = EPSILON_DEFAULT) -> None:
        if P <= 0.0:
            raise ValueError("P must be strictly positive")
        if epsilon <= 0.0:
            raise ValueError("epsilon must be strictly positive")
        self.P = float(P)
        self.epsilon = float(epsilon)

        # Recopilar primos hasta ~5·P (exponencial muy pequeña más allá de eso)
        upper = max(int(5.0 * P) + 1, 10)
        is_prime = _sieve(upper)
        primes = np.array([p for p in range(2, upper + 1) if is_prime[p]], dtype=float)

        # Pesos: (log p / √p) · e^{−p/P}
        log_p = np.log(primes)
        weights = log_p / np.sqrt(primes) * np.exp(-primes / P)

        # Descartar pesos despreciables (< _WEIGHT_THRESHOLD)
        mask = weights > _WEIGHT_THRESHOLD
        self._primes = primes[mask]
        self._log_p = log_p[mask]
        self._weights = weights[mask]

    @property
    def n_primes(self) -> int:
        """Número de primos con peso significativo."""
        return len(self._primes)

    def evaluate(self, x: float) -> float:
        """Corrección oscilatoria V_mell(x).

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            V_mell(x) = ε · Σ_p (log p/√p) · e^{−p/P} · cos(x log p).
        """
        if len(self._primes) == 0:
            return 0.0
        return float(self.epsilon * np.sum(self._weights * np.cos(x * self._log_p)))

    def evaluate_array(self, x_arr: np.ndarray) -> np.ndarray:
        """Versión vectorizada de evaluate.

        Parameters
        ----------
        x_arr : np.ndarray
            Array de puntos de evaluación.

        Returns
        -------
        np.ndarray
            Array de valores V_mell(x).
        """
        x_arr = np.asarray(x_arr, dtype=float)
        if len(self._primes) == 0:
            return np.zeros(len(x_arr))
        cos_mat = np.cos(np.outer(x_arr, self._log_p))
        return self.epsilon * (cos_mat * self._weights[np.newaxis, :]).sum(axis=1)

    def effective_weight(self) -> float:
        """Peso efectivo total Σ_p (log p/√p) · e^{−p/P}.

        Returns
        -------
        float
            Suma de pesos (sin el factor ε).
        """
        return float(np.sum(self._weights))

    def compare_with_sharp(self, p_sharp: float = 100.0) -> dict:
        """Comparar regularización exponencial con truncación afilada en p_sharp.

        Parameters
        ----------
        p_sharp : float
            Límite de la truncación afilada de referencia.

        Returns
        -------
        dict
            Diccionario con claves:
            ``weight_mellin``, ``weight_sharp_p100``, ``n_primes_mellin``,
            ``n_primes_sharp``, ``mellin_coverage_ratio``.
        """
        is_prime_sharp = _sieve(int(p_sharp))
        primes_sharp = [p for p in range(2, int(p_sharp) + 1) if is_prime_sharp[p]]
        weight_sharp = sum(
            math.log(p) / math.sqrt(p) for p in primes_sharp
        )
        n_sharp = len(primes_sharp)
        w_mellin = self.effective_weight()
        n_mellin = self.n_primes
        return {
            "weight_mellin": w_mellin,
            "weight_sharp_p100": weight_sharp,
            "n_primes_mellin": n_mellin,
            "n_primes_sharp": n_sharp,
            "mellin_coverage_ratio": w_mellin / weight_sharp if weight_sharp > 0 else float("inf"),
        }


# ---------------------------------------------------------------------------
# C) Riemann–Siegel Primos  – ceros auto-generados vía suma Z(t)
# ---------------------------------------------------------------------------

class RiemannSiegelPrimos:
    """Aproxima ψ(x) usando la fórmula explícita con ceros derivados de Z(t).

    Los ceros γ_n se calculan automáticamente detectando cambios de signo de
    Z(t) (con la corrección C₀ de Riemann–Siegel) y refinando con bisección
    (brentq). No se usa ninguna tabla precalculada.

    Después de obtener los ceros γ_n, la fórmula explícita da:
        ψ_RS(x) = x
                  − 2x^{½} Σ_n [(½ cos(γ_n log x) + γ_n sin(γ_n log x))
                                  / (¼ + γ_n²)]

    Parameters
    ----------
    t_max : float
        Límite superior del barrido en t (t_max > 14).
    n_scan : int
        Número de puntos en el barrido inicial de Z(t).
    max_zeros : int
        Número máximo de ceros a retener.
    """

    _T_MIN_FIRST_ZERO: float = 14.0  # Primer cero siempre > 14

    def __init__(
        self,
        t_max: float = 50.0,
        n_scan: int = 500,
        max_zeros: int = 20,
    ) -> None:
        if t_max <= self._T_MIN_FIRST_ZERO:
            raise ValueError(
                f"t_max must be > {self._T_MIN_FIRST_ZERO} to capture the first non-trivial zero"
            )
        self.t_max = float(t_max)
        self.n_scan = int(n_scan)
        self.max_zeros = int(max_zeros)
        self._zeros: Optional[np.ndarray] = None

    # ------------------------------------------------------------------
    # Métodos estáticos: θ y Z públicos
    # ------------------------------------------------------------------

    @staticmethod
    def theta(t: float) -> float:
        """θ(t) exacto de Riemann–Siegel (delega a `_theta_rs`)."""
        return _theta_rs(t)

    @staticmethod
    def Z(t: float) -> float:
        """Z(t) de Riemann–Siegel con corrección C₀ (delega a `_Z_main_sum`)."""
        return _Z_main_sum(t)

    # ------------------------------------------------------------------
    # Cálculo de ceros
    # ------------------------------------------------------------------

    def compute_zeros(self) -> np.ndarray:
        """Calcula los ceros de Z(t) en (14, t_max] mediante barrido + bisección.

        Returns
        -------
        np.ndarray
            Array ordenado de ceros γ_n en (14, t_max].
        """
        # Barrido denso cerca del primer cero (14, 16) + barrido grueso en (16, t_max)
        t_dense = np.linspace(14.01, 16.0, max(200, self.n_scan // 5))
        n_coarse = max(self.n_scan - len(t_dense), 100)
        t_coarse = np.linspace(16.0, self.t_max, n_coarse + 1)[1:]  # excluir 16 duplicado
        t_grid = np.concatenate([t_dense, t_coarse])

        # Evaluar Z en todos los puntos del grid
        z_vals = np.array([_Z_main_sum(t) for t in t_grid])

        zeros: list[float] = []
        for i in range(len(t_grid) - 1):
            if len(zeros) >= self.max_zeros:
                break
            z0, z1 = z_vals[i], z_vals[i + 1]
            # Detectar cambio de signo estricto
            if z0 * z1 < 0.0:
                try:
                    gamma = brentq(
                        _Z_main_sum,
                        t_grid[i],
                        t_grid[i + 1],
                        xtol=1e-6,
                        maxiter=50,
                    )
                    # Evitar duplicados
                    if not zeros or abs(gamma - zeros[-1]) > _ZERO_DUPLICATE_THRESHOLD:
                        zeros.append(gamma)
                except ValueError:
                    pass  # brentq no convergió; ignorar

        return np.array(sorted(zeros))

    @property
    def zeros(self) -> np.ndarray:
        """Ceros de Z(t) (calculados y cacheados en la primera llamada)."""
        if self._zeros is None:
            self._zeros = self.compute_zeros()
        return self._zeros

    # ------------------------------------------------------------------
    # Comparación con referencia
    # ------------------------------------------------------------------

    def zero_error_vs_reference(self) -> dict:
        """Compara ceros calculados con los primeros ceros de referencia conocidos.

        Returns
        -------
        dict
            ``n_computed``: número de ceros calculados.
            ``n_compared``: número de pares comparados.
            ``mae_zeros``: error absoluto medio de los pares.
            ``max_error``: error máximo entre pares.
            ``errors``: array de errores absolutos.
        """
        computed = self.zeros
        n_cmp = min(len(computed), len(_REFERENCE_ZEROS))
        if n_cmp == 0:
            return {
                "n_computed": 0,
                "n_compared": 0,
                "mae_zeros": float("nan"),
                "max_error": float("nan"),
                "errors": np.array([]),
            }
        errors = np.abs(computed[:n_cmp] - _REFERENCE_ZEROS[:n_cmp])
        return {
            "n_computed": len(computed),
            "n_compared": n_cmp,
            "mae_zeros": float(np.mean(errors)),
            "max_error": float(np.max(errors)),
            "errors": errors,
        }

    # ------------------------------------------------------------------
    # ψ_RS(x) mediante fórmula explícita con ceros calculados
    # ------------------------------------------------------------------

    def psi_rs(self, x: float) -> float:
        """Aproximación ψ_RS(x) vía fórmula explícita con ceros RS calculados.

        ψ_RS(x) = x − 2x^{½} Σ_γ [(½ cos(γ log x) + γ sin(γ log x)) / (¼+γ²)]

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            Estimación de ψ(x).
        """
        if x <= 1.0:
            return 0.0
        gammas = self.zeros
        if len(gammas) == 0:
            return x
        log_x = math.log(x)
        sqrt_x = math.sqrt(x)
        osc = float(np.sum(
            (0.5 * np.cos(gammas * log_x) + gammas * np.sin(gammas * log_x))
            / (0.25 + gammas ** 2)
        ))
        return x - 2.0 * sqrt_x * osc

    def psi_rs_array(self, x_arr: np.ndarray) -> np.ndarray:
        """Versión vectorizada de psi_rs.

        Parameters
        ----------
        x_arr : np.ndarray
            Array de puntos de evaluación.

        Returns
        -------
        np.ndarray
            Array de estimaciones ψ_RS(x).
        """
        x_arr = np.asarray(x_arr, dtype=float)
        gammas = self.zeros
        result = np.where(x_arr <= 1.0, 0.0, x_arr)
        mask = x_arr > 1.0
        if not np.any(mask) or len(gammas) == 0:
            return result

        x_m = x_arr[mask]
        log_x = np.log(x_m)            # (M,)
        sqrt_x = np.sqrt(x_m)          # (M,)

        # Matriz de oscilaciones: (M, K)
        G = gammas[np.newaxis, :]       # (1, K)
        L = log_x[:, np.newaxis]        # (M, 1)

        osc = (
            (0.5 * np.cos(G * L) + G * np.sin(G * L))
            / (0.25 + G ** 2)
        ).sum(axis=1)                   # (M,)

        result[mask] = x_m - 2.0 * sqrt_x * osc
        return result

    def mae_vs_exact(
        self,
        x_min: float = 5.0,
        x_max: float = 50.0,
        n_points: int = 50,
    ) -> float:
        """Error absoluto medio de ψ_RS vs ψ exacta en [x_min, x_max].

        Parameters
        ----------
        x_min, x_max : float
            Extremos del intervalo.
        n_points : int
            Número de puntos de evaluación.

        Returns
        -------
        float
            MAE = mean |ψ_RS(x) − ψ(x)|.
        """
        x_arr = np.linspace(x_min, x_max, n_points)
        psi_approx = self.psi_rs_array(x_arr)
        psi_exact = np.array([chebyshev_psi(xi) for xi in x_arr])
        return float(np.mean(np.abs(psi_approx - psi_exact)))


# ---------------------------------------------------------------------------
# Comparador unificado de los tres métodos
# ---------------------------------------------------------------------------

class ComparadorMetodos:
    """Compara los tres métodos frente a ψ exacta en un intervalo dado.

    Parameters
    ----------
    weil_delta : float
        Parámetro δ para WeilFuncionPrueba.
    weil_p_max : float
        Límite de criba para WeilFuncionPrueba.
    mellin_P : float
        Parámetro P para MellinExponencial.
    rs_t_max : float
        Límite t_max para RiemannSiegelPrimos.
    epsilon : float
        Factor ε para MellinExponencial.
    """

    def __init__(
        self,
        weil_delta: float = DELTA_WEIL_DEFAULT,
        weil_p_max: float = 500.0,
        mellin_P: float = P_MELLIN_DEFAULT,
        rs_t_max: float = 50.0,
        epsilon: float = EPSILON_DEFAULT,
    ) -> None:
        self.weil = WeilFuncionPrueba(delta=weil_delta, p_max=weil_p_max)
        self.mellin = MellinExponencial(P=mellin_P, epsilon=epsilon)
        self.rs = RiemannSiegelPrimos(t_max=rs_t_max)

    def comparar(
        self,
        x_min: float = 5.0,
        x_max: float = 50.0,
        n_points: int = 50,
    ) -> dict:
        """Calcula el MAE de cada método frente a ψ exacta.

        Parameters
        ----------
        x_min, x_max : float
            Intervalo de comparación.
        n_points : int
            Número de puntos de evaluación.

        Returns
        -------
        dict
            ``mae_lineal``: MAE del modelo lineal ψ(x) ≈ x.
            ``mae_weil``: MAE de WeilFuncionPrueba.
            ``mae_mellin``: MAE de MellinExponencial (ψ ≈ x + V_mell).
            ``mae_rs``: MAE de RiemannSiegelPrimos.
            ``n_zeros_rs``: número de ceros RS calculados.
            ``mejor_metodo``: método con menor MAE (``"weil"``, ``"mellin"`` o ``"rs"``).
        """
        x_arr = np.linspace(x_min, x_max, n_points)
        psi_exact = np.array([chebyshev_psi(xi) for xi in x_arr])

        mae_lineal = float(np.mean(np.abs(x_arr - psi_exact)))
        mae_weil = float(np.mean(np.abs(self.weil.evaluate_array(x_arr) - psi_exact)))
        mae_mellin = float(np.mean(np.abs(
            (x_arr + self.mellin.evaluate_array(x_arr)) - psi_exact
        )))
        mae_rs = float(np.mean(np.abs(self.rs.psi_rs_array(x_arr) - psi_exact)))

        maes = {"weil": mae_weil, "mellin": mae_mellin, "rs": mae_rs}
        mejor = min(maes, key=maes.__getitem__)

        return {
            "mae_lineal": mae_lineal,
            "mae_weil": mae_weil,
            "mae_mellin": mae_mellin,
            "mae_rs": mae_rs,
            "n_zeros_rs": len(self.rs.zeros),
            "mejor_metodo": mejor,
        }
