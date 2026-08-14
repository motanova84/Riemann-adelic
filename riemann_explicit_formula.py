"""
riemann_explicit_formula.py
Implementación de la fórmula explícita de Riemann mediante sumas de primos.
────────────────────────────────────────────────────────────────────────────
Proporciona herramientas para aproximar ψ(x) = Σ_{p^k ≤ x} log(p) usando:
  - Truncación afilada (SharpTruncatedSum)
  - Suavización gaussiana (SmoothedPrimeSum)
  - Estimación de cola via PNT (PNTTailEstimate)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""
from __future__ import annotations

import math
from typing import Optional

import numpy as np
from scipy.special import ndtr  # Normal CDF = Φ

# ---------------------------------------------------------------------------
# Helpers: cribado de números primos y potencias de primos
# ---------------------------------------------------------------------------

def _sieve(n: int) -> list[bool]:
    """Criba de Eratóstenes; devuelve lista bool de longitud n+1."""
    if n < 2:
        return [False] * (n + 1)
    is_prime = bytearray([1]) * (n + 1)
    is_prime[0] = is_prime[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if is_prime[i]:
            is_prime[i * i :: i] = bytearray(len(is_prime[i * i :: i]))
    return list(map(bool, is_prime))


def _prime_powers_up_to(x: float) -> list[tuple[float, float]]:
    """Devuelve lista de (p^k, log p) para todas las potencias de primo p^k ≤ x."""
    n = int(x)
    if n < 2:
        return []
    is_prime = _sieve(n)
    result: list[tuple[float, float]] = []
    for p in range(2, n + 1):
        if not is_prime[p]:
            continue
        logp = math.log(p)
        pk = p
        while pk <= n:
            result.append((float(pk), logp))
            pk *= p
    return result


# ---------------------------------------------------------------------------
# Función de Chebyshev ψ(x)
# ---------------------------------------------------------------------------

def chebyshev_psi(x: float) -> float:
    """Función de Chebyshev  ψ(x) = Σ_{p^k ≤ x} log p.

    Parameters
    ----------
    x : float
        Argumento real positivo.

    Returns
    -------
    float
        ψ(x) calculada mediante criba exacta.
    """
    if x <= 1.0:
        return 0.0
    return sum(logp for _, logp in _prime_powers_up_to(x))


# ---------------------------------------------------------------------------
# A) SharpTruncatedSum – truncación afilada en P
# ---------------------------------------------------------------------------

class SharpTruncatedSum:
    """Aproxima ψ(x) mediante la suma oscilatoria con truncación afilada.

    La suma truncada es:
        V_sharp(x) = Σ_{p ≤ P} (log p / √p) · cos(x · log p)

    y la aproximación completa es ψ(x) ≈ x + V_sharp(x).

    Parameters
    ----------
    P : float
        Límite superior de truncación (todos los primos p ≤ P).
    """

    def __init__(self, P: float = 100.0) -> None:
        if P < 2:
            raise ValueError("P must be >= 2")
        self.P = float(P)
        is_prime = _sieve(int(P))
        self._primes = np.array(
            [p for p in range(2, int(P) + 1) if is_prime[p]], dtype=float
        )

    @property
    def n_primes(self) -> int:
        """Número de primos en [2, P]."""
        return len(self._primes)

    def evaluate(self, x: float) -> float:
        """Corrección oscilatoria V_sharp(x).

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            V_sharp(x) = Σ_{p ≤ P} (log p / √p) · cos(x · log p).
        """
        if len(self._primes) == 0:
            return 0.0
        log_p = np.log(self._primes)
        weights = log_p / np.sqrt(self._primes)
        return float(np.sum(weights * np.cos(x * log_p)))

    def evaluate_array(self, x_arr: np.ndarray) -> np.ndarray:
        """Versión vectorizada de evaluate."""
        if len(self._primes) == 0:
            return np.zeros(len(x_arr))
        log_p = np.log(self._primes)
        weights = log_p / np.sqrt(self._primes)
        # x_arr: (N,), log_p: (M,) → outer product
        return (weights[np.newaxis, :] * np.cos(np.outer(x_arr, log_p))).sum(axis=1)


# ---------------------------------------------------------------------------
# B) SmoothedPrimeSum – suavización gaussiana
# ---------------------------------------------------------------------------

class SmoothedPrimeSum:
    """Suavización gaussiana de la suma de potencias de primos.

    La suma suavizada es:
        ψ_δ(x) = Σ_{p^k} log(p) · Φ((x - p^k) / δ)

    donde Φ es la CDF normal estándar y δ es el ancho de suavización.

    Parameters
    ----------
    delta : float
        Ancho de suavización (σ del gaussiano).
    p_max : float
        Límite máximo para la criba de potencias de primos.
    """

    def __init__(self, delta: float = 0.5, p_max: float = 500.0) -> None:
        if delta <= 0:
            raise ValueError("delta must be positive")
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

    def evaluate(self, x: float) -> float:
        """ψ_δ(x) suavizada.

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            ψ_δ(x).
        """
        if len(self._pk) == 0:
            return 0.0
        return float(np.sum(self._logp * ndtr((x - self._pk) / self.delta)))

    def evaluate_array(self, x_arr: np.ndarray) -> np.ndarray:
        """Versión vectorizada de evaluate."""
        if len(self._pk) == 0:
            return np.zeros(len(x_arr))
        # (N, M) matrix of Φ values
        z = (x_arr[:, np.newaxis] - self._pk[np.newaxis, :]) / self.delta
        return (self._logp[np.newaxis, :] * ndtr(z)).sum(axis=1)


# ---------------------------------------------------------------------------
# C) PNTTailEstimate – estimación de la cola via PNT
# ---------------------------------------------------------------------------

class PNTTailEstimate:
    """Estimación del error de cola de ψ(x) − x usando el PNT clásico.

    Bajo la hipótesis de Riemann, el error satisface:
        |ψ(x) − x| ≤ C · √x · (log x)²

    Esta clase proporciona cota explícita y estimación numérica.

    Parameters
    ----------
    C : float
        Constante en la cota del error (por defecto conservadora = 1.0).
    """

    def __init__(self, C: float = 1.0) -> None:
        if C <= 0:
            raise ValueError("C must be positive")
        self.C = float(C)

    def bound(self, x: float) -> float:
        """Cota superior |ψ(x) − x| ≤ C · √x · (log x)².

        Parameters
        ----------
        x : float
            Punto de evaluación (x > 1).

        Returns
        -------
        float
            Cota del error.
        """
        if x <= 1.0:
            return 0.0
        return self.C * math.sqrt(x) * math.log(x) ** 2

    def relative_error_bound(self, x: float) -> float:
        """Cota relativa |ψ(x)/x − 1| ≤ C · (log x)² / √x."""
        if x <= 1.0:
            return float("inf")
        return self.C * math.log(x) ** 2 / math.sqrt(x)

    def estimate_error(self, x: float) -> float:
        """Estimación empírica |ψ(x) − x| calculando ψ exacta.

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            |ψ(x) − x| calculado con criba exacta.
        """
        return abs(chebyshev_psi(x) - x)
