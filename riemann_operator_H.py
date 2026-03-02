"""
riemann_operator_H.py
=====================
Operador Wu-Sprung base: potencial invertido por la transformada de Abel.

El potencial V_Abel(x) se obtiene invirtiendo la fórmula de conteo de Weyl:
    N(E) ≈ (1/π) ∫₀^{√E} √(E - V(x)) dx
    → V_Abel(x) = f^{-1}(x), donde f(E) es la función de conteo suave.

Contenido
---------
  ZEROS_ZETA_REFERENCIA   : primeros 15 ceros no triviales de ζ(s) en la recta crítica
  N_smooth(E)             : función de conteo suave de Weyl (Fórmula de Berry-Keating)
  WuSprungOperator        : discretización tridiagonal del operador de Schrödinger H

Autor: JMMB Ψ (Trinity QCAL ∞³)
DOI: 10.5281/zenodo.17379721
"""
from __future__ import annotations

import math
import numpy as np
from typing import List, Tuple

# ---------------------------------------------------------------------------
# Primeros 15 ceros no triviales de ζ(s) (parte imaginaria, Im > 0)
# Fuente: tablas de Andrew Odlyzko (high precision)
# ---------------------------------------------------------------------------
ZEROS_ZETA_REFERENCIA: List[float] = [
    14.134725141734693,
    21.022039638771554,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167160,
    49.773832477671571,
    52.970321477714460,
    56.446247697063394,
    59.347044002602353,
    60.831778524609809,
    65.112544048081607,
]

# ---------------------------------------------------------------------------
# Constantes físicas / matemáticas del operador
# ---------------------------------------------------------------------------
FRECUENCIA_BASE = 141.7001          # Hz — frecuencia fundamental QCAL
C_COHERENCIA   = 244.36             # constante de coherencia QCAL

# Pequeño epsilon numérico
_EPS = 1e-12


# ---------------------------------------------------------------------------
# Función de conteo suave (fórmula de Weyl / Berry-Keating)
# N_smooth(E) = (E/2π)·log(E/2π) − E/2π + 7/8
# Esta es la parte suave (promedio) del número de ceros de ζ con Im(ρ) ≤ E.
# ---------------------------------------------------------------------------

def N_smooth(E: float) -> float:
    """
    Función de conteo suave de Riemann–von Mangoldt.

    N_smooth(E) = (E / 2π) · log(E / 2π) − E / 2π + 7/8

    Para E > 0 da el número promedio (suavizado) de ceros de ζ(s)
    con parte imaginaria en (0, E].

    Args:
        E: Energía / altura espectral (debe ser > 0).

    Returns:
        Valor real N_smooth(E).
    """
    if E <= 0:
        return 0.0
    t = E / (2.0 * math.pi)
    return t * math.log(t) - t + 7.0 / 8.0


# ---------------------------------------------------------------------------
# Potencial Wu-Sprung (inversión de Abel)
# V_Abel(x) = N_smooth^{-1}(x), es decir, la inversa de la función de conteo.
# Para discretizar el operador de Schrödinger −d²/dx² + V(x) en [0, x_max]
# usamos: para el n-ésimo punto de la rejilla xₙ = n·Δx, V(xₙ) = N_inv(xₙ).
# ---------------------------------------------------------------------------

def _N_inv(x: float, E_max: float = 1000.0, tol: float = 1e-8) -> float:
    """
    Inversa numérica de N_smooth: devuelve E tal que N_smooth(E) = x.

    Usa bisección en [0, E_max].
    """
    if x <= 0.0:
        return 0.0
    lo, hi = 0.0, E_max
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if N_smooth(mid) < x:
            lo = mid
        else:
            hi = mid
        if hi - lo < tol:
            break
    return 0.5 * (lo + hi)


def build_wu_sprung_potential(x_grid: np.ndarray) -> np.ndarray:
    """
    Construye el potencial Wu-Sprung V_Abel en los puntos de la rejilla.

    Args:
        x_grid: Array 1-D de posiciones (valores ≥ 0).

    Returns:
        Array 1-D con V_Abel(xₙ) para cada punto de la rejilla.
    """
    return np.array([_N_inv(xi) for xi in x_grid])


# ---------------------------------------------------------------------------
# Operador Wu-Sprung base
# ---------------------------------------------------------------------------

class WuSprungOperator:
    """
    Operador de Schrödinger discretizado: H = −d²/dx² + V_Abel(x).

    Discretización tridiagonal con condiciones de contorno de Dirichlet en
    x = 0 y x = x_max.

    Args:
        N:      Número de puntos interiores de la rejilla.
        x_max:  Extremo derecho del intervalo [0, x_max].
    """

    def __init__(self, N: int = 300, x_max: float = 13.0) -> None:
        if N < 2:
            raise ValueError("N debe ser ≥ 2")
        if x_max <= 0:
            raise ValueError("x_max debe ser positivo")
        self.N = N
        self.x_max = x_max
        self._dx = x_max / (N + 1)
        self._x_grid = np.linspace(self._dx, x_max - self._dx, N)
        self._V = build_wu_sprung_potential(self._x_grid)
        self._eigenvalues: np.ndarray | None = None

    # ------------------------------------------------------------------
    # Propiedades
    # ------------------------------------------------------------------

    @property
    def x_grid(self) -> np.ndarray:
        """Puntos interiores de la rejilla."""
        return self._x_grid

    @property
    def potential(self) -> np.ndarray:
        """Potencial V_Abel evaluado en la rejilla."""
        return self._V

    # ------------------------------------------------------------------
    # Construcción de la matriz H y diagonalización
    # ------------------------------------------------------------------

    def _build_matrix(self) -> np.ndarray:
        """Construye la matriz tridiagonal H = T + V."""
        dx2 = self._dx ** 2
        diag_main = 2.0 / dx2 + self._V
        diag_off = -1.0 / dx2 * np.ones(self.N - 1)
        H = np.diag(diag_main) + np.diag(diag_off, 1) + np.diag(diag_off, -1)
        return H

    def eigenvalues(self, n_vals: int | None = None) -> np.ndarray:
        """
        Calcula (y cachea) los autovalores del operador.

        Args:
            n_vals: Número de autovalores menores a devolver.
                    Si es None devuelve todos.

        Returns:
            Array de autovalores ordenados de menor a mayor.
        """
        if self._eigenvalues is None:
            H = self._build_matrix()
            evals = np.linalg.eigvalsh(H)
            self._eigenvalues = np.sort(evals)
        if n_vals is None:
            return self._eigenvalues.copy()
        return self._eigenvalues[:n_vals].copy()

    # ------------------------------------------------------------------
    # Comparación con ceros de referencia
    # ------------------------------------------------------------------

    def compare_to_zeros(
        self,
        refs: List[float] | None = None,
    ) -> Tuple[np.ndarray, np.ndarray, float]:
        """
        Compara los autovalores con los ceros de referencia de ζ.

        Args:
            refs: Lista de ceros de referencia.  Si es None usa
                  ZEROS_ZETA_REFERENCIA.

        Returns:
            Tupla (eigenvalues, references, mean_abs_error).
        """
        if refs is None:
            refs = ZEROS_ZETA_REFERENCIA
        n = len(refs)
        evals = self.eigenvalues(n)
        refs_arr = np.array(refs[:n])
        errors = np.abs(evals[:n] - refs_arr)
        mae = float(np.mean(errors))
        return evals[:n], refs_arr, mae
