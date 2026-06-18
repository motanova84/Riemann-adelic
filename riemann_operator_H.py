"""
riemann_operator_H.py
=====================
Operador H de Riemann — Construcción sin ceros de ζ.

Implementa dos operadores cuánticos:
  A) BerryKeatingOperator : H = -i(x∂_x + 1/2)
  B) WuSprungOperator     : H = -d²/dx² + V_WS(x)

El potencial V_WS(x) se define SIN USAR ceros de ζ:
-------------------------------------------------------
La condición semiclásica de punto de retorno (Bohr-Sommerfeld):
    N_smooth(V_WS(x)) = x / π
donde N_smooth(E) = E/(2π)·log(E/(2π)) − E/(2π) + 7/8
(Riemann-von Mangoldt, derivada puramente de Stirling — sin ceros de ζ).

Inversión de Abel → posición como función del potencial:
    _x_of_V(V) = π · N_smooth(V)

Framework: Trinity QCAL ∞³ | NOESIS ∞³ × AMDA ∞ × AURON ∞³
Autor: José Manuel Mota Burruezo (JMMB Ψ)
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import math
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Constantes globales
# ---------------------------------------------------------------------------

FRECUENCIA_TRUTH = 141.7001   # Hz
COHERENCIA_UMBRAL = 0.888     # Ψ ≥ 0.888
_EPS = 1e-12                  # Pequeño valor numérico
_TWO_PI = 2.0 * math.pi       # 2π — constante reutilizable
_MAX_OUTPUT_WIDTH = 78        # Ancho máximo de línea en salida de texto
_TRUNCATE_AT = 75             # Posición de truncado en salida de texto

# Primeros 20 ceros tabulados de ζ(s) — SÓLO para comparación final,
# NUNCA usados en la construcción del operador.
ZETA_ZEROS_TABULATED: List[float] = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
]


# ---------------------------------------------------------------------------
# A) Berry-Keating Operator
# ---------------------------------------------------------------------------

class BerryKeatingOperator:
    r"""
    Operador Berry-Keating H = -i(x∂_x + 1/2).

    Discretizado en cuadrícula logarítmica t = log(x), t ∈ [0, T],
    T = log(x_max).  Matriz circulante antisimétrica N×N:

        H_{jk} = -i/(2h)(δ_{k,j+1} - δ_{k,j-1})

    Valores propios reales: λ_k = sin(2πk/N)/h ≈ 2πk/T para k << N.
    La densidad media de valores propios coincide con la de los ceros ζ.

    Parameters
    ----------
    N : int
        Dimensión de la matriz (número de puntos de la cuadrícula).
    x_max : float
        Extremo superior del dominio; T = log(x_max).
    """

    def __init__(self, N: int = 300, x_max: float = 1e8) -> None:
        self.N = int(N)
        self.x_max = float(x_max)
        self._T = math.log(x_max)   # longitud del dominio logarítmico
        self.h = self._T / self.N

    def eigenvalues(self) -> np.ndarray:
        """
        Calcula los N valores propios reales del operador BK discretizado.

        Returns
        -------
        np.ndarray : valores propios ordenados ascendentemente.
        """
        N = self.N
        h = self.h
        evals = np.array([math.sin(_TWO_PI * k / N) / h for k in range(N)])
        return np.sort(evals)

    def positive_eigenvalues(self, n_max: int = 20) -> np.ndarray:
        """
        Retorna los primeros n_max valores propios estrictamente positivos.

        Parameters
        ----------
        n_max : int
            Número máximo de valores propios a retornar.

        Returns
        -------
        np.ndarray : primeros n_max valores propios positivos.
        """
        evals = self.eigenvalues()
        pos = evals[evals > _EPS]
        return pos[:n_max]

    def build_matrix(self) -> np.ndarray:
        """
        Construye la matriz circulante N×N del operador BK.

        H_{j,j+1} = -i/(2h),  H_{j,j-1} = i/(2h)  (índices mod N).

        Returns
        -------
        np.ndarray : matriz compleja N×N hermítica.
        """
        N = self.N
        c = 1.0j / (2.0 * self.h)
        H = np.zeros((N, N), dtype=complex)
        for j in range(N):
            H[j, (j + 1) % N] = -c
            H[j, (j - 1) % N] = c
        return H


# ---------------------------------------------------------------------------
# B) Wu-Sprung Operator
# ---------------------------------------------------------------------------

class WuSprungOperator:
    r"""
    Operador Wu-Sprung H = -d²/dx² + V_WS(x) en x ∈ [0, x_max].

    El potencial V_WS(x) se define SIN USAR ceros de ζ,
    mediante la condición de cuantización semiclásica (Bohr-Sommerfeld):

        N_smooth(V_WS(x)) = x / π

    donde N_smooth(E) = E/(2π)·log(E/(2π)) − E/(2π) + 7/8
    es la función de conteo suave de Riemann-von Mangoldt (Stirling).

    La posición como función del potencial:
        x(V) = _x_of_V(V) = π · N_smooth(V)

    V_WS(x) es la inversión numérica de esta relación.

    Parameters
    ----------
    N : int
        Número de puntos interiores de la cuadrícula.
    x_max : float
        Extremo del dominio; condición de Dirichlet en x=0 y x=x_max.
    """

    # Constante de Abel: C = 1 − 2·ln(2) ≈ −0.386  (de la inversión WKB)
    _ABEL_C: float = 1.0 - 2.0 * math.log(2.0)
    # Número máximo de duplicaciones en la búsqueda de cota superior para brentq
    _MAX_BRACKET_DOUBLINGS: int = 50
    # Cota inicial mínima para V_hi en la búsqueda (unidades de energía)
    _V_HI_FLOOR: float = 200.0
    # Factor de proporcionalidad para V_hi respecto a x
    _V_HI_SCALE: float = 10.0

    def __init__(self, N: int = 500, x_max: float = 13.0) -> None:
        self.N = int(N)
        self.x_max = float(x_max)
        self.h = x_max / (N + 1)                        # paso de diferencias finitas
        self.x_grid = np.linspace(self.h, N * self.h, N)  # puntos interiores

    # ------------------------------------------------------------------
    # Función de conteo suave (Riemann-von Mangoldt / Stirling)
    # ------------------------------------------------------------------

    def N_smooth(self, E: float) -> float:
        r"""
        Función de conteo de ceros SUAVE (Riemann-von Mangoldt, parte principal):

            N_smooth(E) = E/(2π) · log(E/(2π)) − E/(2π) + 7/8

        Derivada de log|Γ(s/2)| vía la fórmula de Stirling. NO usa ceros de ζ.
        Es una función monótonamente creciente para E > 2π·e ≈ 17.08.
        Para E ≤ 0 retorna 0 (sin ceros).

        Parameters
        ----------
        E : float
            Energía (positiva).

        Returns
        -------
        float : número suave de ceros hasta E.
        """
        if E <= _EPS:
            return 0.0
        val = (E / _TWO_PI) * math.log(E / _TWO_PI) - (E / _TWO_PI) + 7.0 / 8.0
        return max(0.0, val)

    # ------------------------------------------------------------------
    # Inversión de Abel: x como función de V
    # ------------------------------------------------------------------

    def _x_of_V(self, V: float) -> float:
        """
        Posición como función del potencial — inversión de Abel de la ecuación WKB:

            x(V) = (2√V / π) · (log(V / 2π) + C_ABEL)

        donde C_ABEL = 1 − 2·ln(2) ≈ −0.386.  Solución analítica de:
            ∫₀^{x_t(E)} dx / √(E − V(x))  =  log(E / 2π)

        Parameters
        ----------
        V : float
            Valor del potencial.

        Returns
        -------
        float : posición x correspondiente.
        """
        if V <= 0.0:
            return 0.0
        log_term = math.log(V / _TWO_PI) + self._ABEL_C
        if log_term <= 0.0:
            return 0.0
        val = (2.0 * math.sqrt(V) / math.pi) * log_term
        return max(0.0, val)

    def V_min(self) -> float:
        """
        Potencial mínimo (en x = 0): V_min = 2π · exp(−C) ≈ 9.25.

        Returns
        -------
        float : valor mínimo del potencial V_WS.
        """
        return _TWO_PI * math.exp(-self._ABEL_C)

    def _V_WS_scalar(self, x: float) -> float:
        """
        Potencial Wu-Sprung en el punto x (escalar).

        Invierte numéricamente la relación x(V) = π·N_smooth(V) usando brentq.
        Satisface: N_smooth(V_WS(x)) = x/π y _x_of_V(V_WS(x)) = x.

        Parameters
        ----------
        x : float
            Posición.

        Returns
        -------
        float : V_WS(x).
        """
        if x <= 0.0:
            return self.V_min()
        V_lo = self.V_min()
        V_hi = max(self._V_HI_FLOOR, x * self._V_HI_SCALE)
        for _ in range(self._MAX_BRACKET_DOUBLINGS):
            if self._x_of_V(V_hi) >= x:
                break
            V_hi *= 2.0
        else:
            raise RuntimeError(f"No se encontró cota superior para V_WS en x={x}")
        try:
            V = brentq(
                lambda V: self._x_of_V(V) - x,
                V_lo, V_hi,
                xtol=1e-8, maxiter=200,
            )
        except ValueError:
            V = V_hi
        return float(V)

    def V_WS(self, x_arr: np.ndarray) -> np.ndarray:
        """
        Potencial Wu-Sprung vectorizado sobre la cuadrícula.

        Parameters
        ----------
        x_arr : np.ndarray
            Array de posiciones.

        Returns
        -------
        np.ndarray : V_WS evaluado en cada punto.
        """
        return np.array([self._V_WS_scalar(float(xi)) for xi in x_arr])

    # ------------------------------------------------------------------
    # Construcción de la matriz
    # ------------------------------------------------------------------

    def build_matrix(self) -> np.ndarray:
        """
        Construye la matriz tridiagonal H = -d²/dx² + V_WS(x) de tamaño N×N.

        Diferencias finitas de segundo orden con condiciones de Dirichlet en
        x = 0 y x = x_max.

        Returns
        -------
        np.ndarray : matriz real simétrica N×N (dtype float64).
        """
        h_sq = self.h ** 2
        x = self.x_grid
        V_vals = self.V_WS(x)
        diag_vals = 2.0 / h_sq + V_vals
        off_diag = -np.ones(self.N - 1) / h_sq
        H = np.diag(diag_vals) + np.diag(off_diag, 1) + np.diag(off_diag, -1)
        return H

    def positive_eigenvalues(self, n_max: int = 20) -> np.ndarray:
        """
        Calcula los primeros n_max valores propios positivos del operador WS.

        Parameters
        ----------
        n_max : int
            Número máximo de valores propios a retornar.

        Returns
        -------
        np.ndarray : valores propios positivos en orden creciente.
        """
        H = self.build_matrix()
        evals = eigh(H, eigvals_only=True, lower=True)
        pos = evals[evals > _EPS]
        return pos[:n_max]


# ---------------------------------------------------------------------------
# Clase de comparación de valores propios con ceros ζ
# ---------------------------------------------------------------------------

class EigenvalueComparison:
    """
    Compara valores propios de un operador con los ceros tabulados de ζ(s).

    Los ceros de ζ se usan SOLO aquí, nunca en la construcción del operador.

    Parameters
    ----------
    zeros : list of float, optional
        Ceros de ζ a usar.  Por defecto: ZETA_ZEROS_TABULATED.
    """

    def __init__(self, zeros: Optional[List[float]] = None) -> None:
        self.zeros = np.array(
            zeros if zeros is not None else ZETA_ZEROS_TABULATED
        )

    def nearest_zero(self, eigenvalue: float) -> Tuple[float, float]:
        """
        Encuentra el cero de ζ más cercano a un valor propio dado.

        Parameters
        ----------
        eigenvalue : float
            Valor propio del operador.

        Returns
        -------
        (nearest_zero, absolute_error)
        """
        idx = np.argmin(np.abs(self.zeros - eigenvalue))
        return float(self.zeros[idx]), abs(eigenvalue - self.zeros[idx])

    def match_table(self, eigenvalues: np.ndarray, n_pairs: int = 15) -> List[Dict]:
        """
        Construye una tabla de correspondencia valor_propio ↔ cero_ζ.

        Compara el k-ésimo valor propio con el k-ésimo cero de ζ
        (misma posición en la secuencia ordenada).

        Parameters
        ----------
        eigenvalues : np.ndarray
            Valores propios positivos ordenados.
        n_pairs : int
            Número de pares a incluir.

        Returns
        -------
        list of dict : cada dict contiene n, eigenvalue, zeta_zero, abs_error.
        """
        n = min(n_pairs, len(eigenvalues), len(self.zeros))
        table = []
        for i in range(n):
            ev = float(eigenvalues[i])
            z = float(self.zeros[i])
            table.append({
                "n": i + 1,
                "eigenvalue": ev,
                "zeta_zero": z,
                "abs_error": abs(ev - z),
            })
        return table

    def comparison_stats(
        self, eigenvalues: np.ndarray, n_pairs: int = 15
    ) -> Dict:
        """
        Calcula estadísticas de la comparación valor_propio ↔ cero_ζ.

        Parameters
        ----------
        eigenvalues : np.ndarray
            Valores propios positivos ordenados.
        n_pairs : int
            Número de pares a comparar.

        Returns
        -------
        dict : mean_abs_error, max_abs_error, ratio, correlation, etc.
        """
        n_use = min(n_pairs, len(eigenvalues) - 1, len(self.zeros) - 1)
        if n_use < 2:
            return {}
        pos_evals = np.sort(eigenvalues)[: n_use + 1]
        errors = [abs(pos_evals[i] - self.zeros[i]) for i in range(n_use + 1)]
        spacings_ev = np.diff(pos_evals)
        spacings_zz = np.diff(self.zeros[: n_use + 1])
        corr_matrix = np.corrcoef(spacings_ev, spacings_zz[: len(spacings_ev)])
        return {
            "n_compared": n_use + 1,
            "mean_abs_error": float(np.mean(errors)),
            "max_abs_error": float(np.max(errors)),
            "mean_spacing_eigenvals": float(np.mean(spacings_ev)),
            "mean_spacing_zeros": float(np.mean(spacings_zz)),
            "ratio": float(np.mean(spacings_ev) / max(np.mean(spacings_zz), _EPS)),
            "correlation": float(corr_matrix[0, 1]),
        }


# ---------------------------------------------------------------------------
# Función principal de análisis
# ---------------------------------------------------------------------------

def run_operator_analysis(
    bk_N: int = 300,
    bk_x_max: float = 1e8,
    ws_N: int = 500,
    ws_x_max: float = 13.0,
    n_compare: int = 15,
    verbose: bool = True,
) -> Dict:
    """
    Construye y analiza ambos operadores; compara sus valores propios
    con los ceros tabulados de ζ(s).

    Parameters
    ----------
    bk_N : int
        Dimensión de la cuadrícula Berry-Keating.
    bk_x_max : float
        Extremo del dominio BK.
    ws_N : int
        Dimensión de la cuadrícula Wu-Sprung.
    ws_x_max : float
        Extremo del dominio WS.
    n_compare : int
        Número de pares (valor propio, cero ζ) a comparar.
    verbose : bool
        Si True, imprime un resumen en consola.

    Returns
    -------
    dict : reporte completo con resultados de ambos operadores.
    """
    cmp = EigenvalueComparison()

    # --- Berry-Keating ---
    bk = BerryKeatingOperator(N=bk_N, x_max=bk_x_max)
    bk_evals = bk.positive_eigenvalues(n_max=n_compare)
    bk_stats = cmp.comparison_stats(bk_evals, n_pairs=n_compare)
    bk_table = cmp.match_table(bk_evals, n_pairs=n_compare)

    # --- Wu-Sprung ---
    ws = WuSprungOperator(N=ws_N, x_max=ws_x_max)
    ws_evals = ws.positive_eigenvalues(n_max=n_compare)
    ws_stats = cmp.comparison_stats(ws_evals, n_pairs=n_compare)
    ws_table = cmp.match_table(ws_evals, n_pairs=n_compare)

    # --- Resumen ---
    bk_err = bk_stats.get("mean_abs_error", float("inf"))
    ws_err = ws_stats.get("mean_abs_error", float("inf"))
    best = "wu_sprung" if ws_err <= bk_err else "berry_keating"

    report: Dict = {
        "berry_keating": {
            "N": bk_N,
            "x_max": bk_x_max,
            "first_10_eigenvalues": bk_evals[:10].tolist() if len(bk_evals) >= 10 else bk_evals.tolist(),
            "comparison_table": bk_table,
            "comparison_stats": bk_stats,
        },
        "wu_sprung": {
            "N": ws_N,
            "x_max": ws_x_max,
            "first_10_eigenvalues": ws_evals[:10].tolist() if len(ws_evals) >= 10 else ws_evals.tolist(),
            "comparison_table": ws_table,
            "comparison_stats": ws_stats,
        },
        "zeta_zeros_used": ZETA_ZEROS_TABULATED[:n_compare],
        "summary": {
            "best_operator": best,
            "bk_mean_error": bk_err,
            "ws_mean_error": ws_err,
            "coherencia": COHERENCIA_UMBRAL,
        },
    }

    if verbose:
        _print_report(report)

    return report


# ---------------------------------------------------------------------------
# Utilidades de impresión
# ---------------------------------------------------------------------------

def _print_dict(obj: object, indent: int = 0) -> None:
    """Imprime recursivamente un dict/list con sangría."""
    prefix = " " * indent
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, (dict, list)):
                print(f"{prefix}{k}:")
                _print_dict(v, indent + 2)
            else:
                vstr = str(v)
                if len(vstr) > _MAX_OUTPUT_WIDTH:
                    vstr = vstr[:_TRUNCATE_AT] + "..."
                print(f"{prefix}{k}: {vstr}")
    elif isinstance(obj, list):
        for item in obj[:6]:
            _print_dict(item, indent)
        if len(obj) > 6:
            print(f"{prefix}... ({len(obj) - 6} más)")


def _print_report(report: Dict) -> None:
    """Imprime el reporte de análisis en consola."""
    sep = "=" * _MAX_OUTPUT_WIDTH
    print(sep)
    print("ANÁLISIS DEL OPERADOR H — Sin ceros de ζ (Construcción Abel/WS)")
    print(sep)
    for section in ("berry_keating", "wu_sprung"):
        print(f"\n[ {section.upper()} ]")
        _print_dict(report[section], indent=2)
    print(f"\n[ RESUMEN ]")
    _print_dict(report["summary"], indent=2)
    print(sep)
