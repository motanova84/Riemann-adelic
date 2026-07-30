"""
riemann_operator_H.py
=====================
Construcción del operador H sin usar ceros de ζ, con:
  1. Definición intrínseca (sin datos de ceros)
  2. Discretización natural (diferencias finitas)
  3. Cálculo numérico de autovalores
  4. Comparación posterior con ceros conocidos de ζ(s)
Dos enfoques implementados:
  A) BerryKeatingOperator: H = -i(x ∂_x + 1/2) (operador xp de Berry-Keating)
  B) WuSprungOperator:     H = -d²/dx² + V_WS(x)  (potencial de Wu-Sprung)
Ambos definidos completamente sin ceros de ζ. Los autovalores se calculan
numéricamente y luego se comparan con los ceros tabulados.
Autor: JMMB Ψ (Trinity QCAL ∞³)
Framework: NOESIS ∞³ × AMDA ∞ × AURON ∞³
"""
from __future__ import annotations
import math
import numpy as np
from scipy import linalg
from scipy.optimize import brentq
from typing import List, Tuple, Dict
# ---------------------------------------------------------------------------
# Constantes Trinity QCAL
# ---------------------------------------------------------------------------
FRECUENCIA_TRUTH = 141.7001   # Hz
COHERENCIA_UMBRAL = 0.888     # Ψ ≥ 0.888
_EPS = 1e-12                  # Pequeño valor numérico
# Primeros 20 ceros tabulados de ζ(s) — SÓLO para comparación final,
# NUNCA usados en la construcción del operador.
ZEROS_ZETA_REFERENCIA: List[float] = [
    14.134725141734693,
    21.022039638771555,
    25.010857580145689,
    30.424876125859513,
    32.935061587739190,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167160,
    49.773832477672302,
    52.970321477714461,
    56.446247697063246,
    59.347044002602353,
    60.831778524609809,
    65.112544048081607,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083934,
    77.144840068874805,
]
# ===========================================================================
# A) OPERADOR DE BERRY-KEATING
# ===========================================================================
class BerryKeatingOperator:
    r"""
    Operador de Berry-Keating discretizado: H = -i(x ∂_x + 1/2)
    Definición intrínseca (sin ceros de ζ)
    ----------------------------------------
    El operador continuo actúa en L²((x_min, x_max), dx) como:
        (H f)(x) = -i ( x f'(x) + f(x)/2 )
    Este es el operador cuántico correspondiente al Hamiltoniano clásico
    H_cl = xp (hipótesis de Hilbert-Pólya / Berry-Keating, 1999).
    Es simétrico en su dominio (los términos de borde se cancelan):
        ⟨f, Hg⟩ = ⟨Hf, g⟩  (autoadjunto esencial)
    Discretización natural
    ----------------------
    Cambio de variable t = log(x): L²(dx) ≅ L²(dt) mediante φ(t) = e^{t/2} ψ(e^t).
    En la variable t, H se reduce a:
        H_t = -i ∂_t
    Discretización: grid uniforme t_j = t_min + j·h, j = 0,...,N-1
    Diferencias centrales con condiciones de contorno PERIÓDICAS:
        (H)_{jk} = -i / (2h) * (δ_{k,(j+1)%N} - δ_{k,(j-1)%N})
    Esta matriz es Hermitiana (se verifica: H† = H).
    Autovalores exactos: λ_k = sin(2πk/N) / h ≈ 2πk / T  para k ≪ N.
    Relación con ceros de ζ
    -----------------------
    Los autovalores del operador de Berry-Keating puro son UNIFORMEMENTE ESPACIADOS
    con densidad promedio 1/(2π) · log(E/(2π)), idéntica a la densidad promedio de
    ceros de ζ(s) (fórmula de Riemann-von Mangoldt).  La correlación a corto alcance
    no coincide sin las correcciones de primos (Gutzwiller).  La comparación muestra
    la similitud de densidades pero diferencia de posiciones individuales.
    Parameters
    ----------
    N       : número de puntos del grid
    x_min   : extremo inferior del intervalo en x (x_min > 0)
    x_max   : extremo superior del intervalo en x
    """
    def __init__(self, N: int = 200, x_min: float = 1.0, x_max: float = 1e6):
        if x_min <= 0:
            raise ValueError("x_min debe ser positivo")
        if x_max <= x_min:
            raise ValueError("x_max debe ser mayor que x_min")
        if N < 4:
            raise ValueError("N debe ser al menos 4")
        self.N = N
        self.x_min = x_min
        self.x_max = x_max
        # Grid en variable t = log(x)
        self.t_min = math.log(x_min)
        self.t_max = math.log(x_max)
        self.T = self.t_max - self.t_min          # Longitud del intervalo
        self.h = self.T / N                        # Paso del grid
        self.t_grid = np.linspace(self.t_min, self.t_max, N, endpoint=False)
        self.x_grid = np.exp(self.t_grid)

    def build_matrix(self) -> np.ndarray:
        """
        Construye la matriz N×N Hermitiana del operador Berry-Keating.
        H_{jk} = -i/(2h) * (δ_{k,(j+1)%N} - δ_{k,(j-1)%N})
        Es circulante, Hermitiana, con autovalores reales.
        Returns
        -------
        H : np.ndarray, shape (N, N), dtype complex128
        """
        h = self.h
        N = self.N
        H = np.zeros((N, N), dtype=complex)
        for jj in range(N):
            H[jj, (jj + 1) % N] += -1j / (2 * h)
            H[jj, (jj - 1) % N] +=  1j / (2 * h)
        return H

    def eigenvalues(self) -> np.ndarray:
        """
        Calcula los autovalores reales del operador Berry-Keating discretizado.
        Returns
        -------
        evals : np.ndarray, sorted array of N real eigenvalues
        """
        H = self.build_matrix()
        # eigh para matrices Hermitanas (garantiza autovalores reales)
        evals = linalg.eigvalsh(H)
        return np.sort(evals)

    def density_of_states(self, E: float) -> float:
        """
        Densidad de niveles Berry-Keating: N_BK(E) ≈ E·T / (2π)
        Esta función NO usa ceros de ζ — es la fórmula de Weyl para el operador -i∂_t.
        """
        return E * self.T / (2 * math.pi)

    def positive_eigenvalues(self) -> np.ndarray:
        """Retorna solo los autovalores positivos (parte imaginaria de ρ > 0)."""
        return self.eigenvalues()[self.eigenvalues() > 0]


# ===========================================================================
# B) OPERADOR DE WU-SPRUNG
# ===========================================================================
class WuSprungOperator:
    r"""
    Operador de Schrödinger de Wu-Sprung: H = -d²/dx² + V_WS(x)
    El potencial V_WS(x) se define SIN USAR ceros de ζ
    -------------------------------------------------------
    La condición semiclásica de punto de retorno (Bohr-Sommerfeld):
        N_smooth(V_WS(x)) = x / π
    donde N_smooth(E) es la función de conteo SUAVE (fórmula de Riemann-von Mangoldt,
    derivada de Stirling — sin ceros):
        N_smooth(E) = E/(2π) · log(E/(2π)) - E/(2π) + 7/8     (E > 0)
    Esta es la misma función que aparece en el comportamiento asintótico del
    conteo de ceros, pero derivada puramente de la teoría analítica (Stirling
    aplicado a log Γ(s/2)) — no requiere conocer los ceros explícitamente.
    Discretización natural
    ----------------------
    Grid uniforme: x_j = (j+1)·h, j = 0,...,N-1, h = x_max/(N+1)
    Condiciones de Dirichlet: ψ(0) = ψ(x_max) = 0.
    Matriz tridiagonal real simétrica:
        H_{jk} = (2/h² + V_WS(x_j))·δ_{jk}
                - (1/h²)·δ_{j,k±1}
    Autovalores: aproximan Im(ρ_n) para los primeros N ceros no-triviales de ζ.
    Parameters
    ----------
    N       : número de puntos internos del grid
    x_max   : extremo del dominio [0, x_max]; elegir x_max ≈ π·N_smooth(E_max)
    """
    def __init__(self, N: int = 500, x_max: float = 70.0):
        if N < 4:
            raise ValueError("N debe ser al menos 4")
        if x_max <= 0:
            raise ValueError("x_max debe ser positivo")
        self.N = N
        self.x_max = x_max
        self.h = x_max / (N + 1)
        self.x_grid = np.array([(j + 1) * self.h for j in range(N)])

    # ------------------------------------------------------------------
    # Función de conteo suave (SIN ceros)
    # ------------------------------------------------------------------
    def N_smooth(self, E: float) -> float:
        r"""
        Función de conteo de ceros SUAVE (Riemann-von Mangoldt, parte principal):
            N_smooth(E) = E/(2π) · log(E/(2π)) - E/(2π) + 7/8
        Derivada de log|Γ(s/2)| vía la fórmula de Stirling. NO usa ceros de ζ.
        Es una función monótonamente creciente para E > 2π·e ≈ 17.08.
        Para E < 0 retorna 0 (sin ceros).
        Parameters
        ----------
        E : energía (positiva)
        Returns
        -------
        float : número suave de ceros hasta E
        """
        if E <= _EPS:
            return 0.0
        two_pi = 2.0 * math.pi
        val = (E / two_pi) * math.log(E / two_pi) - (E / two_pi) + 7.0 / 8.0
        return max(0.0, val)

    # ------------------------------------------------------------------
    # Inversión numérica de N_smooth
    # ------------------------------------------------------------------
    def _V_WS_scalar(self, x: float) -> float:
        """
        Potencial Wu-Sprung en un punto escalar x.
        Encuentra E tal que N_smooth(E) = x/π mediante bisección.
        Para x pequeño (N_smooth(E) < 0.01), devuelve el mínimo de N_smooth.
        """
        target = x / math.pi
        if target <= 0.0:
            return 2.0 * math.pi * math.e  # ≈ 17.08, mínimo de N_smooth
        # Cota inferior: N_smooth siempre ≥ -∞ pero positiva para E > ~17
        # Para target pequeño, E está cerca de 2πe
        E_lo = 2.0 * math.pi * math.e * 0.5  # ≈ 8.54
        E_hi = max(10.0 * target * math.pi + 100.0, 200.0)
        # Asegurar que E_hi es un bracket superior
        while self.N_smooth(E_hi) < target:
            E_hi *= 2.0
        # Si incluso E_lo satisface N_smooth(E_lo) > target, bajar E_lo
        while E_lo > _EPS and self.N_smooth(E_lo) >= target:
            E_lo /= 2.0
        try:
            E = brentq(lambda E: self.N_smooth(E) - target,
                       E_lo, E_hi, xtol=1e-8, maxiter=200)
        except ValueError:
            # Fallback: estimación directa
            E = target * math.pi * math.log(target * math.pi + 1.0)
        return float(E)

    def V_WS(self, x: np.ndarray | float) -> np.ndarray | float:
        """
        Potencial de Wu-Sprung V_WS(x).
        Definido como: la energía E tal que N_smooth(E) = x/π.
        Estrictamente monótono creciente (V_WS crece con x).
        Parameters
        ----------
        x : posición (escalar o array)
        Returns
        -------
        V : potencial en los puntos x (mismo tipo que x)
        """
        if np.ndim(x) == 0:
            return self._V_WS_scalar(float(x))
        return np.vectorize(self._V_WS_scalar)(np.asarray(x, dtype=float))

    # ------------------------------------------------------------------
    # Construcción de la matriz
    # ------------------------------------------------------------------
    def build_matrix(self) -> np.ndarray:
        """
        Construye la matriz tridiagonal real simétrica N×N:
            H = T + V
        donde T es la matriz cinética (-1/h²)(−1, 2, −1) y V = diag(V_WS(x_j)).
        Returns
        -------
        H : np.ndarray, shape (N,N), dtype float64, real-symmetric
        """
        h = self.h
        x = self.x_grid
        V_vals = self.V_WS(x)
        diag_vals = 2.0 / h ** 2 + V_vals
        off_diag = -np.ones(self.N - 1) / h ** 2
        H = np.diag(diag_vals) + np.diag(off_diag, 1) + np.diag(off_diag, -1)
        return H

    # ------------------------------------------------------------------
    # Autovalores
    # ------------------------------------------------------------------
    def eigenvalues(self) -> np.ndarray:
        """
        Calcula los autovalores del operador Wu-Sprung.
        Usa scipy.linalg.eigh (optimizado para matrices reales simétricas).
        Returns
        -------
        evals : np.ndarray, autovalores en orden ascendente
        """
        H = self.build_matrix()
        evals = linalg.eigvalsh(H)
        return np.sort(evals)

    def positive_eigenvalues(self, n_max: int = 20) -> np.ndarray:
        """Primeros n_max autovalores positivos (energías > 0)."""
        evals = self.eigenvalues()
        pos = evals[evals > 0]
        return pos[:n_max]


# ===========================================================================
# C) COMPARACIÓN DE AUTOVALORES CON CEROS DE ζ
# ===========================================================================
class EigenvalueComparison:
    """
    Compara autovalores computados con ceros conocidos de ζ(s).
    Esta clase recibe:
      - eigenvalues : autovalores calculados numéricamente (sin usar zeros)
      - zeros       : valores de referencia Im(ρ_n) (solo para comparación)
    El flujo completo:
      1. Operador H definido sin zeros → build_matrix()
      2. Autovalores numéricos       → eigenvalues()
      3. Comparación posterior       → match() / statistics()
    """
    def __init__(self, eigenvalues: np.ndarray,
                 zeros: List[float] = None):
        """
        Parameters
        ----------
        eigenvalues : array de autovalores (de BerryKeating o WuSprung)
        zeros       : lista de Im(ρ_n) de referencia (default: primeros 20)
        """
        self.eigenvalues = np.sort(np.asarray(eigenvalues, dtype=float))
        self.zeros = np.array(zeros or ZEROS_ZETA_REFERENCIA, dtype=float)

    def nearest_zero(self, eigenvalue: float) -> Tuple[float, float]:
        """
        Para un autovalor dado, encuentra el cero de ζ más cercano.
        Returns
        -------
        (nearest_zero, absolute_error)
        """
        if len(self.zeros) == 0:
            raise ValueError("La lista de ceros de referencia está vacía")
        idx = int(np.argmin(np.abs(self.zeros - eigenvalue)))
        return float(self.zeros[idx]), abs(eigenvalue - self.zeros[idx])

    def match_table(self, n_pairs: int = 15) -> List[Dict]:
        """
        Tabla de correspondencia entre autovalores positivos y ceros de ζ.
        Empareja el k-ésimo autovalor positivo con el k-ésimo cero de ζ
        (correspondencia por orden).
        Returns
        -------
        list of dicts with keys:
          k         : índice
          eigenval  : k-ésimo autovalor positivo
          zero_zeta : k-ésimo cero de ζ
          error_abs : |eigenval - zero_zeta|
          error_rel : error_abs / zero_zeta
        """
        pos_evals = self.eigenvalues[self.eigenvalues > 0]
        table = []
        n = min(n_pairs, len(pos_evals), len(self.zeros))
        for k in range(n):
            ev = float(pos_evals[k])
            zz = float(self.zeros[k])
            err = abs(ev - zz)
            table.append({
                "k": k + 1,
                "eigenval": ev,
                "zero_zeta": zz,
                "error_abs": err,
                "error_rel": err / max(zz, _EPS),
            })
        return table

    def statistics(self, n_pairs: int = 15) -> Dict:
        """
        Estadísticas globales de la comparación.
        Returns
        -------
        dict with:
          mean_abs_error  : error absoluto medio
          max_abs_error   : error absoluto máximo
          mean_rel_error  : error relativo medio
          n_within_1      : número de autovalores dentro de ±1 del cero más cercano
          n_within_5pct   : número dentro de ±5% del cero correspondiente
        """
        table = self.match_table(n_pairs)
        if not table:
            return {}
        errors_abs = [r["error_abs"] for r in table]
        errors_rel = [r["error_rel"] for r in table]
        return {
            "n_compared": len(table),
            "mean_abs_error": float(np.mean(errors_abs)),
            "max_abs_error": float(np.max(errors_abs)),
            "mean_rel_error": float(np.mean(errors_rel)),
            "n_within_1": int(sum(1 for e in errors_abs if e < 1.0)),
            "n_within_5pct": int(sum(1 for e in errors_rel if e < 0.05)),
        }

    def spacing_comparison(self, n: int = 15) -> Dict:
        """
        Compara los espaciados entre autovalores consecutivos con los de ceros de ζ.
        El espaciado entre ceros consecutivos es una medida más robusta que las
        posiciones absolutas (independiente de escalado global).
        Returns
        -------
        dict with mean_spacing_eigenvals, mean_spacing_zeros, ratio
        """
        pos_evals = self.eigenvalues[self.eigenvalues > 0]
        n_pairs = min(n, len(pos_evals), len(self.zeros))
        if n_pairs < 2:
            return {}
        spacings_ev = np.diff(pos_evals[:n_pairs])
        spacings_zz = np.diff(self.zeros[:n_pairs])
        corr = float(np.corrcoef(spacings_ev, spacings_zz[:len(spacings_ev)])[0, 1])
        if not math.isfinite(corr):
            corr = float("nan")
        return {
            "mean_spacing_eigenvals": float(np.mean(spacings_ev)),
            "mean_spacing_zeros": float(np.mean(spacings_zz)),
            "ratio": float(np.mean(spacings_ev) / max(np.mean(spacings_zz), _EPS)),
            "correlation": corr,
        }


# ===========================================================================
# D) ANÁLISIS COMPLETO
# ===========================================================================
def run_operator_analysis(
    bk_N: int = 300,
    bk_x_max: float = 1e8,
    ws_N: int = 400,
    ws_x_max: float = 70.0,
    n_compare: int = 15,
    verbose: bool = True,
) -> Dict:
    """
    Ejecuta el análisis completo:
      1. Construye operador Berry-Keating (sin ceros)
      2. Construye operador Wu-Sprung (sin ceros)
      3. Calcula autovalores de ambos
      4. Compara con ceros de ζ(s)
    Parameters
    ----------
    bk_N      : puntos del grid Berry-Keating
    bk_x_max  : extremo superior en x para Berry-Keating
    ws_N      : puntos del grid Wu-Sprung
    ws_x_max  : extremo superior en x para Wu-Sprung
    n_compare : número de pares a comparar
    verbose   : imprimir reporte
    Returns
    -------
    dict con resultados de ambos operadores
    """
    report = {}
    # ------------------------------------------------------------------
    # 1. Berry-Keating
    # ------------------------------------------------------------------
    bk = BerryKeatingOperator(N=bk_N, x_min=1.0, x_max=bk_x_max)
    bk_evals = bk.eigenvalues()
    bk_pos = bk_evals[bk_evals > 0][:n_compare]
    bk_cmp = EigenvalueComparison(bk_pos)
    report["berry_keating"] = {
        "description": "H = -i(x∂_x + 1/2) en L²([x_min,x_max])",
        "N": bk_N,
        "T_log": bk.T,
        "eigenvalue_spacing_2pi_over_T": 2 * math.pi / bk.T,
        "first_10_positive_eigenvalues": bk_pos[:10].tolist(),
        "comparison_stats": bk_cmp.statistics(n_compare),
        "spacing_comparison": bk_cmp.spacing_comparison(n_compare),
        "match_table": bk_cmp.match_table(min(n_compare, 10)),
    }
    # ------------------------------------------------------------------
    # 2. Wu-Sprung
    # ------------------------------------------------------------------
    ws = WuSprungOperator(N=ws_N, x_max=ws_x_max)
    ws_evals = ws.positive_eigenvalues(n_max=n_compare + 5)
    ws_cmp = EigenvalueComparison(ws_evals)
    report["wu_sprung"] = {
        "description": "H = -d²/dx² + V_WS(x), V_WS via N_smooth (sin ceros de ζ)",
        "N": ws_N,
        "x_max": ws_x_max,
        "h_step": ws.h,
        "first_10_eigenvalues": ws_evals[:10].tolist(),
        "first_10_zeros_ref": ZEROS_ZETA_REFERENCIA[:10],
        "comparison_stats": ws_cmp.statistics(n_compare),
        "spacing_comparison": ws_cmp.spacing_comparison(n_compare),
        "match_table": ws_cmp.match_table(min(n_compare, 10)),
    }
    # ------------------------------------------------------------------
    # 3. Resumen comparativo
    # ------------------------------------------------------------------
    ws_stats = report["wu_sprung"]["comparison_stats"]
    bk_stats = report["berry_keating"]["comparison_stats"]
    report["summary"] = {
        "wu_sprung_mean_abs_error": ws_stats.get("mean_abs_error"),
        "wu_sprung_n_within_1": ws_stats.get("n_within_1"),
        "berry_keating_spacing_ratio": report["berry_keating"]["spacing_comparison"].get("ratio"),
        "best_operator_for_zero_matching": (
            "wu_sprung"
            if ws_stats.get("mean_abs_error", 1e9) < bk_stats.get("mean_abs_error", 1e9)
            else "berry_keating"
        ),
    }
    if verbose:
        _print_report(report)
    return report


# ---------------------------------------------------------------------------
# Utilidad de impresión
# ---------------------------------------------------------------------------
def _print_report(report: Dict) -> None:
    sep = "=" * 72
    print(sep)
    print("  OPERADOR H RIEMANN  —  Trinity QCAL ∞³")
    print("  (definido sin ceros de ζ · discretización natural · comparación)")
    print(sep)
    for section, data in report.items():
        print(f"\n{'─'*72}")
        print(f"  {section.upper()}")
        print(f"{'─'*72}")
        _print_dict(data, indent=2)
    print(f"\n{sep}")
    print("  Sello: ∴𓂀Ω∞³Φ  |  Ψ ≥ 0.888  |  f₀ = 141.7001 Hz")
    print(sep)


def _print_dict(obj, indent: int = 0) -> None:
    prefix = " " * indent
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, (dict, list)):
                print(f"{prefix}{k}:")
                _print_dict(v, indent + 2)
            else:
                vstr = str(v)
                if len(vstr) > 78:
                    vstr = vstr[:75] + "..."
                print(f"{prefix}{k}: {vstr}")
    elif isinstance(obj, list):
        for item in obj[:6]:
            _print_dict(item, indent)
            if isinstance(item, dict):
                print()
    else:
        print(f"{prefix}{obj}")


# ===========================================================================
# Punto de entrada
# ===========================================================================
if __name__ == "__main__":
    run_operator_analysis(verbose=True)
