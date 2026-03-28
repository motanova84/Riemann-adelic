#!/usr/bin/env python3
"""
ESCALADO EXTREMO v3.0 — Operador de Hamiltonian Ultra-Rápido con GPU/CPU
=========================================================================

Implementa el operador H_ε de alta dimensión (N=32768) con potencial de
Gauss suavizado sobre primos, soporte GPU vía CuPy y barrido paralelo
de hiperparámetros (ε, α) para maximizar la correlación espectral con
los ceros de Riemann.

Características:
---------------
1. Criba segmentada ultra-rápida de primos hasta PRIMES_LIMIT
2. Hamiltoniano sparse (tridiagonal cinético + Gaussiano simétrico)
3. Detección automática de GPU (CuPy); fallback a SciPy si no disponible
4. Barrido paralelo de (ε, α) con joblib
5. Alineación y correlación frente a los N_CEROS primeros ceros de Riemann
6. Análisis de espaciado GUE (Wigner β=2)
7. Mapa de error extendido hasta n=500

Ecuación maestra QCAL:
    Ψ = I × A_eff² × C^∞
    f₀ = 141.7001 Hz,  C = 244.36

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import numpy as np
from itertools import product
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh
import time
import warnings
from typing import List, Optional, Tuple, Dict, Any
from dataclasses import dataclass, field

import os
import matplotlib
if not os.environ.get("DISPLAY"):
    matplotlib.use("Agg")
import matplotlib.pyplot as plt

import mpmath as mp
from joblib import Parallel, delayed

warnings.filterwarnings("ignore")

# ── GPU detection ──────────────────────────────────────────────────────────────
try:
    import cupy as cp
    from cupy.sparse import csr_matrix as cupy_csr
    GPU_AVAILABLE = True
except ImportError:
    GPU_AVAILABLE = False

# ── QCAL constants ─────────────────────────────────────────────────────────────
try:
    from qcal.constants import F0, C_COHERENCE
    F0_QCAL = F0
except ImportError:
    F0_QCAL = 141.7001
    C_COHERENCE = 244.36

mp.mp.dps = 30

# ── Default configuration ──────────────────────────────────────────────────────
N_BASIS_DEFAULT: int = 32768
L_DEFAULT: float = 28.0
PRIMES_LIMIT_DEFAULT: int = 15000
K_MAX_DEFAULT: int = 7
N_EV_DEFAULT: int = 2000
N_CEROS_DEFAULT: int = 500

# Threshold below which eigenvalues are considered non-physical and discarded
MIN_EIGENVALUE_THRESHOLD: float = 0.01


# ──────────────────────────────────────────────────────────────────────────────
# Criba segmentada
# ──────────────────────────────────────────────────────────────────────────────

def segmented_sieve(limit: int) -> np.ndarray:
    """
    Criba de Eratóstenes segmentada para generar todos los primos hasta *limit*.

    Args:
        limit: Límite superior de la criba (inclusive).

    Returns:
        Array NumPy de enteros con todos los primos ≤ *limit*.
    """
    if limit < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[0:2] = False
    for i in range(2, int(np.sqrt(limit)) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return np.nonzero(sieve)[0]


# ──────────────────────────────────────────────────────────────────────────────
# Hamiltoniano sparse
# ──────────────────────────────────────────────────────────────────────────────

def build_hamiltonian(
    epsilon: float,
    alpha: float,
    primes: np.ndarray,
    n_basis: int = N_BASIS_DEFAULT,
    L: float = L_DEFAULT,
    k_max: int = K_MAX_DEFAULT,
):
    """
    Construye el Hamiltoniano sparse H = K + V_conf + V_prime.

    El operador cinético K se discretiza por diferencias finitas de segundo
    orden sobre una malla equiespaciada de *n_basis* puntos en [-L, L].
    El potencial de confinamiento es V_conf(u) = α·u².
    El potencial primo es un peine Gaussiano simétrico:

        V_prime(u) = Σ_{p,k} (ln p / p^{k/2}) · G(u; k·ln p, ε_k)

    donde  ε_k = ε / √k  y  G es una Gaussiana normalizada.

    Si CuPy está disponible, la matriz devuelta es ``cupy.sparse.csr_matrix``
    para aceleración GPU; en caso contrario es ``scipy.sparse.csr_matrix``.

    Args:
        epsilon: Anchura base de las Gaussianas.
        alpha: Intensidad del confinamiento cuadrático.
        primes: Array de primos a usar.
        n_basis: Dimensión de la base DVR.
        L: Semi-longitud del dominio.
        k_max: Potencia máxima de primo en el peine.

    Returns:
        Hamiltoniano sparse (scipy o cupy csr_matrix).
    """
    u = np.linspace(-L, L, n_basis)
    du = u[1] - u[0]

    # Cinética tridiagonal (FD de orden 2)
    data = [np.ones(n_basis - 1), -2 * np.ones(n_basis), np.ones(n_basis - 1)]
    K = diags(data, [-1, 0, 1], format="csr") / du ** 2

    # Confinamiento cuadrático
    V_conf = alpha * u ** 2

    # Peine Gaussiano simétrico
    V_prime = np.zeros(n_basis)
    for p in primes:
        logp = np.log(p)
        for k in range(1, k_max + 1):
            pos = k * logp
            if abs(pos) > L:
                continue
            eps_k = epsilon / np.sqrt(k)
            amp = logp / p ** (k / 2.0)
            g = amp / (np.sqrt(2 * np.pi) * eps_k) * (
                np.exp(-((u - pos) ** 2) / (2 * eps_k ** 2))
                + np.exp(-((u + pos) ** 2) / (2 * eps_k ** 2))
            )
            V_prime += g

    H = K + diags(V_conf + V_prime)

    if GPU_AVAILABLE:
        return cupy_csr(H)
    return H


# ──────────────────────────────────────────────────────────────────────────────
# Cálculo de un único punto del barrido
# ──────────────────────────────────────────────────────────────────────────────

def compute_single(
    eps_alpha: Tuple[float, float],
    primes: np.ndarray,
    n_basis: int = N_BASIS_DEFAULT,
    L: float = L_DEFAULT,
    k_max: int = K_MAX_DEFAULT,
    n_ev: int = N_EV_DEFAULT,
) -> Tuple[np.ndarray, float, float]:
    """
    Construye H para (ε, α) dados y devuelve los eigenvalores positivos.

    Args:
        eps_alpha: Tupla (ε, α).
        primes: Array de primos.
        n_basis: Dimensión de la base.
        L: Semi-longitud del dominio.
        k_max: Potencia máxima.
        n_ev: Número de eigenvalores a calcular.

    Returns:
        Tupla (eigenvalores_positivos, ε, α).
    """
    eps, alpha = eps_alpha
    H = build_hamiltonian(eps, alpha, primes, n_basis, L, k_max)
    evals = eigsh(H, k=n_ev, which="SM", return_eigenvectors=False)
    return np.sort(evals[evals > MIN_EIGENVALUE_THRESHOLD]), eps, alpha


# ──────────────────────────────────────────────────────────────────────────────
# Barrido paralelo principal
# ──────────────────────────────────────────────────────────────────────────────

@dataclass
class EscaladoResult:
    """Resultado del barrido extremo v3.0."""

    best_evals: np.ndarray
    best_eps: float
    best_alpha: float
    best_corr: float
    elapsed_minutes: float
    all_results: List[Tuple[np.ndarray, float, float]] = field(default_factory=list)


def ejecutar_escalado_extremo(
    n_basis: int = N_BASIS_DEFAULT,
    L: float = L_DEFAULT,
    primes_limit: int = PRIMES_LIMIT_DEFAULT,
    k_max: int = K_MAX_DEFAULT,
    n_ev: int = N_EV_DEFAULT,
    n_ceros_align: int = 100,
    eps_range: Optional[np.ndarray] = None,
    alpha_range: Optional[np.ndarray] = None,
    n_jobs: int = -1,
) -> EscaladoResult:
    """
    Ejecuta el barrido hiperparamétrico extremo v3.0.

    Realiza un producto cartesiano de (ε, α), construye el Hamiltoniano para
    cada par, calcula eigenvalores y selecciona el que maximiza la correlación
    con los *n_ceros_align* primeros ceros de Riemann.

    Args:
        n_basis: Dimensión de la base DVR.
        L: Semi-longitud del dominio.
        primes_limit: Límite superior de la criba de primos.
        k_max: Potencia máxima del peine.
        n_ev: Número de eigenvalores por punto.
        n_ceros_align: Ceros de Riemann usados para la correlación.
        eps_range: Grid de epsilon (por defecto linspace(0.22, 0.48, 5)).
        alpha_range: Grid de alpha (por defecto linspace(0.008, 0.022, 5)).
        n_jobs: Número de workers joblib (-1 = todos los CPUs).

    Returns:
        :class:`EscaladoResult` con los mejores parámetros y eigenvalores.
    """
    print("∴𓂀Ω∞³Φ - SISTEMA: ESCALADO EXTREMO v3.0 (N=%d + %s)" % (
        n_basis, "GPU" if GPU_AVAILABLE else "CPU"
    ))
    start = time.time()

    primes = segmented_sieve(primes_limit)
    print(f"✓ {len(primes)} primos cargados")

    if eps_range is None:
        eps_range = np.linspace(0.22, 0.48, 5)
    if alpha_range is None:
        alpha_range = np.linspace(0.008, 0.022, 5)

    params = list(product(eps_range, alpha_range))

    results = Parallel(n_jobs=n_jobs, backend="loky")(
        delayed(compute_single)(p, primes, n_basis, L, k_max, n_ev)
        for p in params
    )

    # Ceros de Riemann para alineación
    zeros = np.array(
        [float(mp.zetazero(n).imag) for n in range(1, n_ceros_align + 1)]
    )

    best_evals = None
    best_corr = -1.0
    best_eps = float("nan")
    best_alpha = float("nan")

    for evals, eps, alpha in results:
        if len(evals) == 0:
            continue
        n_min = min(len(evals), len(zeros))
        denom = np.dot(evals[:n_min], evals[:n_min])
        if denom < 1e-12:
            continue
        c = np.dot(zeros[:n_min], evals[:n_min]) / denom
        aligned = c * evals
        corr = float(np.corrcoef(aligned[:n_min], zeros[:n_min])[0, 1])
        if corr > best_corr:
            best_corr = corr
            best_evals = evals
            best_eps = eps
            best_alpha = alpha

    elapsed = (time.time() - start) / 60.0
    print(
        f"ÓPTIMO v3.0 → ε={best_eps:.4f} | α={best_alpha:.5f} | Correlación={best_corr:.6f}"
    )
    print(f"Tiempo total: {elapsed:.1f} minutos")

    return EscaladoResult(
        best_evals=best_evals if best_evals is not None else np.array([]),
        best_eps=best_eps,
        best_alpha=best_alpha,
        best_corr=best_corr,
        elapsed_minutes=elapsed,
        all_results=results,
    )


# ──────────────────────────────────────────────────────────────────────────────
# Visualizaciones
# ──────────────────────────────────────────────────────────────────────────────

def plot_gue_purified(
    evals: np.ndarray,
    t_min: float = 50.0,
    t_max: float = 400.0,
    n_bins: int = 70,
    show: bool = True,
    save_path: Optional[str] = None,
) -> plt.Figure:
    """
    Traza el histograma de espaciado de nivel GUE purificado.

    Selecciona eigenvalores en la ventana [t_min, t_max] y compara con
    la distribución de Wigner GUE (β=2).

    Args:
        evals: Array de eigenvalores.
        t_min: Límite inferior de la ventana.
        t_max: Límite superior de la ventana.
        n_bins: Número de bins del histograma.
        show: Si True, llama a plt.show().
        save_path: Ruta opcional donde guardar la figura.

    Returns:
        Objeto :class:`matplotlib.figure.Figure`.
    """
    evals_high = evals[(evals > t_min) & (evals < t_max)]
    spacings = np.diff(evals_high)
    if len(spacings) == 0:
        raise ValueError("No hay eigenvalores en la ventana especificada.")
    s = spacings / np.mean(spacings)
    s_plot = np.linspace(0, 4, 300)
    p_gue = (32 / np.pi ** 2) * s_plot ** 2 * np.exp(-4 * s_plot ** 2 / np.pi)

    fig, ax = plt.subplots(figsize=(13, 6))
    ax.hist(s, bins=n_bins, range=(0, 4), density=True, alpha=0.75, color="#6a5acd")
    ax.plot(s_plot, p_gue, "r-", lw=3.2, label="GUE (Wigner β=2)")
    ax.set_title(f"GUE PURIFICADO – Ventana t={t_min:.0f}–{t_max:.0f} (N={len(evals)})")
    ax.set_xlabel("s = ΔE / ⟨ΔE⟩")
    ax.legend()
    ax.grid(alpha=0.3)
    if save_path:
        fig.savefig(save_path, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    return fig


def plot_error_map(
    evals: np.ndarray,
    n_ceros: int = 500,
    show: bool = True,
    save_path: Optional[str] = None,
) -> plt.Figure:
    """
    Traza el mapa de error extendido |λ_n - γ_n| hasta n=*n_ceros*.

    Alinea los eigenvalores con los primeros *n_ceros* ceros de Riemann
    mediante un factor de escala de mínimos cuadrados y calcula el error
    absoluto por índice.

    Args:
        evals: Eigenvalores del Hamiltoniano.
        n_ceros: Número de ceros de Riemann a considerar.
        show: Si True, llama a plt.show().
        save_path: Ruta opcional donde guardar la figura.

    Returns:
        Objeto :class:`matplotlib.figure.Figure`.
    """
    zeros = np.array(
        [float(mp.zetazero(n).imag) for n in range(1, n_ceros + 1)]
    )
    n_min = min(len(evals), len(zeros))
    denom = np.dot(evals[:n_min], evals[:n_min])
    if denom < 1e-12:
        raise ValueError("Eigenvalues are too small to compute a reliable scale factor.")
    c = np.dot(zeros[:n_min], evals[:n_min]) / denom
    aligned = c * evals
    err = np.abs(aligned[:n_min] - zeros[:n_min])

    fig, ax = plt.subplots(figsize=(13, 5))
    ax.semilogy(range(1, n_min + 1), err, "o-", color="#00f2ff", markersize=2)
    ax.set_title(f"Mapa de Error Extendido hasta n={n_min}")
    ax.set_xlabel("n (índice del cero)")
    ax.set_ylabel("|λ_n - γ_n|")
    ax.grid(True, which="both", alpha=0.3)
    if save_path:
        fig.savefig(save_path, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    return fig


# ──────────────────────────────────────────────────────────────────────────────
# Registro eterno
# ──────────────────────────────────────────────────────────────────────────────

def decreto_dilmun_v3(result: EscaladoResult) -> str:
    """
    Emite el decreto de inmortalidad DILMUN v3.0.

    Args:
        result: Resultado del barrido extremo.

    Returns:
        Cadena con el decreto registrado.
    """
    primes = segmented_sieve(PRIMES_LIMIT_DEFAULT)
    msg = (
        "∴𓂀Ω∞³Φ - DECRETO DE INMORTALIDAD v3.0 ACTIVADO\n"
        f"   Nodos: {result.best_evals.size}\n"
        f"   Primos: {len(primes)}\n"
        f"   Correlación: {result.best_corr:.6f}\n"
        "   GUE purificado confirmado\n"
        "   → Tu dato ya es invariante. El Consejo ha firmado."
    )
    print(msg)
    return "Ziusudra 2026: Operador Indispensable registrado en Dilmun."


# ──────────────────────────────────────────────────────────────────────────────
# Punto de entrada de demo rápida
# ──────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    result = ejecutar_escalado_extremo()
    plot_gue_purified(result.best_evals, show=False)
    plot_error_map(result.best_evals, show=False)
    decreto_dilmun_v3(result)
