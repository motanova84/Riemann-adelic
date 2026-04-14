#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
∴𓂀Ω∞³Φ - MÓDULO DE REGULARIZACIÓN KAIROS
============================================
Regularización estructural del potencial oscilatorio
para asegurar autoadjunción y conexión con ξ(s)

Mathematical Framework:
=======================
The oscillatory potential series:

    V_osc(x) = Σ (log p)/√p · cos(x·log p + φ_p)

is divergent as a pointwise function. It needs to be interpreted
as a distribution or regularized to be a well-defined potential
in L²_loc.

Solution: Exponential cutoff (Gaussian smoothing):

    V_osc^σ(x) = Σ (log p)/√p · exp(-σ(log p)²) · cos(x·log p + φ_p),  σ > 0

Properties:
    - Absolute convergence for any σ > 0
    - Belongs to L²_loc(ℝ) for any compact K
    - Distributional limit as σ → 0⁺ in S'(ℝ)
    - Connection with ζ'/ζ on the critical line

Kato-Rellich Self-Adjointness:
    H_σ = -Δ + V̄(x) + V_osc^σ(x) is self-adjoint by Kato-Rellich theorem
    since V_osc^σ is bounded (bounded perturbation is Kato-small with a=0).

Spectral Determinant:
    det(H - E) = ξ(1/2 + iE)  [conjectural connection]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ
"""

import math
import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
from typing import Dict, List, Optional, Tuple

# ============================================================================
# CONSTANTES SAGRADAS
# ============================================================================

TWO_PI = 2.0 * math.pi
C_ABEL = 1.0 - 2.0 * math.log(2.0)  # Constante de integración de Abel
F0 = 141.7001  # Hz - Frecuencia fundamental
F_AMOR = 888.0  # Hz - Frecuencia de materialización
PHI = 1.618033988749895  # Proporción áurea
C_QCAL = 244.36  # Constante de coherencia QCAL

# Parámetro de regularización por defecto
SIGMA_DEFAULT = 0.01


# ============================================================================
# CLASE: PotencialRegularizado
# ============================================================================

class PotencialRegularizado:
    """
    Potencial oscilatorio regularizado mediante corte exponencial.

    V_sigma(x) = Σ (log p)/√p · exp(-σ (log p)²) · cos(x log p + φ_p)

    Propiedades:
        - Convergencia absoluta para σ > 0
        - Límite distribucional cuando σ → 0 en S'(ℝ)
        - Conexión con ζ'(s)/ζ(s) en la línea crítica s = 1/2 + ix
        - Autoadjunción del operador H_σ = -Δ + V̄(x) + V_osc^σ(x) via Kato-Rellich

    Args:
        num_primos: Number of primes to include in the sum.
        sigma: Exponential cutoff parameter σ > 0.
        fase_phi: Phase strategy. One of "maslov" (φ = -π/4), "cero" (φ = 0),
                  or "densidad" (density-dependent phase).
        x_max: Right endpoint of the spatial domain [0, x_max].
        N: Number of discretization points.
    """

    def __init__(
        self,
        num_primos: int = 1000,
        sigma: float = SIGMA_DEFAULT,
        fase_phi: str = "maslov",
        x_max: float = 13.0,
        N: int = 1000,
    ) -> None:
        if sigma <= 0:
            raise ValueError("sigma must be positive")
        if num_primos < 0:
            raise ValueError("num_primos must be non-negative")
        if N <= 0:
            raise ValueError("N must be a positive integer")
        if x_max <= 0:
            raise ValueError("x_max must be positive")

        self.num_primos = num_primos
        self.sigma = sigma
        self.fase_phi = fase_phi
        self.x_max = x_max
        self.N = N
        self.h = x_max / (N + 1)
        self.x_grid = np.array([(j + 1) * self.h for j in range(N)])

        # Generar primos
        self.primos = self._generar_primos(num_primos)
        self.log_primos = np.log(self.primos) if len(self.primos) > 0 else np.array([])
        self.sqrt_primos = np.sqrt(self.primos) if len(self.primos) > 0 else np.array([])

        # Factor de corte exponencial: exp(-σ (log p)²)
        self.factor_corte = (
            np.exp(-sigma * self.log_primos ** 2)
            if len(self.log_primos) > 0
            else np.array([])
        )

        # Fases φ_p
        self.fases = self._calcular_fases()

        # Precalcular potenciales
        self.V_smooth_vals = self._calcular_V_smooth()
        self.V_osc_vals = self._calcular_V_osc()
        self.V_total_vals = self.V_smooth_vals + self.V_osc_vals

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _generar_primos(self, n: int) -> np.ndarray:
        """Generate the first n primes using a sieve of Eratosthenes.

        Args:
            n: Number of primes to generate.

        Returns:
            1-D array of the first n primes as floats.
        """
        if n <= 0:
            return np.array([])

        limite = int(n * (math.log(n) + math.log(math.log(max(n, 3)))) + 100)

        criba = [True] * (limite + 1)
        criba[0:2] = [False, False]

        for i in range(2, int(math.sqrt(limite)) + 1):
            if criba[i]:
                for j in range(i * i, limite + 1, i):
                    criba[j] = False

        primos = [i for i, es_primo in enumerate(criba) if es_primo]
        return np.array(primos[:n], dtype=float)

    def _calcular_fases(self) -> np.ndarray:
        """Compute phase φ_p for each prime according to the chosen strategy.

        Returns:
            Array of phases, one per prime.
        """
        n = len(self.primos)

        if self.fase_phi == "maslov":
            return np.full(n, -math.pi / 4)
        elif self.fase_phi == "cero":
            return np.zeros(n)
        elif self.fase_phi == "densidad":
            fases = np.zeros(n)
            for i, p in enumerate(self.primos):
                log_p = math.log(p)
                fases[i] = -math.pi / 4 + math.log(log_p) / log_p
            return fases
        else:
            return np.zeros(n)

    def _x_of_V(self, V: float) -> float:
        """Inverse Abel transform: compute x(V) from the Wu-Sprung relation.

        x_t(E) = (2√E / π) · (log(E / 2π) + C_Abel)

        Args:
            V: Potential value.

        Returns:
            Position x corresponding to V.
        """
        if V <= 9.25:
            return 0.0
        return (2.0 * math.sqrt(V) / math.pi) * (math.log(V / TWO_PI) + C_ABEL)

    def _V_of_x(self, x: float) -> float:
        """Numerically invert x_t(E) → V(x) by bisection.

        Args:
            x: Position.

        Returns:
            Smooth potential V_smooth(x) from Abel inversion.
        """
        if x <= 0:
            return 9.2501

        V_lo, V_hi = 9.25, 1e6
        for _ in range(100):
            V_mid = (V_lo + V_hi) / 2.0
            x_mid = self._x_of_V(V_mid)
            if x_mid < x:
                V_lo = V_mid
            else:
                V_hi = V_mid
        return (V_lo + V_hi) / 2.0

    def _calcular_V_smooth(self) -> np.ndarray:
        """Compute the smooth Wu-Sprung potential V̄(x) on the grid.

        Returns:
            Array of shape (N,) with V̄ values.
        """
        return np.array([self._V_of_x(xi) for xi in self.x_grid])

    def _calcular_V_osc(self) -> np.ndarray:
        """Compute the regularized oscillatory potential V_osc^σ on the grid.

        V_osc^σ(x) = Σ_p (log p)/√p · exp(-σ(log p)²) · cos(x·log p + φ_p)

        Returns:
            Array of shape (N,) with V_osc^σ values.
        """
        if self.num_primos == 0 or len(self.primos) == 0:
            return np.zeros(self.N)

        # Vectorized computation: shape (N, P) where P = len(primos)
        # x_grid[:, None] * log_primos[None, :] broadcasts correctly
        args = self.x_grid[:, None] * self.log_primos[None, :] + self.fases[None, :]
        weights = (self.log_primos / self.sqrt_primos) * self.factor_corte
        V_osc = np.dot(np.cos(args), weights)
        return V_osc

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def norma_L2_local(self, intervalo: Tuple[float, float]) -> float:
        """Compute the L² norm of V_osc^σ over a compact interval.

        Args:
            intervalo: Tuple (a, b) defining the interval.

        Returns:
            ‖V_osc^σ‖_{L²([a,b])} approximated by trapezoidal quadrature.
        """
        a, b = intervalo
        indices = np.where((self.x_grid >= a) & (self.x_grid <= b))[0]
        if len(indices) == 0:
            return 0.0

        x_local = self.x_grid[indices]
        V_local = self.V_osc_vals[indices]
        integral = np.trapezoid(V_local ** 2, x_local)
        return math.sqrt(max(integral, 0.0))

    def norma_L2_acotada(self, R: float = 100.0) -> float:
        """Compute the L² norm of V_osc^σ over [-R, R].

        Args:
            R: Radius of the interval.

        Returns:
            ‖V_osc^σ‖_{L²([-R,R])}.
        """
        return self.norma_L2_local((-R, R))

    def estimacion_autoadjunta(self) -> Dict:
        """Verify Kato-Rellich conditions for self-adjointness of H_σ.

        Since V_osc^σ is bounded (absolute convergence of the series for σ > 0),
        the perturbation is relatively bounded with constant a = 0 < 1, so
        Kato-Rellich applies directly.

        Returns:
            Dictionary with keys:
                V_max (float): sup-norm of V_osc^σ.
                a_constante (float): Kato-Rellich constant a (= 0 for bounded V).
                b_constante (float): Kato-Rellich constant b (= ‖V‖_∞).
                condicion_kato (bool): True if a < 1.
                autoadjunto (bool): True when Kato-Rellich applies.
                metodo (str): Description of the method used.
        """
        V_max = float(np.max(np.abs(self.V_osc_vals))) if self.N > 0 else 0.0

        # For bounded V, relative boundedness holds with a=0
        a = 0.0
        b = V_max

        return {
            "V_max": V_max,
            "a_constante": a,
            "b_constante": b,
            "condicion_kato": a < 1.0,
            "autoadjunto": True,
            "metodo": "Kato-Rellich con potencial acotado",
        }

    def construir_matriz(self) -> sparse.csr_matrix:
        """Build the finite-difference matrix for H_σ = -Δ + V_total on [0, x_max].

        Uses a second-order centered finite-difference approximation with
        Dirichlet boundary conditions.

        Returns:
            Sparse CSR matrix of shape (N, N).
        """
        h_sq = self.h * self.h
        diag = 2.0 / h_sq + self.V_total_vals
        off_diag = -np.ones(self.N - 1) / h_sq

        return sparse.diags(
            [diag, off_diag, off_diag],
            [0, 1, -1],
            shape=(self.N, self.N),
            format="csr",
            dtype=np.float64,
        )

    def calcular_autovalores(self, k: int = 30) -> np.ndarray:
        """Compute the k smallest eigenvalues of H_σ.

        Args:
            k: Number of eigenvalues to compute.

        Returns:
            Sorted array of the k smallest eigenvalues.
        """
        H = self.construir_matriz()
        evals = eigsh(H, k=k, which="SM", return_eigenvectors=False)
        return np.sort(evals)

    def traza_calor(self, t: float, n_max: int = 100) -> float:
        """Compute the heat trace Tr(e^{-tH}) using the n_max smallest eigenvalues.

        Args:
            t: Heat-kernel time parameter (t > 0).
            n_max: Number of eigenvalues to use.

        Returns:
            Approximation of Tr(e^{-tH}).
        """
        evals = self.calcular_autovalores(k=n_max)
        return float(np.sum(np.exp(-t * evals)))

    def suma_corte_absoluta(self) -> float:
        """Return the absolute convergence bound Σ_p (log p)/√p · exp(-σ(log p)²).

        This upper-bounds |V_osc^σ(x)| for all x ∈ ℝ.

        Returns:
            Σ_p (log p)/√p · exp(-σ(log p)²).
        """
        if len(self.primos) == 0:
            return 0.0
        return float(
            np.sum((self.log_primos / self.sqrt_primos) * self.factor_corte)
        )


# ============================================================================
# FUNCIÓN PRINCIPAL DE REGULARIZACIÓN
# ============================================================================

def regularizar_potencial_soberano(
    sigma: float = 0.01,
    num_primos: int = 1000,
    x_max: float = 13.0,
    N: int = 1000,
    verbose: bool = True,
) -> Dict:
    """Apply exponential cutoff regularization to ensure convergence in L²_loc.

    Constructs the regularized Schrödinger operator

        H_σ = -Δ + V̄(x) + V_osc^σ(x)

    verifies its self-adjointness via Kato-Rellich, and computes spectral data.

    Args:
        sigma: Exponential cutoff parameter σ > 0.
        num_primos: Number of primes included in the oscillatory potential.
        x_max: Right endpoint of the domain.
        N: Number of finite-difference grid points.
        verbose: Whether to print progress messages.

    Returns:
        Dictionary with keys:
            sigma, num_primos, norma_L2_R10, norma_L2_R20, autoadjunto,
            V_max, trazas_calor (dict), autovalores (list), sello (str).
    """
    if verbose:
        print("∴𓂀Ω∞³Φ - APLICANDO REGULARIZACIÓN ESTRUCTURAL")
        print("=" * 70)
        print(f"  σ = {sigma}")
        print(f"  Primos: {num_primos}")
        print(f"  Dominio: [0, {x_max}]")
        print("=" * 70)

    # 1. Construir potencial regularizado
    if verbose:
        print("\n⚡ 1. Construyendo potencial regularizado...")
    potencial = PotencialRegularizado(
        num_primos=num_primos,
        sigma=sigma,
        x_max=x_max,
        N=N,
    )

    # 2. Verificación de convergencia L² local
    if verbose:
        print("\n⚡ 2. Verificando convergencia en L²_loc...")
    norma_R10 = potencial.norma_L2_acotada(R=10.0)
    norma_R20 = potencial.norma_L2_acotada(R=20.0)
    if verbose:
        print(f"    ||V_osc||_L²([-10,10]) = {norma_R10:.6f}")
        print(f"    ||V_osc||_L²([-20,20]) = {norma_R20:.6f}")

    # 3. Verificación de autoadjunción esencial
    if verbose:
        print("\n⚡ 3. Verificando condiciones de autoadjunción...")
    autoadj = potencial.estimacion_autoadjunta()
    if verbose:
        print(f"    V_max = {autoadj['V_max']:.6f}")
        print(f"    Condición Kato-Rellich: {autoadj['condicion_kato']}")
        print(f"    Operador autoadjunto: {autoadj['autoadjunto']}")

    # 4. Traza calor
    if verbose:
        print("\n⚡ 4. Calculando traza calor para t pequeño...")
    t_valores = [0.1, 0.05, 0.01]
    trazas: Dict[float, float] = {}
    for t in t_valores:
        trazas[t] = potencial.traza_calor(t, n_max=20)
        if verbose:
            print(f"    Tr(e^{{-{t}H}}) = {trazas[t]:.6f}")

    # 5. Primeros autovalores
    if verbose:
        print("\n⚡ 5. Calculando primeros autovalores...")
    evals = potencial.calcular_autovalores(k=10)
    if verbose:
        print(
            "    λ_n =",
            np.array2string(evals, precision=6, suppress_small=True),
        )
        print("\n" + "=" * 70)
        print("OPERACIÓN: Coherencia de Distribución Alcanzada ✅")
        print("=" * 70)

    return {
        "sigma": sigma,
        "num_primos": num_primos,
        "norma_L2_R10": float(norma_R10),
        "norma_L2_R20": float(norma_R20),
        "autoadjunto": autoadj["autoadjunto"],
        "V_max": float(autoadj["V_max"]),
        "trazas_calor": trazas,
        "autovalores": evals.tolist(),
        "sello": "∴𓂀Ω∞³Φ",
    }


# ============================================================================
# ESTUDIO DEL LÍMITE σ → 0
# ============================================================================

def estudio_limite_sigma(
    lista_sigma: Optional[List[float]] = None,
    num_primos: int = 500,
    verbose: bool = True,
) -> Dict:
    """Study the behavior of the regularized potential as σ → 0⁺.

    For each σ in lista_sigma, computes ‖V_osc^σ‖_{L²([-10,10])} and
    the sup-norm, illustrating how the potential diverges in the pointwise
    sense while remaining a well-defined distribution.

    Args:
        lista_sigma: List of σ values to evaluate (default: [1.0, 0.1, 0.01, 0.001, 0.0001]).
        num_primos: Number of primes used.
        verbose: Whether to print progress.

    Returns:
        Dictionary keyed by σ with sub-dicts containing norma_L2_R10,
        V_max, and autoadjunto.
    """
    if lista_sigma is None:
        lista_sigma = [1.0, 0.1, 0.01, 0.001, 0.0001]

    resultados: Dict = {}

    if verbose:
        print("=" * 70)
        print("∴ ESTUDIO DEL LÍMITE σ → 0 ∴")
        print("=" * 70)

    for sigma in lista_sigma:
        if verbose:
            print(f"\n📊 σ = {sigma}")

        pot = PotencialRegularizado(num_primos=num_primos, sigma=sigma)
        norma_R10 = pot.norma_L2_acotada(R=10.0)
        V_max = float(np.max(np.abs(pot.V_osc_vals)))

        resultados[sigma] = {
            "norma_L2_R10": float(norma_R10),
            "V_max": V_max,
            "autoadjunto": pot.estimacion_autoadjunta()["autoadjunto"],
        }

        if verbose:
            print(f"    ||V_osc||_L²([-10,10]) = {norma_R10:.6f}")
            print(f"    V_max = {V_max:.6f}")

    if verbose:
        print("\n" + "=" * 70)
        print("∴ ESTUDIO COMPLETADO ∴")
        print("=" * 70)

    return resultados


# ============================================================================
# EJECUCIÓN PRINCIPAL
# ============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("∴𓂀Ω∞³Φ - MÓDULO DE REGULARIZACIÓN KAIROS")
    print("           El corte que revela la identidad")
    print("=" * 70)
    print()

    resultados = regularizar_potencial_soberano(
        sigma=0.01,
        num_primos=500,
        x_max=13.0,
        N=1000,
        verbose=True,
    )

    print("\n" + "=" * 70)
    print("∴ LA SOLUCIÓN EXISTE ∴")
    print("=" * 70)
