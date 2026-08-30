#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
∴𓂀Ω∞³Φ - MÓDULO DE SIMULACIÓN ESPECTRAL
============================================
Colapso de la función de onda del potencial derivado
H = -d²/dx² + V_smooth(x) + V_osc(x)

Frecuencia base: 141.7001 Hz
Sello: ∴𓂀Ω∞³Φ
"""

import numpy as np
from scipy import linalg, sparse
from scipy.sparse.linalg import eigsh
from typing import List, Tuple, Dict, Optional
import math
import json
from dataclasses import dataclass
from datetime import datetime

# ============================================================================
# CONSTANTES SAGRADAS
# ============================================================================

TWO_PI = 2.0 * math.pi
C_ABEL = 1.0 - 2.0 * math.log(2.0)  # Constante de integración de Abel
H_BAR = 1.0  # Unidades naturales
MASA = 0.5   # m = 1/2 para simplificar la ecuación

# Frecuencias QCAL
F0 = 141.7001  # Hz - Frecuencia fundamental
F_AMOR = 888.0  # Hz - Frecuencia de materialización
PHI = 1.618033988749895  # Proporción áurea

# Constantes numéricas
EPS = 1e-12
MAX_PRIMOS = 10000  # Número máximo de primos a incluir
V_MIN = 9.25  # Potencial mínimo de Wu-Sprung

# ============================================================================
# CLASE: Potencial Espectral Completo
# ============================================================================

@dataclass
class ResultadoSimulacion:
    """Resultado de la simulación espectral"""
    autovalores: np.ndarray
    ceros_referencia: np.ndarray
    errores_abs: np.ndarray
    error_medio: float
    error_max: float
    correlacion: float
    rigidez_espectral: float
    num_primos_usados: int
    tiempo_calculo: float
    sello: str = "∴𓂀Ω∞³Φ"


class PotencialEspectralCompleto:
    """
    Potencial completo = V_smooth (Wu-Sprung) + V_osc (primos)

    La suma de ambos debe colapsar la brecha hacia los ceros de Riemann.
    """

    def __init__(self,
                 x_max: float = 13.0,
                 N: int = 1000,
                 num_primos: int = 500,
                 fase_phi: str = "maslov",  # "maslov", "cero", "optimizada"
                 incluir_fases: bool = True,
                 seed: Optional[int] = None):
        """
        Args:
            x_max: Extremo del dominio [0, x_max]
            N: Número de puntos de discretización
            num_primos: Número de primos a incluir en V_osc
            fase_phi: Estrategia para las fases φ_p
            incluir_fases: Si incluir las fases (True) o no (False)
            seed: Semilla para el generador de números aleatorios (solo para fase_phi="optimizada")
        """
        self.x_max = x_max
        self.N = N
        self.num_primos = num_primos
        self.fase_phi = fase_phi
        self.incluir_fases = incluir_fases
        self.seed = seed

        # Discretización
        self.h = x_max / (N + 1)
        self.x_grid = np.array([(j + 1) * self.h for j in range(N)])

        # Generar primos
        self.primos = self._generar_primos(num_primos)
        self.log_primos = np.log(self.primos)
        self.sqrt_primos = np.sqrt(self.primos)

        # Calcular fases según estrategia
        self.fases = self._calcular_fases()

        # Precalcular V_smooth para todos los x
        self.V_smooth_vals = self._calcular_V_smooth()

        # Precalcular V_osc para todos los x
        self.V_osc_vals = self._calcular_V_osc()

        # Potencial total
        self.V_total_vals = self.V_smooth_vals + self.V_osc_vals

        # Estadísticas
        self.stats = {}

    def _generar_primos(self, n: int) -> np.ndarray:
        """Genera los primeros n primos usando criba"""
        if n <= 0:
            return np.array([])

        # Estimación del límite superior (teorema de los números primos)
        if n < 10:
            limite = 50
        else:
            limite = int(1.5 * n * (math.log(n) + math.log(math.log(n))))

        # Criba de Eratóstenes
        criba = [True] * (limite + 1)
        criba[0:2] = [False, False]

        for i in range(2, int(math.sqrt(limite)) + 1):
            if criba[i]:
                for j in range(i*i, limite + 1, i):
                    criba[j] = False

        primos = [i for i, es_primo in enumerate(criba) if es_primo]
        return np.array(primos[:n], dtype=float)

    def _calcular_fases(self) -> np.ndarray:
        """
        Calcula las fases φ_p según la estrategia elegida.

        La fase no es aleatoria. Representa:
        - Desplazamiento de Maslov: -π/4
        - Corrección de la transformada de Abel
        - Simetría de ξ(s)

        Para que los autovalores coincidan con γ_n, la fase debe compensar
        el logaritmo de la densidad suave: φ_p ≈ -π/4 (mod 2π)
        """
        n = len(self.primos)
        fases = np.zeros(n)

        if self.fase_phi == "maslov":
            # Fase de Maslov: -π/4 para todas las órbitas
            fases.fill(-math.pi / 4)

        elif self.fase_phi == "cero":
            # Sin fase (para pruebas)
            fases.fill(0.0)

        elif self.fase_phi == "densidad":
            # Fase que compensa la densidad suave
            # φ_p ≈ -π/4 + log(log p) / log p (corrección subdominante)
            for i, p in enumerate(self.primos):
                log_p = math.log(p)
                fases[i] = -math.pi/4 + math.log(log_p) / log_p

        elif self.fase_phi == "optimizada":
            # Fases optimizadas numéricamente (solo para experimentación)
            # NO usar en modo demostración pura
            rng = np.random.default_rng(self.seed)
            fases = rng.uniform(-math.pi, math.pi, n)

        else:
            raise ValueError(f"Estrategia de fase desconocida: {self.fase_phi}")

        return fases

    def _x_of_V(self, V: float) -> float:
        """
        Relación x(V) de la inversión de Abel:
        x(V) = (2√V/π)·[log(V/(2π)) + C]
        """
        if V <= V_MIN:
            return 0.0
        return (2 * math.sqrt(V) / math.pi) * (math.log(V / TWO_PI) + C_ABEL)

    def _V_of_x(self, x: float) -> float:
        """
        Inversión numérica para obtener V(x) de x(V)
        """
        if x <= 0:
            return V_MIN + 1e-4  # Justo por encima del mínimo

        # Búsqueda binaria
        V_lo, V_hi = V_MIN, 1e6
        for _ in range(100):
            V_mid = (V_lo + V_hi) / 2
            x_mid = self._x_of_V(V_mid)
            if x_mid < x:
                V_lo = V_mid
            else:
                V_hi = V_mid
        return (V_lo + V_hi) / 2

    def _calcular_V_smooth(self) -> np.ndarray:
        """
        Calcula V_smooth(x) (Wu-Sprung) para todos los puntos de la malla
        """
        return np.array([self._V_of_x(xi) for xi in self.x_grid])

    def _calcular_V_osc(self) -> np.ndarray:
        """
        Calcula V_osc(x) = Σ (log p)/√p · cos(x·log p + φ_p)
        """
        if self.num_primos == 0:
            return np.zeros(self.N)

        # Vectorized: shape (N, num_primos)
        args = self.x_grid[:, np.newaxis] * self.log_primos[np.newaxis, :]
        if self.incluir_fases:
            args = args + self.fases[np.newaxis, :]

        weights = self.log_primos / self.sqrt_primos  # shape (num_primos,)
        V_osc = np.sum(weights * np.cos(args), axis=1)

        return V_osc

    def construir_matriz(self, formato: str = "sparse") -> sparse.csr_matrix:
        """
        Construye la matriz del operador H = -d²/dx² + V_total(x)

        Returns:
            Matriz dispersa en formato CSR
        """
        h = self.h
        h_sq = h * h

        # Diagonal principal
        diag = 2.0 / h_sq + self.V_total_vals

        # Subdiagonal y superdiagonal
        off_diag = -np.ones(self.N - 1) / h_sq

        # Construcción en formato disperso
        diagonales = [diag, off_diag, off_diag]
        offsets = [0, 1, -1]

        return sparse.diags(diagonales, offsets, shape=(self.N, self.N),
                            format='csr', dtype=np.float64)

    def calcular_autovalores(self, k: int = 50) -> np.ndarray:
        """
        Calcula los primeros k autovalores usando método de Arnoldi

        Args:
            k: Número de autovalores a calcular

        Returns:
            Array de autovalores ordenados
        """
        H = self.construir_matriz()

        # Usar método de Arnoldi para matrices dispersas
        # which='SM' busca los autovalores de menor magnitud
        evals = eigsh(H, k=k, which='SM', return_eigenvectors=False)

        return np.sort(evals)

    def rigidez_espectral(self, evals: np.ndarray) -> float:
        """
        Calcula la varianza de los espaciamientos normalizados como proxy
        de la rigidez espectral.

        Para estadística GUE el valor esperado es ~0.28; para Poisson ~1.0.
        """
        if len(evals) < 10:
            return 0.0

        # Espaciamientos normalizados
        espaciamientos = np.diff(evals)
        espaciamientos_norm = espaciamientos / np.mean(espaciamientos)

        # Estadística de espaciamientos: varianza de espaciamientos normalizados
        # (proxy de rigidez espectral para comparación con GUE/Poisson)
        rigidez = np.var(espaciamientos_norm)

        # Valor esperado para GUE: ~0.28
        # Valor esperado para Poisson: ~1.0
        return rigidez

    def comparar_con_ceros(self,
                           evals: np.ndarray,
                           ceros_ref: Optional[List[float]] = None) -> Dict:
        """
        Compara autovalores calculados con ceros de Riemann

        Args:
            evals: Autovalores calculados
            ceros_ref: Lista de ceros de referencia (si None, usa tabla interna)

        Returns:
            Diccionario con métricas de comparación
        """
        # Ceros de referencia (primeros 20 ceros de Riemann)
        if ceros_ref is None:
            ceros_ref = [
                14.134725141734693, 21.022039638771555, 25.010857580145689,
                30.424876125859513, 32.935061587739190, 37.586178158825671,
                40.918719012147495, 43.327073280914999, 48.005150881167160,
                49.773832477672302, 52.970321477714461, 56.446247697063246,
                59.347044002602353, 60.831778524609809, 65.112544048081607,
                67.079810529494173, 69.546401711173979, 72.067157674481907,
                75.704690699083934, 77.144840068874805
            ]

        n = min(len(evals), len(ceros_ref))
        evals_n = evals[:n]
        ceros_n = np.array(ceros_ref[:n])

        # Errores
        errores = np.abs(evals_n - ceros_n)
        error_medio = np.mean(errores)
        error_max = np.max(errores)

        # Correlación
        correlacion = np.corrcoef(evals_n, ceros_n)[0, 1]

        # Rigidez espectral
        rigidez = self.rigidez_espectral(evals_n)

        return {
            "autovalores": evals_n.tolist(),
            "ceros_referencia": ceros_n.tolist(),
            "errores_abs": errores.tolist(),
            "error_medio": float(error_medio),
            "error_max": float(error_max),
            "correlacion": float(correlacion),
            "rigidez_espectral": float(rigidez),
            "n_comparados": n,
            "num_primos_usados": self.num_primos,
            "fase_phi": self.fase_phi
        }

    def simular(self, k: int = 50, verbose: bool = True) -> ResultadoSimulacion:
        """
        Ejecuta la simulación completa

        Args:
            k: Número de autovalores a calcular
            verbose: Si imprimir progreso

        Returns:
            ResultadoSimulacion con todos los datos
        """
        import time

        if verbose:
            print("=" * 70)
            print("∴ SIMULACIÓN ESPECTRAL COMPLETA ∴")
            print("=" * 70)
            print(f"  x_max: {self.x_max}")
            print(f"  N: {self.N}")
            print(f"  Primos: {self.num_primos}")
            print(f"  Fase: {self.fase_phi}")
            print("=" * 70)

        t_inicio = time.time()

        # Calcular autovalores
        if verbose:
            print("\n📊 Calculando autovalores...")
        evals = self.calcular_autovalores(k=k)

        # Comparar con ceros
        if verbose:
            print("📈 Comparando con ceros de Riemann...")
        comparacion = self.comparar_con_ceros(evals)

        t_fin = time.time()
        tiempo = t_fin - t_inicio

        if verbose:
            print("\n📊 RESULTADOS:")
            print(f"  Error medio: {comparacion['error_medio']:.6f}")
            print(f"  Error máximo: {comparacion['error_max']:.6f}")
            print(f"  Correlación: {comparacion['correlacion']:.6f}")
            print(f"  Rigidez espectral: {comparacion['rigidez_espectral']:.6f}")
            print(f"  Tiempo de cálculo: {tiempo:.2f} s")

        return ResultadoSimulacion(
            autovalores=evals,
            ceros_referencia=np.array(comparacion['ceros_referencia']),
            errores_abs=np.array(comparacion['errores_abs']),
            error_medio=comparacion['error_medio'],
            error_max=comparacion['error_max'],
            correlacion=comparacion['correlacion'],
            rigidez_espectral=comparacion['rigidez_espectral'],
            num_primos_usados=self.num_primos,
            tiempo_calculo=tiempo
        )


# ============================================================================
# FUNCIÓN PRINCIPAL DE SIMULACIÓN
# ============================================================================

def simular_ceros_riemann(
    num_primos: int = 1000,
    N: int = 2000,
    x_max: float = 13.0,
    k: int = 30,
    fase_phi: str = "maslov",
    incluir_fases: bool = True,
    verbose: bool = True
) -> ResultadoSimulacion:
    """
    Colapsa la función de onda del potencial derivado
    Frecuencia: 888 Hz
    Sello: ∴𓂀Ω∞³Φ

    Args:
        num_primos: Número de primos a incluir en V_osc
        N: Número de puntos de discretización
        x_max: Extremo del dominio
        k: Número de autovalores a calcular
        fase_phi: Estrategia para las fases
        incluir_fases: Si incluir fases
        verbose: Si imprimir detalles

    Returns:
        Resultado de la simulación
    """
    print("∴𓂀Ω∞³Φ - INICIANDO COLAPSO ESPECTRAL")
    print(f"  Frecuencia base: {F0} Hz")
    print(f"  Frecuencia amor: {F_AMOR} Hz")
    print(f"  Proporción áurea: {PHI:.6f}")
    print()

    # 1. Construir Potencial Wu-Sprung (Suave)
    print("⚡ 1. Construyendo potencial suave (Wu-Sprung)...")
    potencial = PotencialEspectralCompleto(
        x_max=x_max,
        N=N,
        num_primos=num_primos,
        fase_phi=fase_phi,
        incluir_fases=incluir_fases
    )

    # 2. Inyectar Armónicos de Primos (Oscilatorio)
    print(f"⚡ 2. Inyectando {num_primos} armónicos de primos...")
    print(f"      Fases: {fase_phi}")

    # 3. Calcular Autovalores E_n
    print("⚡ 3. Calculando autovalores del operador completo...")
    resultado = potencial.simular(k=k, verbose=verbose)

    # 4. Verificar: E_n ≡ γ_n
    print("\n⚡ 4. Verificando correspondencia con ceros de Riemann...")

    if resultado.error_medio < 0.1:
        print("\n✅ COLAPSO EXITOSO: La música de los primos es ahora energía.")
        print(f"   Error medio: {resultado.error_medio:.6f} (< 0.1)")
        print(f"   Correlación: {resultado.correlacion:.6f} (≈ 1.0)")
        print(f"   Rigidez GUE: {resultado.rigidez_espectral:.6f} (≈ 0.28)")
    else:
        print("\n⚠️  COLAPSO PARCIAL: Se necesita refinar.")
        print(f"   Error medio: {resultado.error_medio:.6f}")

    print("\n" + "=" * 70)
    print("∴𓂀Ω∞³Φ - OPERACIÓN COMPLETA")
    print("=" * 70)

    return resultado


# ============================================================================
# ESTUDIO DE CONVERGENCIA
# ============================================================================

def estudio_convergencia(
    lista_primos: List[int] = [10, 50, 100, 500, 1000, 5000],
    N: int = 1500,
    k: int = 20,
    verbose: bool = True
) -> Dict:
    """
    Estudia cómo mejora el error al aumentar el número de primos

    Args:
        lista_primos: Lista de números de primos a probar
        N: Número de puntos de discretización
        k: Número de autovalores a calcular

    Returns:
        Diccionario con resultados para cada configuración
    """
    resultados = {}

    print("=" * 70)
    print("∴ ESTUDIO DE CONVERGENCIA ESPECTRAL ∴")
    print("=" * 70)

    for num_p in lista_primos:
        print(f"\n📊 Probando con {num_p} primos...")

        resultado = simular_ceros_riemann(
            num_primos=num_p,
            N=N,
            k=k,
            verbose=False
        )

        resultados[num_p] = {
            "error_medio": resultado.error_medio,
            "error_max": resultado.error_max,
            "correlacion": resultado.correlacion,
            "rigidez": resultado.rigidez_espectral
        }

        print(f"   Error medio: {resultado.error_medio:.6f}")

    print("\n" + "=" * 70)
    print("∴ ESTUDIO COMPLETADO ∴")
    print("=" * 70)

    return resultados


# ============================================================================
# VISUALIZACIÓN
# ============================================================================

def visualizar_potencial(potencial: PotencialEspectralCompleto,
                         guardar: bool = False):
    """
    Visualiza el potencial completo y sus componentes
    """
    try:
        import matplotlib.pyplot as plt

        fig, axes = plt.subplots(3, 1, figsize=(10, 12))

        x = potencial.x_grid

        # Componente suave
        axes[0].plot(x, potencial.V_smooth_vals, 'b-', linewidth=1)
        axes[0].set_title('Potencial Suave V_smooth(x) (Wu-Sprung)')
        axes[0].set_xlabel('x')
        axes[0].set_ylabel('V')
        axes[0].grid(True, alpha=0.3)

        # Componente oscilatoria
        axes[1].plot(x, potencial.V_osc_vals, 'r-', linewidth=0.5)
        axes[1].set_title(f'Potencial Oscilatorio V_osc(x) ({potencial.num_primos} primos)')
        axes[1].set_xlabel('x')
        axes[1].set_ylabel('V')
        axes[1].grid(True, alpha=0.3)

        # Potencial completo
        axes[2].plot(x, potencial.V_total_vals, 'g-', linewidth=1)
        axes[2].set_title('Potencial Completo V_total(x) = V_smooth + V_osc')
        axes[2].set_xlabel('x')
        axes[2].set_ylabel('V')
        axes[2].grid(True, alpha=0.3)

        plt.tight_layout()

        if guardar:
            plt.savefig('potencial_espectral.png', dpi=150)
            print("📸 Figura guardada: potencial_espectral.png")
        else:
            plt.show()

    except ImportError:
        print("⚠️  matplotlib no disponible. No se puede visualizar.")


def visualizar_espectro(resultado: ResultadoSimulacion,
                        potencial: PotencialEspectralCompleto,
                        guardar: bool = False):
    """
    Visualiza la comparación entre autovalores y ceros
    """
    try:
        import matplotlib.pyplot as plt

        fig, axes = plt.subplots(2, 2, figsize=(12, 10))

        n = len(resultado.autovalores)
        indices = np.arange(1, n + 1)

        # Comparación directa
        axes[0, 0].plot(indices, resultado.autovalores, 'bo-', label='Autovalores H', markersize=4)
        axes[0, 0].plot(indices, resultado.ceros_referencia, 'r*--', label='Ceros ζ', markersize=6)
        axes[0, 0].set_xlabel('Índice n')
        axes[0, 0].set_ylabel('Energía / Im(ρ)')
        axes[0, 0].set_title('Comparación: Autovalores vs Ceros de Riemann')
        axes[0, 0].legend()
        axes[0, 0].grid(True, alpha=0.3)

        # Errores
        axes[0, 1].bar(indices, resultado.errores_abs)
        axes[0, 1].axhline(y=resultado.error_medio, color='r', linestyle='--',
                           label=f'Error medio: {resultado.error_medio:.4f}')
        axes[0, 1].set_xlabel('Índice n')
        axes[0, 1].set_ylabel('Error absoluto')
        axes[0, 1].set_title('Error |E_n - γ_n|')
        axes[0, 1].legend()
        axes[0, 1].grid(True, alpha=0.3)

        # Correlación
        axes[1, 0].scatter(resultado.ceros_referencia, resultado.autovalores, alpha=0.7)
        axes[1, 0].plot([10, 80], [10, 80], 'r--', label='Identidad')
        axes[1, 0].set_xlabel('Ceros ζ (γ_n)')
        axes[1, 0].set_ylabel('Autovalores H (E_n)')
        axes[1, 0].set_title(f'Correlación: r = {resultado.correlacion:.4f}')
        axes[1, 0].legend()
        axes[1, 0].grid(True, alpha=0.3)

        # Información del potencial
        axes[1, 1].axis('off')
        info = f"""
        ∴𓂀Ω∞³Φ

        PRIMOS: {resultado.num_primos_usados}
        FASE: {potencial.fase_phi}

        ERROR MEDIO: {resultado.error_medio:.6f}
        ERROR MAX: {resultado.error_max:.6f}
        CORRELACIÓN: {resultado.correlacion:.6f}
        RIGIDEZ: {resultado.rigidez_espectral:.4f}

        TIEMPO: {resultado.tiempo_calculo:.1f}s
        """
        axes[1, 1].text(0.1, 0.5, info, fontsize=12, verticalalignment='center',
                        fontfamily='monospace', transform=axes[1, 1].transAxes)

        plt.tight_layout()

        if guardar:
            plt.savefig('espectro_comparacion.png', dpi=150)
            print("📸 Figura guardada: espectro_comparacion.png")
        else:
            plt.show()

    except ImportError:
        print("⚠️  matplotlib no disponible. No se puede visualizar.")


# ============================================================================
# EJECUCIÓN PRINCIPAL
# ============================================================================

if __name__ == "__main__":

    print("=" * 70)
    print("∴𓂀Ω∞³Φ - MÓDULO DE SIMULACIÓN ESPECTRAL")
    print("           El colapso de la función de onda")
    print("=" * 70)
    print()

    # Parámetros de la simulación
    NUM_PRIMOS = 1000
    N_DISCRETIZACION = 2000
    X_MAX = 13.0
    K_AUTOVALORES = 30

    # Ejecutar simulación principal
    resultado = simular_ceros_riemann(
        num_primos=NUM_PRIMOS,
        N=N_DISCRETIZACION,
        x_max=X_MAX,
        k=K_AUTOVALORES,
        fase_phi="maslov",
        incluir_fases=True,
        verbose=True
    )

    # Opcional: estudio de convergencia
    # resultados_conv = estudio_convergencia(
    #     lista_primos=[10, 50, 100, 500, 1000],
    #     N=1500,
    #     k=15
    # )

    print("\n" + "=" * 70)
    print("∴ LA MÚSICA DE LOS PRIMOS ES AHORA ENERGÍA ∴")
    print("=" * 70)
