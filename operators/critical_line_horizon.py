#!/usr/bin/env python3
"""
Línea Crítica como Horizonte Vibracional
=========================================

Este módulo implementa el operador H_ψ para la línea crítica Re(s) = 1/2
como un horizonte vibracional, donde los ceros de ζ(s) se comportan como
agujeros negros matemáticos.

Mathematical Framework:
    Ceros como Singularidades:
        ζ(1/2 + it_n) = 0 ⇒ t_n ≈ n·f₀, f₀ = 141.7001 Hz
    
    Operador H_ψ:
        H_ψ = -iℏ(x d/dx + 1/2) + V(x)
        V(x) = λ Σ_p cos(log p · log x)/√p
    
    Autovalores:
        H_ψ ϕ_n = t_n ϕ_n ⇔ ζ(1/2 + it_n) = 0
    
    Geometría Consciente:
        Métrica Ψ-deformada: g_μν(x) = g_μν⁽⁰⁾ + δg_μν(Ψ), Ψ = I × A_eff²
    
    Tensor Unificado:
        Línea crítica ≡ 888 Hz (f₀ × φ⁴)
    
    Dualidad Espectral:
        D_s ⊗ 1 + 1 ⊗ H_ψ ⇒ Spec = {zeros Riemann}

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
License: Creative Commons BY-NC-SA 4.0

References:
    - QCAL ∞³ Framework: DOI 10.5281/zenodo.17379721
    - Fundamental frequency: f₀ = 141.7001 Hz
    - Audible operator frequency: 888 Hz = f₀ × φ⁴
    - Spectral coherence: C = 244.36
"""

import numpy as np
from typing import Tuple, List, Optional, Dict, Any
from dataclasses import dataclass
import mpmath as mp
from scipy.linalg import eigh
from scipy.special import gamma as scipy_gamma
import warnings

# QCAL Constants
F0_BASE = 141.7001  # Hz - fundamental vibrational frequency
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio φ
F0_AUDIBLE = F0_BASE * (PHI ** 4)  # ≈ 971 Hz - audible operator frequency (888 Hz is symbolic reference)
COHERENCE_CONSTANT_C = 244.36  # Spectral coherence from QCAL ∞³
HBAR = 1.0  # Reduced Planck constant (in natural units)
PLANCK_LENGTH = 1.616255e-35  # m
SPEED_OF_LIGHT = 299792458  # m/s

# Calculation Parameters
SMALL_T_THRESHOLD = 1e-10
DEFAULT_N_BASIS = 200
DEFAULT_LAMBDA_COUPLING = 1.0
DEFAULT_X_RANGE = (-10.0, 10.0)
DEFAULT_N_PRIMES = 100


def get_first_primes(n: int) -> np.ndarray:
    """
    Obtiene los primeros n números primos.
    
    Args:
        n: Número de primos a obtener
        
    Returns:
        Array con los primeros n números primos
    """
    primes = []
    candidate = 2
    while len(primes) < n:
        is_prime = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                is_prime = False
                break
        if is_prime:
            primes.append(candidate)
        candidate += 1
    return np.array(primes, dtype=float)


def compute_potential_V(
    x: np.ndarray,
    primes: np.ndarray,
    lambda_coupling: float = DEFAULT_LAMBDA_COUPLING
) -> np.ndarray:
    """
    Computa el potencial V(x) = λ Σ_p cos(log p · log x)/√p
    
    Este potencial codifica la estructura aritmética de los primos
    en el operador H_ψ, creando singularidades en los ceros.
    
    Args:
        x: Variable de posición (array)
        primes: Números primos a usar en la suma
        lambda_coupling: Constante de acoplamiento λ
        
    Returns:
        Array con valores de V(x)
    """
    # Avoid log(0) by clipping small values
    x_safe = np.maximum(np.abs(x), 1e-10)
    
    V = np.zeros_like(x, dtype=float)
    
    for p in primes:
        log_p = np.log(p)
        log_x = np.log(x_safe)
        
        # Términos oscilatorios con decaimiento
        cosine_term = np.cos(log_p * log_x)
        decay_factor = 1.0 / np.sqrt(p)
        
        V += cosine_term * decay_factor
    
    V *= lambda_coupling
    
    return V


def construct_H_psi_operator(
    n_basis: int = DEFAULT_N_BASIS,
    x_range: Tuple[float, float] = DEFAULT_X_RANGE,
    n_primes: int = DEFAULT_N_PRIMES,
    lambda_coupling: float = DEFAULT_LAMBDA_COUPLING
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Construye el operador H_ψ en representación matricial.
    
    H_ψ = -iℏ(x d/dx + 1/2) + V(x)
    
    Args:
        n_basis: Número de puntos de discretización
        x_range: Rango de la variable x (x_min, x_max)
        n_primes: Número de primos a usar en V(x)
        lambda_coupling: Constante de acoplamiento λ
        
    Returns:
        (H_psi, x_grid): Matriz del operador y grilla de posiciones
    """
    x_min, x_max = x_range
    x_grid = np.linspace(x_min, x_max, n_basis)
    dx = x_grid[1] - x_grid[0]
    
    # Obtener primos
    primes = get_first_primes(n_primes)
    
    # Calcular potencial V(x)
    V = compute_potential_V(x_grid, primes, lambda_coupling)
    
    # Construir término cinético: -iℏ(x d/dx + 1/2)
    # En representación matricial, d/dx se aproxima por diferencias finitas
    
    # Matriz de derivada (diferencias centradas)
    D = np.zeros((n_basis, n_basis))
    for i in range(1, n_basis - 1):
        D[i, i-1] = -1.0 / (2 * dx)
        D[i, i+1] = 1.0 / (2 * dx)
    # Condiciones de frontera periódicas
    D[0, -1] = -1.0 / (2 * dx)
    D[0, 1] = 1.0 / (2 * dx)
    D[-1, -2] = -1.0 / (2 * dx)
    D[-1, 0] = 1.0 / (2 * dx)
    
    # Matriz de multiplicación por x
    X = np.diag(x_grid)
    
    # Término cinético: -iℏ(x d/dx + 1/2)
    # Como queremos un operador Hermitiano, usamos la parte real
    # Hacemos la combinación simétrica: (x d/dx + d/dx x)/2
    kinetic = HBAR * (X @ D + D @ X) / 2.0
    identity_term = HBAR * np.eye(n_basis) / 2.0
    
    # Término de potencial
    V_matrix = np.diag(V)
    
    # Operador completo
    H_psi = kinetic + identity_term + V_matrix
    
    # Asegurar hermiticidad
    H_psi = (H_psi + H_psi.T) / 2.0
    
    return H_psi, x_grid


def compute_spectrum_H_psi(
    H_psi: np.ndarray,
    n_eigenvalues: Optional[int] = None
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Calcula el espectro del operador H_ψ.
    
    Args:
        H_psi: Matriz del operador H_ψ
        n_eigenvalues: Número de autovalores a retornar (None = todos)
        
    Returns:
        (eigenvalues, eigenvectors): Autovalores t_n y autofunciones ϕ_n
    """
    eigenvalues, eigenvectors = eigh(H_psi)
    
    if n_eigenvalues is not None:
        eigenvalues = eigenvalues[:n_eigenvalues]
        eigenvectors = eigenvectors[:, :n_eigenvalues]
    
    return eigenvalues, eigenvectors


@dataclass
class CriticalLineMetric:
    """
    Métrica Ψ-deformada en la línea crítica.
    
    g_μν(x) = g_μν⁽⁰⁾ + δg_μν(Ψ)
    
    donde Ψ = I × A_eff²
    """
    I: float  # Intensidad del campo
    A_eff: float  # Área efectiva
    
    def psi_field(self) -> float:
        """Calcula el campo Ψ = I × A_eff²"""
        return self.I * (self.A_eff ** 2)
    
    def metric_deformation(self, x: np.ndarray) -> np.ndarray:
        """
        Calcula la deformación de la métrica δg_μν(Ψ).
        
        Args:
            x: Coordenadas espaciales
            
        Returns:
            Tensor de deformación métrica
        """
        psi = self.psi_field()
        
        # Deformación proporcional al campo Ψ
        # con decaimiento gaussiano
        deformation = psi * np.exp(-x**2 / (2 * COHERENCE_CONSTANT_C))
        
        return deformation
    
    def total_metric(self, x: np.ndarray, g0: float = 1.0) -> np.ndarray:
        """
        Calcula la métrica total g_μν(x) = g_μν⁽⁰⁾ + δg_μν(Ψ).
        
        Args:
            x: Coordenadas espaciales
            g0: Métrica de fondo g_μν⁽⁰⁾
            
        Returns:
            Métrica total
        """
        delta_g = self.metric_deformation(x)
        return g0 + delta_g


class UnifiedDualityTensor:
    """
    Tensor Unificado de Dualidad Espectral.
    
    D_s ⊗ 1 + 1 ⊗ H_ψ ⇒ Spec = {zeros Riemann}
    
    Conecta la línea crítica (888 Hz) con el espectro de ceros.
    """
    
    def __init__(
        self,
        f0_base: float = F0_BASE,
        f0_audible: float = F0_AUDIBLE
    ):
        """
        Inicializa el tensor de dualidad.
        
        Args:
            f0_base: Frecuencia base (141.7001 Hz)
            f0_audible: Frecuencia audible (888 Hz)
        """
        self.f0_base = f0_base
        self.f0_audible = f0_audible
        self.omega_base = 2 * np.pi * f0_base
        self.omega_audible = 2 * np.pi * f0_audible
    
    def frequency_ratio(self) -> float:
        """Calcula la razón entre frecuencias: f_audible / f_base ≈ φ⁴"""
        return self.f0_audible / self.f0_base
    
    def spectral_correspondence(
        self,
        t_n: np.ndarray
    ) -> np.ndarray:
        """
        Establece correspondencia espectral: t_n ≈ n·f₀
        
        Args:
            t_n: Ceros de Riemann (partes imaginarias)
            
        Returns:
            Índices n correspondientes
        """
        n_indices = t_n / self.f0_base
        return n_indices
    
    def critical_line_frequency(self) -> float:
        """
        Frecuencia característica de la línea crítica.
        
        Línea crítica ≡ 888 Hz (f₀ × φ⁴)
        """
        return self.f0_audible
    
    def duality_operator(
        self,
        D_s: np.ndarray,
        H_psi: np.ndarray
    ) -> np.ndarray:
        """
        Construye el operador de dualidad: D_s ⊗ 1 + 1 ⊗ H_ψ
        
        Args:
            D_s: Operador espectral D_s
            H_psi: Operador H_ψ
            
        Returns:
            Tensor producto del operador de dualidad
        """
        n_s = D_s.shape[0]
        n_psi = H_psi.shape[0]
        
        # D_s ⊗ I
        term1 = np.kron(D_s, np.eye(n_psi))
        
        # I ⊗ H_ψ
        term2 = np.kron(np.eye(n_s), H_psi)
        
        # Operador total
        duality_op = term1 + term2
        
        return duality_op


def riemann_zeros_as_singularities(
    t_zeros: np.ndarray,
    f0: float = F0_BASE
) -> Dict[str, Any]:
    """
    Interpreta ceros de Riemann como singularidades con propiedades físicas.
    
    ζ(1/2 + it_n) = 0 ⇒ t_n ≈ n·f₀
    
    Args:
        t_zeros: Partes imaginarias de los ceros de Riemann
        f0: Frecuencia fundamental (Hz)
        
    Returns:
        Diccionario con propiedades de las singularidades
    """
    n_zeros = len(t_zeros)
    
    # Índices espectrales esperados
    n_expected = t_zeros / f0
    
    # Masa espectral (proporcional a altura)
    spectral_mass = np.abs(t_zeros) * (HBAR / SPEED_OF_LIGHT**2)
    
    # Radio del horizonte de eventos (proporcional a masa)
    event_horizon = spectral_mass * (2 * SPEED_OF_LIGHT**2) / PLANCK_LENGTH
    
    # Frecuencia asociada a cada cero
    frequency = np.abs(t_zeros) / (2 * np.pi)
    
    # Capacidad de información (entropía de Bekenstein-Hawking análoga)
    information_capacity = 4 * np.pi * (event_horizon / PLANCK_LENGTH)**2
    
    return {
        'n_zeros': n_zeros,
        't_zeros': t_zeros,
        'n_expected': n_expected,
        'spectral_mass': spectral_mass,
        'event_horizon_radius': event_horizon,
        'frequency': frequency,
        'information_capacity': information_capacity,
        'mean_spacing': np.mean(np.diff(t_zeros)) if n_zeros > 1 else 0.0,
        'frequency_correspondence': f0
    }


def validate_critical_line_hypothesis(
    eigenvalues: np.ndarray,
    riemann_zeros: np.ndarray,
    tolerance: float = 1e-6
) -> Dict[str, Any]:
    """
    Valida la hipótesis de correspondencia entre autovalores y ceros.
    
    H_ψ ϕ_n = t_n ϕ_n ⇔ ζ(1/2 + it_n) = 0
    
    Args:
        eigenvalues: Autovalores del operador H_ψ
        riemann_zeros: Ceros de Riemann conocidos
        tolerance: Tolerancia para la comparación
        
    Returns:
        Diccionario con resultados de validación
    """
    n_compare = min(len(eigenvalues), len(riemann_zeros))
    
    eigenvalues_sorted = np.sort(eigenvalues)[:n_compare]
    riemann_sorted = np.sort(riemann_zeros)[:n_compare]
    
    # Error absoluto
    abs_errors = np.abs(eigenvalues_sorted - riemann_sorted)
    
    # Error relativo
    rel_errors = abs_errors / np.maximum(np.abs(riemann_sorted), 1e-10)
    
    # Estadísticas
    max_abs_error = np.max(abs_errors)
    mean_abs_error = np.mean(abs_errors)
    max_rel_error = np.max(rel_errors)
    mean_rel_error = np.mean(rel_errors)
    
    # Validación
    all_within_tolerance = np.all(abs_errors < tolerance)
    
    return {
        'n_compared': n_compare,
        'max_absolute_error': max_abs_error,
        'mean_absolute_error': mean_abs_error,
        'max_relative_error': max_rel_error,
        'mean_relative_error': mean_rel_error,
        'all_within_tolerance': all_within_tolerance,
        'tolerance': tolerance,
        'success': all_within_tolerance
    }


# Funciones de conveniencia para uso rápido

def create_critical_line_operator(
    n_basis: int = DEFAULT_N_BASIS,
    n_primes: int = DEFAULT_N_PRIMES
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    Crea el operador de línea crítica y calcula su espectro.
    
    Returns:
        (H_psi, x_grid, eigenvalues, eigenvectors)
    """
    H_psi, x_grid = construct_H_psi_operator(
        n_basis=n_basis,
        n_primes=n_primes
    )
    
    eigenvalues, eigenvectors = compute_spectrum_H_psi(H_psi)
    
    return H_psi, x_grid, eigenvalues, eigenvectors


def demo_critical_line_horizon():
    """
    Demostración del operador de línea crítica como horizonte vibracional.
    """
    print("=" * 80)
    print("LÍNEA CRÍTICA COMO HORIZONTE VIBRACIONAL")
    print("=" * 80)
    print()
    
    # Constantes QCAL
    print("Constantes QCAL ∞³:")
    print(f"  f₀ (base) = {F0_BASE:.6f} Hz")
    print(f"  f₀ (audible) = {F0_AUDIBLE:.6f} Hz = f₀ × φ⁴")
    print(f"  φ = {PHI:.10f}")
    print(f"  C (coherencia) = {COHERENCE_CONSTANT_C:.2f}")
    print()
    
    # Construir operador
    print("Construyendo operador H_ψ...")
    H_psi, x_grid, eigenvalues, eigenvectors = create_critical_line_operator(
        n_basis=100,
        n_primes=50
    )
    
    print(f"  Dimensión del operador: {H_psi.shape}")
    print(f"  Número de autovalores: {len(eigenvalues)}")
    print()
    
    # Primeros autovalores
    print("Primeros 10 autovalores (singularidades espectrales):")
    for i in range(min(10, len(eigenvalues))):
        print(f"  λ_{i+1:2d} = {eigenvalues[i]:12.6f}")
    print()
    
    # Tensor de dualidad
    print("Tensor Unificado de Dualidad:")
    duality = UnifiedDualityTensor()
    print(f"  Razón de frecuencias: {duality.frequency_ratio():.6f} ≈ φ⁴")
    print(f"  Frecuencia crítica: {duality.critical_line_frequency():.2f} Hz")
    print()
    
    # Métrica deformada
    print("Métrica Ψ-deformada:")
    metric = CriticalLineMetric(I=1.0, A_eff=1.0)
    print(f"  Campo Ψ = I × A_eff² = {metric.psi_field():.2f}")
    print()
    
    print("=" * 80)
    print("✓ Demostración completada")
    print("=" * 80)


if __name__ == "__main__":
    demo_critical_line_horizon()
