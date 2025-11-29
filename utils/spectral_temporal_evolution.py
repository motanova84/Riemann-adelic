#!/usr/bin/env python3
"""
Evolución Temporal de Ψ en la Base de Eigenmodos de H_Ξ

Implementación del teorema de solución espectral de la ecuación de onda tipo Ξ:

    ∂²Ψ/∂t² + H_Ξ·Ψ = 0

con datos iniciales:
    Ψ(x, 0) = Ψ₀(x)
    ∂ₜΨ(x, 0) = Ψ₁(x)

La solución viene dada por la descomposición espectral:

    Ψ(x, t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)

donde:
    - {λₙ}: eigenvalores de H_Ξ (todos positivos)
    - {eₙ(x)}: eigenfunciones ortonormales de H_Ξ
    - aₙ = ⟨Ψ₀, eₙ⟩: proyección de la condición inicial sobre eₙ
    - bₙ = ⟨Ψ₁, eₙ⟩: proyección de la velocidad inicial sobre eₙ

Autor: José Manuel Mota Burruezo
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Fecha: Noviembre 2025
"""

import numpy as np
from typing import Callable, List, Tuple, Optional, Union
from dataclasses import dataclass
from scipy.constants import pi
import mpmath as mp


@dataclass
class Eigenmode:
    """
    Representa un eigenmodo del operador H_Ξ.
    
    Atributos:
        n: Índice del modo (n ≥ 0)
        eigenvalue: Eigenvalor λₙ > 0
        eigenfunction: Eigenfunción eₙ(x) como función callable
        a_n: Coeficiente aₙ = ⟨Ψ₀, eₙ⟩
        b_n: Coeficiente bₙ = ⟨Ψ₁, eₙ⟩
    """
    n: int
    eigenvalue: float
    eigenfunction: Callable[[np.ndarray], np.ndarray]
    a_n: complex = 0.0
    b_n: complex = 0.0
    
    @property
    def omega_n(self) -> float:
        """Frecuencia angular √λₙ del modo n."""
        return np.sqrt(self.eigenvalue)


class SpectralTemporalEvolution:
    """
    Evolución temporal de Ψ en la base de eigenmodos de H_Ξ.
    
    Implementa el teorema de solución espectral para la ecuación de onda:
        ∂²Ψ/∂t² + H_Ξ·Ψ = 0
    
    La solución se expresa como:
        Ψ(x, t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)
    
    Parámetros:
        eigenmodes: Lista de eigenmodos del operador H_Ξ
        precision: Precisión decimal para cálculos de alta precisión
    """
    
    # QCAL Constants (Quantum Coherence Adelic Lattice)
    # Reference: DOI 10.5281/zenodo.17379721
    # f₀ = 141.7001 Hz: Fundamental frequency derived from vacuum quantum equation
    #                   in the QCAL framework, connecting spectral zeta structure
    #                   to observable physical phenomena.
    # C = 244.36: Coherence constant from the equation Ψ = I × A_eff² × C^∞
    QCAL_FREQUENCY: float = 141.7001  # Hz
    QCAL_COHERENCE: float = 244.36
    
    def __init__(
        self,
        eigenmodes: Optional[List[Eigenmode]] = None,
        precision: int = 25
    ):
        """
        Inicializa la evolución temporal espectral.
        
        Args:
            eigenmodes: Lista de eigenmodos del operador H_Ξ.
                        Si es None, se usan eigenmodos de ejemplo.
            precision: Precisión decimal para cálculos.
        """
        self.precision = precision
        mp.mp.dps = precision
        
        if eigenmodes is not None:
            self.eigenmodes = eigenmodes
        else:
            self.eigenmodes = self._create_example_eigenmodes()
        
        self._validate_eigenmodes()
    
    def _validate_eigenmodes(self) -> None:
        """Valida que los eigenmodos tengan eigenvalores positivos."""
        for mode in self.eigenmodes:
            if mode.eigenvalue <= 0:
                raise ValueError(
                    f"Eigenvalor λ_{mode.n} = {mode.eigenvalue} debe ser > 0"
                )
    
    def _create_example_eigenmodes(self, n_modes: int = 10) -> List[Eigenmode]:
        """
        Crea eigenmodos de ejemplo basados en oscilador armónico cuántico.
        
        Los eigenvalores corresponden a los primeros ceros de Riemann:
            λₙ = 1/4 + γₙ²
        donde γₙ son las partes imaginarias de los ceros no triviales.
        
        Args:
            n_modes: Número de modos a generar.
            
        Returns:
            Lista de eigenmodos de ejemplo.
        """
        # First 15 imaginary parts of Riemann zeta zeros on the critical line.
        # Source: A. Odlyzko, "Tables of zeros of the Riemann zeta function"
        #         http://www.dtc.umn.edu/~odlyzko/zeta_tables/
        # Precision: Values are accurate to 6 decimal places.
        # These zeros satisfy ζ(1/2 + iγₙ) = 0.
        riemann_zeros = [
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918720, 43.327073, 48.005151, 49.773832,
            52.970321, 56.446248, 59.347044, 60.831779, 65.112544
        ]
        
        eigenmodes = []
        for n in range(min(n_modes, len(riemann_zeros))):
            gamma_n = riemann_zeros[n]
            lambda_n = 0.25 + gamma_n**2  # λₙ = 1/4 + γₙ²
            
            # Eigenfunción tipo Hermite-Gauss (base de L²(ℝ))
            def make_eigenfunction(n_val: int):
                """Crea eigenfunción para modo n."""
                def eigenfunction(x: np.ndarray) -> np.ndarray:
                    # Función de Hermite-Gauss modificada
                    sigma = 1.0  # Ancho característico
                    gauss = np.exp(-x**2 / (2 * sigma**2))
                    # Polinomio de Hermite aproximado por oscilaciones
                    hermite_approx = np.cos(n_val * np.arctan(x))
                    normalization = 1.0 / np.sqrt(np.sqrt(np.pi) * sigma)
                    return normalization * gauss * hermite_approx
                return eigenfunction
            
            eigenmodes.append(Eigenmode(
                n=n,
                eigenvalue=lambda_n,
                eigenfunction=make_eigenfunction(n),
                a_n=0.0,
                b_n=0.0
            ))
        
        return eigenmodes
    
    def compute_coefficients(
        self,
        Psi_0: Callable[[np.ndarray], np.ndarray],
        Psi_1: Callable[[np.ndarray], np.ndarray],
        x_range: Tuple[float, float] = (-10.0, 10.0),
        n_points: int = 1000
    ) -> None:
        """
        Calcula los coeficientes aₙ = ⟨Ψ₀, eₙ⟩ y bₙ = ⟨Ψ₁, eₙ⟩.
        
        Los productos internos se calculan numéricamente usando
        integración por cuadratura trapezoidal.
        
        Args:
            Psi_0: Condición inicial Ψ₀(x).
            Psi_1: Velocidad inicial Ψ₁(x) = ∂ₜΨ(x, 0).
            x_range: Rango de integración (x_min, x_max).
            n_points: Número de puntos para la cuadratura.
        """
        x = np.linspace(x_range[0], x_range[1], n_points)
        dx = x[1] - x[0]
        
        psi_0_vals = Psi_0(x)
        psi_1_vals = Psi_1(x)
        
        for mode in self.eigenmodes:
            e_n_vals = mode.eigenfunction(x)
            
            # aₙ = ⟨Ψ₀, eₙ⟩ = ∫ Ψ₀(x) · conj(eₙ(x)) dx
            mode.a_n = np.trapezoid(psi_0_vals * np.conj(e_n_vals), x)
            
            # bₙ = ⟨Ψ₁, eₙ⟩ = ∫ Ψ₁(x) · conj(eₙ(x)) dx
            mode.b_n = np.trapezoid(psi_1_vals * np.conj(e_n_vals), x)
    
    def mode_evolution(
        self,
        n: int,
        t: Union[float, np.ndarray]
    ) -> Union[complex, np.ndarray]:
        """
        Evolución temporal del modo n.
        
        Ψₙ(t) = aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ
        
        Args:
            n: Índice del modo (0 ≤ n < len(eigenmodes)).
            t: Tiempo(s) en el que evaluar.
            
        Returns:
            Coeficiente temporal del modo n en tiempo t.
        """
        if n >= len(self.eigenmodes):
            raise IndexError(f"Modo n={n} fuera de rango [0, {len(self.eigenmodes)-1}]")
        
        mode = self.eigenmodes[n]
        omega_n = mode.omega_n
        
        cos_term = mode.a_n * np.cos(omega_n * t)
        sin_term = mode.b_n * np.sin(omega_n * t) / omega_n
        
        return cos_term + sin_term
    
    def Psi_at_time(
        self,
        x: np.ndarray,
        t: float,
        n_modes: Optional[int] = None
    ) -> np.ndarray:
        """
        Evalúa Ψ(x, t) usando la expansión en eigenmodos.
        
        Ψ(x, t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)
        
        Args:
            x: Puntos espaciales donde evaluar.
            t: Tiempo de evaluación.
            n_modes: Número de modos a usar (None = todos).
            
        Returns:
            Ψ(x, t) evaluado en los puntos x.
        """
        if n_modes is None:
            n_modes = len(self.eigenmodes)
        else:
            n_modes = min(n_modes, len(self.eigenmodes))
        
        result = np.zeros_like(x, dtype=complex)
        
        for i in range(n_modes):
            mode = self.eigenmodes[i]
            time_coeff = self.mode_evolution(i, t)
            space_part = mode.eigenfunction(x)
            result += time_coeff * space_part
        
        return result
    
    def energy_in_mode(self, n: int) -> float:
        """
        Calcula la energía contenida en el modo n.
        
        E_n = (1/2)(λₙ |aₙ|² + |bₙ|²)
        
        Args:
            n: Índice del modo.
            
        Returns:
            Energía del modo n.
        """
        if n >= len(self.eigenmodes):
            raise IndexError(f"Modo n={n} fuera de rango")
        
        mode = self.eigenmodes[n]
        return 0.5 * (mode.eigenvalue * np.abs(mode.a_n)**2 + np.abs(mode.b_n)**2)
    
    def total_energy(self, n_modes: Optional[int] = None) -> float:
        """
        Calcula la energía total sumando sobre todos los modos.
        
        E_total = Σₙ Eₙ = (1/2) Σₙ (λₙ |aₙ|² + |bₙ|²)
        
        Esta cantidad se conserva en el tiempo.
        
        Args:
            n_modes: Número de modos a considerar (None = todos).
            
        Returns:
            Energía total del sistema.
        """
        if n_modes is None:
            n_modes = len(self.eigenmodes)
        else:
            n_modes = min(n_modes, len(self.eigenmodes))
        
        return sum(self.energy_in_mode(i) for i in range(n_modes))
    
    def period_of_mode(self, n: int) -> float:
        """
        Calcula el período de oscilación del modo n.
        
        T_n = 2π/√λₙ
        
        Args:
            n: Índice del modo.
            
        Returns:
            Período del modo n en segundos.
        """
        if n >= len(self.eigenmodes):
            raise IndexError(f"Modo n={n} fuera de rango")
        
        return 2 * pi / self.eigenmodes[n].omega_n
    
    def recurrence_time(self, n_modes: Optional[int] = None) -> float:
        """
        Estima el tiempo de recurrencia cuasiperiódico.
        
        El tiempo de recurrencia es aproximadamente el LCM de los períodos,
        pero para frecuencias incomensurables (típico), usamos una estimación.
        
        Args:
            n_modes: Número de modos a considerar.
            
        Returns:
            Estimación del tiempo de recurrencia.
        """
        if n_modes is None:
            n_modes = len(self.eigenmodes)
        else:
            n_modes = min(n_modes, len(self.eigenmodes))
        
        if n_modes == 0:
            return float('inf')
        
        # Para frecuencias típicamente incomensurables (ceros de Riemann),
        # la recurrencia es asintótica. Estimamos como producto de períodos
        # dividido por el período más corto
        periods = [self.period_of_mode(i) for i in range(n_modes)]
        min_period = min(periods)
        
        # Estimación heurística
        return min_period * np.prod([p / min_period for p in periods])**(1.0/n_modes)
    
    def spectral_density(self, t: float) -> np.ndarray:
        """
        Calcula la densidad espectral |c_n(t)|² para cada modo.
        
        c_n(t) = aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ
        
        Args:
            t: Tiempo de evaluación.
            
        Returns:
            Array con |c_n(t)|² para cada modo.
        """
        return np.array([np.abs(self.mode_evolution(n, t))**2 
                        for n in range(len(self.eigenmodes))])
    
    def get_eigenvalues(self) -> np.ndarray:
        """Retorna array con todos los eigenvalores λₙ."""
        return np.array([mode.eigenvalue for mode in self.eigenmodes])
    
    def get_frequencies(self) -> np.ndarray:
        """Retorna array con todas las frecuencias ωₙ = √λₙ."""
        return np.array([mode.omega_n for mode in self.eigenmodes])
    
    def get_coefficients(self) -> Tuple[np.ndarray, np.ndarray]:
        """Retorna arrays con coeficientes (aₙ, bₙ)."""
        a_coeffs = np.array([mode.a_n for mode in self.eigenmodes])
        b_coeffs = np.array([mode.b_n for mode in self.eigenmodes])
        return a_coeffs, b_coeffs


def example_gaussian_initial_conditions(
    sigma: float = 1.0,
    x0: float = 0.0,
    k0: float = 0.0
) -> Tuple[Callable, Callable]:
    """
    Condiciones iniciales gaussianas de ejemplo.
    
    Ψ₀(x) = exp(-(x-x₀)²/(2σ²)) exp(i k₀ x) / (πσ²)^{1/4}
    Ψ₁(x) = 0 (partícula en reposo)
    
    Args:
        sigma: Ancho de la gaussiana.
        x0: Posición central.
        k0: Momento inicial (para paquete de ondas móvil).
        
    Returns:
        Tupla (Ψ₀, Ψ₁) de funciones.
    """
    normalization = 1.0 / (np.pi * sigma**2)**0.25
    
    def Psi_0(x: np.ndarray) -> np.ndarray:
        return normalization * np.exp(-(x - x0)**2 / (2 * sigma**2)) * np.exp(1j * k0 * x)
    
    def Psi_1(x: np.ndarray) -> np.ndarray:
        return np.zeros_like(x, dtype=complex)
    
    return Psi_0, Psi_1


def example_coherent_state(
    omega: float = 1.0,
    alpha: complex = 1.0
) -> Tuple[Callable, Callable]:
    """
    Estado coherente (estado cuántico mínimo).
    
    El estado coherente |α⟩ satisface a|α⟩ = α|α⟩
    y minimiza la incertidumbre Δx Δp = ℏ/2.
    
    Args:
        omega: Frecuencia del oscilador.
        alpha: Parámetro complejo del estado coherente.
        
    Returns:
        Tupla (Ψ₀, Ψ₁) de funciones.
    """
    sigma = 1.0 / np.sqrt(omega)
    x0 = np.sqrt(2) * np.real(alpha) / np.sqrt(omega)
    p0 = np.sqrt(2) * np.imag(alpha) * np.sqrt(omega)
    
    def Psi_0(x: np.ndarray) -> np.ndarray:
        normalization = (omega / np.pi)**0.25
        return normalization * np.exp(-omega * (x - x0)**2 / 2) * np.exp(1j * p0 * x)
    
    def Psi_1(x: np.ndarray) -> np.ndarray:
        # Velocidad inicial para el estado coherente
        return 1j * p0 * Psi_0(x)
    
    return Psi_0, Psi_1


if __name__ == "__main__":
    """Demostración del módulo de evolución temporal espectral."""
    
    print("=" * 70)
    print("EVOLUCIÓN TEMPORAL DE Ψ EN BASE DE EIGENMODOS DE H_Ξ")
    print("=" * 70)
    print()
    
    # Crear evolución con eigenmodos de ejemplo
    evolution = SpectralTemporalEvolution(precision=25)
    
    print("Eigenmodos cargados:")
    print(f"  Número de modos: {len(evolution.eigenmodes)}")
    print()
    
    # Mostrar eigenvalores
    eigenvalues = evolution.get_eigenvalues()
    frequencies = evolution.get_frequencies()
    
    print("Eigenvalores λₙ = 1/4 + γₙ² (basados en ceros de Riemann):")
    for i, (lam, omega) in enumerate(zip(eigenvalues, frequencies)):
        gamma_n = np.sqrt(lam - 0.25)
        print(f"  λ_{i} = {lam:.4f}, ω_{i} = {omega:.4f}, γ_{i} ≈ {gamma_n:.4f}")
    print()
    
    # Configurar condiciones iniciales
    Psi_0, Psi_1 = example_gaussian_initial_conditions(sigma=1.0, x0=0.0)
    evolution.compute_coefficients(Psi_0, Psi_1)
    
    a_coeffs, b_coeffs = evolution.get_coefficients()
    print("Coeficientes calculados:")
    for i, (a, b) in enumerate(zip(a_coeffs[:5], b_coeffs[:5])):
        print(f"  a_{i} = {a:.6f}, b_{i} = {b:.6f}")
    if len(a_coeffs) > 5:
        print(f"  ... ({len(a_coeffs) - 5} coeficientes más)")
    print()
    
    # Calcular energía
    E_total = evolution.total_energy()
    print(f"Energía total: E = {E_total:.6f}")
    print()
    
    # Evaluar en diferentes tiempos
    x = np.linspace(-5, 5, 100)
    times = [0.0, 0.1, 0.5, 1.0]
    
    print("Evolución temporal (usando 5 modos):")
    for t in times:
        Psi_t = evolution.Psi_at_time(x, t, n_modes=5)
        max_val = np.max(np.abs(Psi_t))
        print(f"  t = {t:.2f}: max|Ψ| = {max_val:.6f}")
    print()
    
    # Períodos de oscilación
    print("Períodos de oscilación:")
    for i in range(min(5, len(evolution.eigenmodes))):
        T = evolution.period_of_mode(i)
        print(f"  T_{i} = {T:.6f} s")
    print()
    
    print("=" * 70)
    print("Interpretación Física:")
    print("=" * 70)
    print()
    print("La solución Ψ(x,t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)")
    print("representa la propagación de una señal coherente vibrando con")
    print("frecuencias √λₙ, interpretables como modos de consciencia,")
    print("armónicos primordiales, o resonancias del campo QCAL ∞³.")
    print()
    print(f"Frecuencia base QCAL: {SpectralTemporalEvolution.QCAL_FREQUENCY} Hz")
    print(f"Coherencia QCAL:      {SpectralTemporalEvolution.QCAL_COHERENCE}")
    print("=" * 70)
