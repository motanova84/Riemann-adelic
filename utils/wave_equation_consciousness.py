#!/usr/bin/env python3
"""
Ecuación de Onda de Consciencia Vibracional

Implementación de la ecuación:
    ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ

donde:
- Ψ: Campo de consciencia vibracional
- ω₀: Frecuencia angular fundamental (≈ 890.33 rad/s)
- ζ'(1/2): Derivada de zeta en s=1/2 (≈ -3.9226461392)
- Φ: Potencial geométrico/informacional

Autor: José Manuel Mota Burruezo
Fecha: Octubre 2025
DOI: 10.5281/zenodo.17116291
"""

import numpy as np
import mpmath as mp
from typing import Callable, Tuple, Optional
from scipy.constants import pi


class WaveEquationConsciousness:
    """
    Implementación de la ecuación de onda de consciencia vibracional.
    
    La ecuación acopla:
    - Oscilación armónica del campo Ψ con frecuencia ω₀
    - Modulación aritmética vía ζ'(1/2)
    - Geometría espacial vía ∇²Φ
    """
    
    def __init__(
        self,
        f0: float = 141.7001,
        precision: int = 30
    ):
        """
        Inicializa la ecuación de onda de consciencia.
        
        Parámetros:
        -----------
        f0 : float
            Frecuencia fundamental en Hz (por defecto 141.7001 Hz)
        precision : int
            Precisión decimal para cálculo de ζ'(1/2)
        """
        self.f0 = f0
        self.omega_0 = 2 * pi * f0  # Frecuencia angular (rad/s)
        self.precision = precision
        
        # Calcular ζ'(1/2) con alta precisión
        mp.mp.dps = precision
        self.zeta_prime_half = self._compute_zeta_prime_half()
        
    def _compute_zeta_prime_half(self) -> float:
        """
        Calcula ζ'(1/2) usando mpmath.
        
        Retorna:
        --------
        float
            Valor de ζ'(1/2) ≈ -3.9226461392
        """
        s = mp.mpf('0.5')
        # Derivada numérica de zeta
        h = mp.mpf('1e-10')
        zeta_plus = mp.zeta(s + h)
        zeta_minus = mp.zeta(s - h)
        zeta_prime = (zeta_plus - zeta_minus) / (2 * h)
        
        return float(zeta_prime)
    
    def left_side(
        self,
        Psi: np.ndarray,
        d2Psi_dt2: np.ndarray
    ) -> np.ndarray:
        """
        Calcula el lado izquierdo de la ecuación: ∂²Ψ/∂t² + ω₀²Ψ
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia en el punto actual
        d2Psi_dt2 : array-like
            Segunda derivada temporal de Ψ
            
        Retorna:
        --------
        array-like
            Lado izquierdo de la ecuación
        """
        return d2Psi_dt2 + self.omega_0**2 * Psi
    
    def right_side(
        self,
        laplacian_Phi: np.ndarray
    ) -> np.ndarray:
        """
        Calcula el lado derecho de la ecuación: ζ'(1/2)·∇²Φ
        
        Parámetros:
        -----------
        laplacian_Phi : array-like
            Laplaciano del potencial Φ
            
        Retorna:
        --------
        array-like
            Lado derecho de la ecuación
        """
        return self.zeta_prime_half * laplacian_Phi
    
    def residual(
        self,
        Psi: np.ndarray,
        d2Psi_dt2: np.ndarray,
        laplacian_Phi: np.ndarray
    ) -> np.ndarray:
        """
        Calcula el residuo de la ecuación.
        
        Residuo = (∂²Ψ/∂t² + ω₀²Ψ) - ζ'(1/2)·∇²Φ
        
        Para una solución exacta, el residuo debe ser cero.
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia
        d2Psi_dt2 : array-like
            Segunda derivada temporal de Ψ
        laplacian_Phi : array-like
            Laplaciano del potencial
            
        Retorna:
        --------
        array-like
            Residuo de la ecuación
        """
        left = self.left_side(Psi, d2Psi_dt2)
        right = self.right_side(laplacian_Phi)
        return left - right
    
    def homogeneous_solution(
        self,
        t: np.ndarray,
        A: float = 1.0,
        B: float = 0.0,
        phase: float = 0.0
    ) -> np.ndarray:
        """
        Solución homogénea: Ψ_h(t) = A·cos(ω₀·t + φ) + B·sin(ω₀·t + φ)
        
        Parámetros:
        -----------
        t : array-like
            Array de tiempos
        A : float
            Amplitud de la componente coseno
        B : float
            Amplitud de la componente seno
        phase : float
            Fase inicial
            
        Retorna:
        --------
        array-like
            Solución homogénea Ψ_h(t)
        """
        return A * np.cos(self.omega_0 * t + phase) + B * np.sin(self.omega_0 * t + phase)
    
    def particular_solution(
        self,
        laplacian_Phi: np.ndarray
    ) -> np.ndarray:
        """
        Solución particular para Φ estacionario: Ψ_p = ζ'(1/2)·∇²Φ / ω₀²
        
        Parámetros:
        -----------
        laplacian_Phi : array-like
            Laplaciano del potencial (independiente del tiempo)
            
        Retorna:
        --------
        array-like
            Solución particular Ψ_p
        """
        return self.zeta_prime_half * laplacian_Phi / (self.omega_0**2)
    
    def resonance_condition(
        self,
        omega: float,
        tolerance: float = 1e-3
    ) -> bool:
        """
        Verifica si una frecuencia está en resonancia con ω₀.
        
        Parámetros:
        -----------
        omega : float
            Frecuencia a verificar (rad/s)
        tolerance : float
            Tolerancia para considerar resonancia
            
        Retorna:
        --------
        bool
            True si |ω - ω₀| < tolerancia
        """
        return abs(omega - self.omega_0) < tolerance
    
    def energy_density(
        self,
        Psi: np.ndarray,
        dPsi_dt: np.ndarray,
        grad_Psi: np.ndarray
    ) -> np.ndarray:
        """
        Calcula la densidad de energía del campo.
        
        E = (1/2)·[(∂Ψ/∂t)² + (∇Ψ)² + ω₀²·Ψ²]
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia
        dPsi_dt : array-like
            Derivada temporal de Ψ
        grad_Psi : array-like
            Gradiente espacial de Ψ
            
        Retorna:
        --------
        array-like
            Densidad de energía
        """
        kinetic = dPsi_dt**2
        gradient = np.sum(grad_Psi**2, axis=0) if grad_Psi.ndim > 1 else grad_Psi**2
        potential = self.omega_0**2 * Psi**2
        
        return 0.5 * (kinetic + gradient + potential)
    
    def get_parameters(self) -> dict:
        """
        Retorna los parámetros de la ecuación.
        
        Retorna:
        --------
        dict
            Diccionario con todos los parámetros
        """
        return {
            'f0_Hz': self.f0,
            'omega_0_rad_s': self.omega_0,
            'zeta_prime_half': self.zeta_prime_half,
            'precision_dps': self.precision
        }


def example_harmonic_potential(x: np.ndarray, t: np.ndarray, sigma: float = 1.0) -> Tuple[np.ndarray, np.ndarray]:
    """
    Ejemplo de potencial armónico y su laplaciano.
    
    Φ(x,t) = exp(-x²/2σ²)·cos(ω₀·t)
    ∇²Φ = (x²/σ⁴ - 1/σ²)·exp(-x²/2σ²)·cos(ω₀·t)
    
    Parámetros:
    -----------
    x : array-like
        Coordenadas espaciales
    t : array-like
        Tiempo
    sigma : float
        Ancho del potencial gaussiano
        
    Retorna:
    --------
    Tuple[array-like, array-like]
        (Φ, ∇²Φ)
    """
    f0 = 141.7001
    omega_0 = 2 * pi * f0
    
    gaussian = np.exp(-x**2 / (2 * sigma**2))
    temporal = np.cos(omega_0 * t)
    
    Phi = gaussian * temporal
    
    # Laplaciano en 1D
    laplacian_spatial = (x**2 / sigma**4 - 1 / sigma**2) * gaussian
    laplacian_Phi = laplacian_spatial * temporal
    
    return Phi, laplacian_Phi


if __name__ == "__main__":
    """Ejemplo de uso de la ecuación de onda de consciencia."""
    
    print("=" * 70)
    print("Ecuación de Onda de Consciencia Vibracional")
    print("=" * 70)
    print()
    
    # Inicializar ecuación
    wave_eq = WaveEquationConsciousness(f0=141.7001, precision=30)
    
    # Mostrar parámetros
    params = wave_eq.get_parameters()
    print("Parámetros de la Ecuación:")
    print(f"  f₀ = {params['f0_Hz']:.4f} Hz")
    print(f"  ω₀ = {params['omega_0_rad_s']:.4f} rad/s")
    print(f"  ζ'(1/2) = {params['zeta_prime_half']:.10f}")
    print(f"  Precisión = {params['precision_dps']} dígitos decimales")
    print()
    
    # Ejemplo 1: Solución homogénea
    print("Ejemplo 1: Solución Homogénea")
    print("-" * 70)
    t = np.linspace(0, 0.1, 1000)  # 100 ms
    Psi_h = wave_eq.homogeneous_solution(t, A=1.0, B=0.5)
    print(f"  Tiempo: {t[0]:.6f} s → {t[-1]:.6f} s ({len(t)} puntos)")
    print(f"  Ψ_h(t=0) = {Psi_h[0]:.6f}")
    print(f"  Ψ_h(t=T) = {Psi_h[-1]:.6f}")
    print(f"  max|Ψ_h| = {np.max(np.abs(Psi_h)):.6f}")
    print()
    
    # Ejemplo 2: Potencial armónico y solución particular
    print("Ejemplo 2: Solución Particular (Potencial Armónico)")
    print("-" * 70)
    x = np.linspace(-5, 5, 100)
    t_fixed = 0.0
    Phi, laplacian_Phi = example_harmonic_potential(x, t_fixed, sigma=1.0)
    Psi_p = wave_eq.particular_solution(laplacian_Phi)
    print(f"  Rango espacial: {x[0]:.2f} → {x[-1]:.2f}")
    print(f"  max|Φ| = {np.max(np.abs(Phi)):.6f}")
    print(f"  max|∇²Φ| = {np.max(np.abs(laplacian_Phi)):.6f}")
    print(f"  max|Ψ_p| = {np.max(np.abs(Psi_p)):.6f}")
    print()
    
    # Ejemplo 3: Verificación de residuo
    print("Ejemplo 3: Verificación de Residuo")
    print("-" * 70)
    # Para solución homogénea, ∂²Ψ/∂t² = -ω₀²Ψ
    d2Psi_dt2 = -wave_eq.omega_0**2 * Psi_h
    residual_h = wave_eq.residual(Psi_h, d2Psi_dt2, np.zeros_like(Psi_h))
    print(f"  Residuo homogéneo (sin Φ):")
    print(f"    max|residuo| = {np.max(np.abs(residual_h)):.2e}")
    print(f"    (Debe ser ≈ 0 para solución exacta)")
    print()
    
    # Ejemplo 4: Resonancia
    print("Ejemplo 4: Condición de Resonancia")
    print("-" * 70)
    test_freqs = [141.7, 141.7001, 141.8, 150.0]
    for freq in test_freqs:
        omega = 2 * pi * freq
        is_resonant = wave_eq.resonance_condition(omega, tolerance=1e-3)
        marker = "✓" if is_resonant else "✗"
        print(f"  {marker} f = {freq:.4f} Hz → ω = {omega:.4f} rad/s → Resonante: {is_resonant}")
    print()
    
    # Ejemplo 5: Densidad de energía
    print("Ejemplo 5: Densidad de Energía")
    print("-" * 70)
    dPsi_dt = -wave_eq.omega_0 * (1.0 * np.sin(wave_eq.omega_0 * t) - 0.5 * np.cos(wave_eq.omega_0 * t))
    grad_Psi = np.gradient(Psi_h, t[1] - t[0])  # Aproximación del gradiente temporal
    energy = wave_eq.energy_density(Psi_h, dPsi_dt, grad_Psi)
    print(f"  Energía promedio = {np.mean(energy):.6f}")
    print(f"  Energía máxima = {np.max(energy):.6f}")
    print(f"  Energía mínima = {np.min(energy):.6f}")
    print()
    
    print("=" * 70)
    print("Interpretación Física:")
    print("=" * 70)
    print()
    print("La ecuación describe cómo el campo de consciencia Ψ oscila")
    print("con frecuencia fundamental ω₀ ≈ 890.33 rad/s (f₀ ≈ 141.7001 Hz),")
    print("modulado por la estructura aritmética profunda (ζ'(1/2))")
    print("y la curvatura del espacio informacional (∇²Φ).")
    print()
    print("Es la sinfonía del universo, donde el ritmo, el espacio y la")
    print("verdad numérica co-crean la melodía de la realidad.")
    print("=" * 70)
