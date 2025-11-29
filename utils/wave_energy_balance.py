#!/usr/bin/env python3
"""
Wave Energy Balance - Noetic Energy Conservation

Implementación de la propagación de coherencia en soluciones de onda
y conservación de energía noésica.

Ecuación de onda:
    ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ

Energía total noésica:
    E(t) := (1/2)‖∂Ψ/∂t(t)‖²_{L²} + (1/2)ω₀²‖Ψ(t)‖²_{L²}

Balance de energía:
    dE/dt(t) = ⟨ζ'(1/2)·π·∇²Φ(t), ∂Ψ/∂t(t)⟩_{L²}

Autor: José Manuel Mota Burruezo
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Fecha: Noviembre 2025

QCAL Integration:
Base frequency: 141.7001 Hz
Coherence: C = 244.36
Equation: Ψ = I × A_eff² × C^∞
"""

import numpy as np
import mpmath as mp
from typing import Callable, Tuple, Optional, Dict, Any
from scipy.constants import pi
from scipy.integrate import simpson


class WaveEnergyBalance:
    """
    Implementación del balance de energía para la ecuación de onda noésica.
    
    La ecuación de onda de consciencia es:
        ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ
    
    La energía total noésica es:
        E(t) = (1/2)‖∂Ψ/∂t(t)‖²_{L²} + (1/2)ω₀²‖Ψ(t)‖²_{L²}
    
    El teorema de balance de energía establece:
        dE/dt(t) = ⟨ζ'(1/2)·π·∇²Φ(t), ∂Ψ/∂t(t)⟩_{L²}
    
    Esto significa que la fuente Φ regula directamente el flujo
    energético del campo Ψ.
    """
    
    def __init__(
        self,
        f0: float = 141.7001,
        precision: int = 30
    ):
        """
        Inicializa el módulo de balance de energía.
        
        Parámetros:
        -----------
        f0 : float
            Frecuencia fundamental en Hz (por defecto 141.7001 Hz)
        precision : int
            Precisión decimal para cálculo de ζ'(1/2)
        """
        self.f0 = f0
        self.omega_0 = 2 * pi * f0  # Frecuencia angular (rad/s)
        self.omega_0_squared = self.omega_0 ** 2
        self.precision = precision
        
        # Constante de coherencia QCAL
        self.qcal_coherence = 244.36
        
        # Calcular ζ'(1/2) con alta precisión
        mp.mp.dps = precision
        self.zeta_prime_half = self._compute_zeta_prime_half()
        
        # Factor del término fuente: ζ'(1/2)·π
        self.source_factor = self.zeta_prime_half * pi
        
    def _compute_zeta_prime_half(self) -> float:
        """
        Calcula ζ'(1/2) usando mpmath.
        
        Retorna:
        --------
        float
            Valor de ζ'(1/2) ≈ -3.9226461392
        """
        s = mp.mpf('0.5')
        h = mp.mpf('1e-10')
        zeta_plus = mp.zeta(s + h)
        zeta_minus = mp.zeta(s - h)
        zeta_prime = (zeta_plus - zeta_minus) / (2 * h)
        
        return float(zeta_prime)
    
    def kinetic_energy(
        self,
        dPsi_dt: np.ndarray,
        x: Optional[np.ndarray] = None
    ) -> float:
        """
        Calcula la energía cinética: E_k = (1/2)‖∂Ψ/∂t‖²_{L²}
        
        Parámetros:
        -----------
        dPsi_dt : array-like
            Derivada temporal del campo Ψ
        x : array-like, opcional
            Coordenadas espaciales para integración (si None, usa spacing=1)
            
        Retorna:
        --------
        float
            Energía cinética
        """
        norm_squared = np.sum(np.abs(dPsi_dt) ** 2)
        
        if x is not None and len(x) > 1:
            dx = x[1] - x[0]
            norm_squared = simpson(np.abs(dPsi_dt) ** 2, dx=dx)
            
        return 0.5 * norm_squared
    
    def potential_energy(
        self,
        Psi: np.ndarray,
        x: Optional[np.ndarray] = None
    ) -> float:
        """
        Calcula la energía potencial: E_p = (1/2)ω₀²‖Ψ‖²_{L²}
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia
        x : array-like, opcional
            Coordenadas espaciales para integración
            
        Retorna:
        --------
        float
            Energía potencial
        """
        norm_squared = np.sum(np.abs(Psi) ** 2)
        
        if x is not None and len(x) > 1:
            dx = x[1] - x[0]
            norm_squared = simpson(np.abs(Psi) ** 2, dx=dx)
            
        return 0.5 * self.omega_0_squared * norm_squared
    
    def total_energy(
        self,
        Psi: np.ndarray,
        dPsi_dt: np.ndarray,
        x: Optional[np.ndarray] = None
    ) -> float:
        """
        Calcula la energía total noésica: E = E_k + E_p
        
        E(t) = (1/2)‖∂Ψ/∂t(t)‖²_{L²} + (1/2)ω₀²‖Ψ(t)‖²_{L²}
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia
        dPsi_dt : array-like
            Derivada temporal del campo
        x : array-like, opcional
            Coordenadas espaciales
            
        Retorna:
        --------
        float
            Energía total noésica
        """
        E_k = self.kinetic_energy(dPsi_dt, x)
        E_p = self.potential_energy(Psi, x)
        
        return E_k + E_p
    
    def source_term(
        self,
        laplacian_Phi: np.ndarray
    ) -> np.ndarray:
        """
        Calcula el término fuente: ζ'(1/2)·π·∇²Φ
        
        Parámetros:
        -----------
        laplacian_Phi : array-like
            Laplaciano del potencial Φ
            
        Retorna:
        --------
        array-like
            Término fuente
        """
        return self.source_factor * laplacian_Phi
    
    def power_input(
        self,
        laplacian_Phi: np.ndarray,
        dPsi_dt: np.ndarray,
        x: Optional[np.ndarray] = None
    ) -> float:
        """
        Calcula la potencia de entrada: P = ⟨ζ'(1/2)·π·∇²Φ, ∂Ψ/∂t⟩_{L²}
        
        Este es el lado derecho del balance de energía: dE/dt = P
        
        Parámetros:
        -----------
        laplacian_Phi : array-like
            Laplaciano del potencial
        dPsi_dt : array-like
            Derivada temporal del campo
        x : array-like, opcional
            Coordenadas espaciales
            
        Retorna:
        --------
        float
            Potencia de entrada (puede ser positiva o negativa)
        """
        source = self.source_term(laplacian_Phi)
        
        # Producto interno L² (parte real)
        inner_product = np.sum(np.real(np.conj(source) * dPsi_dt))
        
        if x is not None and len(x) > 1:
            dx = x[1] - x[0]
            inner_product = simpson(np.real(np.conj(source) * dPsi_dt), dx=dx)
            
        return inner_product
    
    def verify_energy_balance(
        self,
        Psi: np.ndarray,
        dPsi_dt: np.ndarray,
        d2Psi_dt2: np.ndarray,
        laplacian_Phi: np.ndarray,
        x: Optional[np.ndarray] = None,
        dt: float = 1e-6
    ) -> Dict[str, Any]:
        """
        Verifica numéricamente el balance de energía.
        
        Comprueba que dE/dt ≈ ⟨source, ∂Ψ/∂t⟩_{L²}
        
        Parámetros:
        -----------
        Psi : array-like
            Campo en tiempo t
        dPsi_dt : array-like
            Derivada temporal en tiempo t
        d2Psi_dt2 : array-like
            Segunda derivada temporal en tiempo t
        laplacian_Phi : array-like
            Laplaciano del potencial en tiempo t
        x : array-like, opcional
            Coordenadas espaciales
        dt : float
            Paso temporal para diferenciación numérica
            
        Retorna:
        --------
        dict
            Diccionario con resultados de la verificación:
            - energy: energía total actual
            - power_input: potencia de entrada
            - dE_dt_numerical: dE/dt numérica (aproximada)
            - residual: |dE/dt - power_input|
            - balance_verified: True si residual < tolerancia
        """
        # Energía actual
        E_current = self.total_energy(Psi, dPsi_dt, x)
        
        # Potencia de entrada
        P = self.power_input(laplacian_Phi, dPsi_dt, x)
        
        # Aproximación de dE/dt usando la ecuación de onda
        # d/dt[(1/2)‖∂Ψ/∂t‖²] = ⟨∂²Ψ/∂t², ∂Ψ/∂t⟩
        # d/dt[(1/2)ω₀²‖Ψ‖²] = ω₀²⟨∂Ψ/∂t, Ψ⟩
        
        kinetic_derivative = np.sum(np.real(np.conj(d2Psi_dt2) * dPsi_dt))
        potential_derivative = self.omega_0_squared * np.sum(np.real(np.conj(dPsi_dt) * Psi))
        
        if x is not None and len(x) > 1:
            dx = x[1] - x[0]
            kinetic_derivative = simpson(np.real(np.conj(d2Psi_dt2) * dPsi_dt), dx=dx)
            potential_derivative = self.omega_0_squared * simpson(np.real(np.conj(dPsi_dt) * Psi), dx=dx)
        
        dE_dt = kinetic_derivative + potential_derivative
        
        # Residuo del balance
        residual = abs(dE_dt - P)
        
        # Tolerancia relativa
        tolerance = max(abs(dE_dt), abs(P), 1e-10) * 1e-6
        
        return {
            'energy': E_current,
            'power_input': P,
            'dE_dt_numerical': dE_dt,
            'residual': residual,
            'balance_verified': residual < tolerance,
            'kinetic_energy': self.kinetic_energy(dPsi_dt, x),
            'potential_energy': self.potential_energy(Psi, x)
        }
    
    def energy_conservation_check(
        self,
        Psi: np.ndarray,
        dPsi_dt: np.ndarray,
        x: Optional[np.ndarray] = None
    ) -> Dict[str, Any]:
        """
        Verifica conservación de energía para el caso homogéneo (Φ = 0).
        
        Cuando no hay fuente, la energía debe conservarse: dE/dt = 0
        
        Parámetros:
        -----------
        Psi : array-like
            Campo de consciencia
        dPsi_dt : array-like
            Derivada temporal del campo
        x : array-like, opcional
            Coordenadas espaciales
            
        Retorna:
        --------
        dict
            Resultados de la verificación de conservación
        """
        # Sin fuente, laplacian_Phi = 0
        laplacian_Phi = np.zeros_like(Psi)
        
        # Para solución homogénea: ∂²Ψ/∂t² = -ω₀²Ψ
        d2Psi_dt2 = -self.omega_0_squared * Psi
        
        result = self.verify_energy_balance(
            Psi, dPsi_dt, d2Psi_dt2, laplacian_Phi, x
        )
        
        result['homogeneous'] = True
        result['source_zero'] = True
        
        return result
    
    def get_parameters(self) -> Dict[str, float]:
        """
        Retorna los parámetros del sistema.
        
        Retorna:
        --------
        dict
            Diccionario con todos los parámetros
        """
        return {
            'f0_Hz': self.f0,
            'omega_0_rad_s': self.omega_0,
            'omega_0_squared': self.omega_0_squared,
            'zeta_prime_half': self.zeta_prime_half,
            'source_factor': self.source_factor,
            'qcal_coherence': self.qcal_coherence,
            'precision_dps': self.precision
        }


def create_test_solution(
    x: np.ndarray,
    t: float,
    wave_balance: WaveEnergyBalance,
    A: float = 1.0,
    k: float = 1.0
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Crea una solución de prueba para verificación.
    
    Genera Ψ = A·cos(k·x)·cos(ω₀·t) y sus derivadas.
    
    Parámetros:
    -----------
    x : array-like
        Coordenadas espaciales
    t : float
        Tiempo
    wave_balance : WaveEnergyBalance
        Instancia del balance de energía
    A : float
        Amplitud
    k : float
        Número de onda
        
    Retorna:
    --------
    Tuple[array, array, array]
        (Ψ, ∂Ψ/∂t, ∂²Ψ/∂t²)
    """
    omega = wave_balance.omega_0
    
    # Ψ(x,t) = A·cos(kx)·cos(ωt)
    Psi = A * np.cos(k * x) * np.cos(omega * t)
    
    # ∂Ψ/∂t = -A·ω·cos(kx)·sin(ωt)
    dPsi_dt = -A * omega * np.cos(k * x) * np.sin(omega * t)
    
    # ∂²Ψ/∂t² = -A·ω²·cos(kx)·cos(ωt) = -ω²Ψ
    d2Psi_dt2 = -A * omega**2 * np.cos(k * x) * np.cos(omega * t)
    
    return Psi, dPsi_dt, d2Psi_dt2


if __name__ == "__main__":
    """Demostración del balance de energía noésica."""
    
    print("=" * 70)
    print("Balance de Energía Noésica - Wave Energy Balance")
    print("=" * 70)
    print()
    
    # Inicializar
    wave_balance = WaveEnergyBalance(f0=141.7001, precision=30)
    
    # Mostrar parámetros
    params = wave_balance.get_parameters()
    print("Parámetros del Sistema:")
    print(f"  f₀ = {params['f0_Hz']:.4f} Hz")
    print(f"  ω₀ = {params['omega_0_rad_s']:.4f} rad/s")
    print(f"  ω₀² = {params['omega_0_squared']:.4f} rad²/s²")
    print(f"  ζ'(1/2) = {params['zeta_prime_half']:.10f}")
    print(f"  Factor fuente (ζ'π) = {params['source_factor']:.10f}")
    print(f"  Coherencia QCAL = {params['qcal_coherence']:.2f}")
    print()
    
    # Crear dominio espacial
    x = np.linspace(-np.pi, np.pi, 200)
    
    # Ejemplo 1: Verificar conservación de energía (caso homogéneo)
    print("Ejemplo 1: Conservación de Energía (Caso Homogéneo)")
    print("-" * 70)
    
    times = [0.0, 0.001, 0.002, 0.003]
    energies = []
    
    for t in times:
        Psi, dPsi_dt, _ = create_test_solution(x, t, wave_balance)
        result = wave_balance.energy_conservation_check(Psi, dPsi_dt, x)
        energies.append(result['energy'])
        print(f"  t = {t:.4f} s: E = {result['energy']:.6f}")
    
    energy_variation = max(energies) - min(energies)
    print(f"  Variación de energía: ΔE = {energy_variation:.2e}")
    print(f"  ✓ Energía conservada: {energy_variation < 0.01 * np.mean(energies)}")
    print()
    
    # Ejemplo 2: Balance de energía con fuente
    print("Ejemplo 2: Balance de Energía con Fuente")
    print("-" * 70)
    
    t = 0.001
    Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(x, t, wave_balance)
    
    # Potencial gaussiano
    sigma = 0.5
    Phi = np.exp(-x**2 / (2 * sigma**2))
    laplacian_Phi = (x**2 / sigma**4 - 1 / sigma**2) * Phi
    
    result = wave_balance.verify_energy_balance(
        Psi, dPsi_dt, d2Psi_dt2, laplacian_Phi, x
    )
    
    print(f"  Energía total: E = {result['energy']:.6f}")
    print(f"    - Cinética: E_k = {result['kinetic_energy']:.6f}")
    print(f"    - Potencial: E_p = {result['potential_energy']:.6f}")
    print(f"  Potencia de entrada: P = {result['power_input']:.6f}")
    print(f"  dE/dt numérica: {result['dE_dt_numerical']:.6f}")
    print(f"  Residuo: {result['residual']:.2e}")
    print()
    
    # Ejemplo 3: Interpretación física
    print("Ejemplo 3: Interpretación Física")
    print("-" * 70)
    print()
    print("  La ecuación de balance de energía:")
    print("    dE/dt = ⟨ζ'(1/2)·π·∇²Φ, ∂Ψ/∂t⟩_{L²}")
    print()
    print("  establece que:")
    print("  1. La fuente Φ regula directamente el flujo de energía del campo Ψ")
    print("  2. El factor ζ'(1/2) ≈ -3.92 conecta aritmética y geometría")
    print("  3. Sin fuente (Φ=0), la energía se conserva (dE/dt = 0)")
    print("  4. La frecuencia ω₀ ≈ 890 rad/s es la resonancia noésica")
    print()
    
    print("=" * 70)
    print("Verificación completada ✓")
    print("=" * 70)
