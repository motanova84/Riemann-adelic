#!/usr/bin/env python3
"""
EL EJE: LA LÍNEA CRÍTICA - The Critical Line as Vibrational Axis
=================================================================

Este módulo implementa la visión poética y matemática de la línea crítica Re(s) = 1/2
como el eje vibracional del universo matemático, con los extremos ±1, los primos 
en espiral, y la frecuencia fundamental f₀ = 141.7001 Hz.

Conceptos Implementados:
-----------------------
I. La Línea Crítica Re(s) = 1/2
   - El eje vertical perfecto donde todo se equilibra
   - A un lado: caos (Re(s) < 1/2)
   - Al otro: simetría oculta (Re(s) > 1/2)
   - En el centro: el pulso coherente

II. Los Extremos: +1 y -1
   - +1: Donde la serie armónica diverge → ∞
   - -1: Donde ζ(-1) = -1/12 (explosión)
   - Límites de vibración sin disolución
   - Raíces del código dual: existencia / anti-existencia

III. Los Primos en Espiral
   - Cada primo p es un nodo de curvatura
   - Espiral aritmética: r(p) = log(p), θ(p) = p
   - Una serpiente de luz, el zumbido de la Magicicada
   - Danza en torno a la línea crítica

IV. La Frecuencia como Mar
   - Campo Ψ vibrando a f₀ = 141.7001 Hz
   - El medio donde los ceros respiran
   - Presión cuántica que permite estructura
   - Frecuencia que da fase al electrón

Visión Total:
------------
El eje no es solo vertical.
Es el árbol del universo.
+1 y -1 son sus raíces invertidas.
Los primos son las hojas que giran.
Y la frecuencia: el viento eterno que canta entre sus ramas.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
License: Creative Commons BY-NC-SA 4.0

References:
    - QCAL ∞³ Framework: DOI 10.5281/zenodo.17379721
    - Fundamental frequency: f₀ = 141.7001 Hz
    - Coherence constant: C = 244.36
"""

import numpy as np
import mpmath as mp
from typing import Tuple, List, Dict, Any, Optional
from dataclasses import dataclass
import warnings

# QCAL ∞³ Constants
F0_FUNDAMENTAL = 141.7001  # Hz - El viento eterno
COHERENCE_C = 244.36  # Constante de coherencia
CRITICAL_LINE_RE = 0.5  # Re(s) = 1/2 - El eje
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio φ
EULER_GAMMA = 0.5772156649015329  # Constante de Euler-Mascheroni

# Extremos del universo vibracional
PLUS_ONE = 1.0  # Divergencia de la serie armónica
MINUS_ONE = -1.0  # Explosión: ζ(-1) = -1/12
ZETA_AT_MINUS_ONE = -1.0 / 12.0  # El punto de anti-existencia


@dataclass
class CriticalLineAxis:
    """
    La Línea Crítica como Eje Vibracional.
    
    Representa el eje vertical Re(s) = 1/2 donde todo se equilibra.
    """
    re_s: float = CRITICAL_LINE_RE  # La vertical perfecta
    
    def equilibrium_point(self) -> float:
        """Retorna el punto de equilibrio: Re(s) = 1/2"""
        return self.re_s
    
    def distance_from_equilibrium(self, s: complex) -> float:
        """
        Calcula la distancia de un punto complejo s desde el equilibrio.
        
        Args:
            s: Punto complejo en el plano ℂ
            
        Returns:
            Distancia desde la línea crítica
        """
        return abs(s.real - self.re_s)
    
    def classify_region(self, s: complex) -> str:
        """
        Clasifica la región donde está el punto s.
        
        Args:
            s: Punto complejo
            
        Returns:
            'caos' (Re < 1/2), 'equilibrio' (Re = 1/2), o 'simetria_oculta' (Re > 1/2)
        """
        re = s.real
        
        if abs(re - self.re_s) < 1e-10:
            return 'equilibrio_pulso_coherente'
        elif re < self.re_s:
            return 'caos'
        else:
            return 'simetria_oculta'
    
    def coherence_field(self, t: float) -> float:
        """
        Campo de coherencia en la línea crítica para altura t.
        
        Ψ(t) = exp(-t²/(2·C)) donde C = 244.36
        
        Args:
            t: Altura en la línea crítica (parte imaginaria)
            
        Returns:
            Valor del campo de coherencia
        """
        return np.exp(-(t**2) / (2 * COHERENCE_C))


@dataclass
class VibrationalExtremes:
    """
    Los Extremos: +1 y -1.
    
    Representa los límites del universo vibracional.
    """
    plus_one: float = PLUS_ONE
    minus_one: float = MINUS_ONE
    
    def harmonic_divergence(self, n_terms: int = 1000) -> float:
        """
        Calcula la serie armónica parcial en +1.
        
        ζ(1) diverge, pero podemos ver la divergencia logarítmica:
        H_n = 1 + 1/2 + 1/3 + ... + 1/n ≈ log(n) + γ
        
        Args:
            n_terms: Número de términos en la serie
            
        Returns:
            Suma parcial de la serie armónica
        """
        return sum(1.0 / k for k in range(1, n_terms + 1))
    
    def zeta_at_minus_one(self) -> float:
        """
        Retorna ζ(-1) = -1/12.
        
        Este es el punto de "explosión" donde la zeta se comporta
        de manera anti-intuitiva, relacionado con regularización.
        
        Returns:
            ζ(-1) = -1/12
        """
        return ZETA_AT_MINUS_ONE
    
    def dual_code_roots(self) -> Dict[str, Any]:
        """
        Raíces del código dual: existencia / anti-existencia.
        
        Returns:
            Diccionario con las raíces duales
        """
        return {
            'existencia': {
                'punto': self.plus_one,
                'naturaleza': 'divergencia_positiva',
                'serie_armonica': 'infinito',
                'simbolo': '∞'
            },
            'anti_existencia': {
                'punto': self.minus_one,
                'naturaleza': 'regularizacion_negativa',
                'zeta_valor': self.zeta_at_minus_one(),
                'simbolo': '-1/12'
            }
        }
    
    def vibration_limit(self) -> Tuple[float, float]:
        """
        Límites de vibración sin disolución: [-1, +1].
        
        Returns:
            (límite_inferior, límite_superior)
        """
        return (self.minus_one, self.plus_one)


@dataclass
class PrimeSpiral:
    """
    Los Primos en Espiral.
    
    Cada primo p es un nodo de curvatura sobre el eje.
    Espiral aritmética: r(p) = log(p), θ(p) = p
    """
    
    def get_primes(self, n_primes: int) -> np.ndarray:
        """
        Obtiene los primeros n números primos.
        
        Args:
            n_primes: Número de primos deseados
            
        Returns:
            Array con los primeros n primos
        """
        primes = []
        candidate = 2
        
        while len(primes) < n_primes:
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
    
    def spiral_coordinates(self, p: float) -> Tuple[float, float]:
        """
        Coordenadas de la espiral para un primo p.
        
        r(p) = log(p)  - radio (curvatura logarítmica)
        θ(p) = p       - ángulo (el primo mismo)
        
        Args:
            p: Número primo
            
        Returns:
            (r, theta) - coordenadas polares
        """
        r = np.log(p)
        theta = p
        return r, theta
    
    def spiral_cartesian(self, p: float) -> Tuple[float, float]:
        """
        Coordenadas cartesianas de la espiral para un primo p.
        
        x = r(p) · cos(θ(p)) = log(p) · cos(p)
        y = r(p) · sin(θ(p)) = log(p) · sin(p)
        
        Args:
            p: Número primo
            
        Returns:
            (x, y) - coordenadas cartesianas
        """
        r, theta = self.spiral_coordinates(p)
        x = r * np.cos(theta)
        y = r * np.sin(theta)
        return x, y
    
    def curvature_nodes(self, n_primes: int = 100) -> Dict[str, np.ndarray]:
        """
        Calcula los nodos de curvatura para los primeros n primos.
        
        Cada primo es un nodo donde la espiral cambia de dirección.
        
        Args:
            n_primes: Número de primos a calcular
            
        Returns:
            Diccionario con arrays de coordenadas
        """
        primes = self.get_primes(n_primes)
        
        r_coords = np.log(primes)
        theta_coords = primes
        x_coords = r_coords * np.cos(theta_coords)
        y_coords = r_coords * np.sin(theta_coords)
        
        return {
            'primes': primes,
            'r': r_coords,
            'theta': theta_coords,
            'x': x_coords,
            'y': y_coords,
            'n_nodes': len(primes)
        }
    
    def euler_product_representation(self, s: complex, n_primes: int = 50) -> complex:
        """
        Representación del producto de Euler truncado.
        
        ζ(s) = ∏_p (1 - 1/p^s)^(-1)
        
        Args:
            s: Punto complejo
            n_primes: Número de primos en el producto
            
        Returns:
            Valor aproximado del producto
        """
        primes = self.get_primes(n_primes)
        product = 1.0 + 0j
        
        for p in primes:
            factor = 1.0 - (1.0 / (p ** s))
            if abs(factor) > 1e-15:  # Evitar división por cero
                product *= 1.0 / factor
        
        return product
    
    def magicicada_frequency(self, p: float) -> float:
        """
        Frecuencia de "zumbido" asociada a cada primo.
        
        El zumbido de la Magicicada es la modulación del primo
        con la frecuencia fundamental.
        
        f_p = f₀ · log(p) / (2π)
        
        Args:
            p: Número primo
            
        Returns:
            Frecuencia de zumbido en Hz
        """
        return F0_FUNDAMENTAL * np.log(p) / (2 * np.pi)


@dataclass
class FrequencyField:
    """
    La Frecuencia como Mar.
    
    Campo Ψ vibrando a f₀ = 141.7001 Hz.
    El medio invisible donde los ceros respiran.
    """
    f0: float = F0_FUNDAMENTAL  # Hz
    omega0: float = 2 * np.pi * F0_FUNDAMENTAL  # rad/s
    
    def wave_field(self, t: float, x: float = 0.0) -> complex:
        """
        Campo de onda vibracional.
        
        Ψ(x, t) = exp(i·ω₀·t) · exp(-x²/(2C))
        
        Args:
            t: Tiempo
            x: Posición espacial
            
        Returns:
            Amplitud compleja del campo
        """
        temporal = np.exp(1j * self.omega0 * t)
        spatial = np.exp(-(x**2) / (2 * COHERENCE_C))
        return temporal * spatial
    
    def quantum_pressure(self, t: float) -> float:
        """
        Presión cuántica que permite estructura.
        
        P(t) = ℏω₀ · |Ψ(t)|²
        
        Args:
            t: Tiempo
            
        Returns:
            Presión cuántica (unidades naturales)
        """
        psi = self.wave_field(t)
        pressure = self.omega0 * abs(psi)**2
        return pressure
    
    def electron_phase(self, t: float) -> float:
        """
        Fase del electrón modulada por la frecuencia.
        
        φ(t) = ω₀·t mod 2π
        
        Args:
            t: Tiempo
            
        Returns:
            Fase en radianes [0, 2π)
        """
        phase = (self.omega0 * t) % (2 * np.pi)
        return phase
    
    def breathing_zeros(self, t_zeros: np.ndarray) -> np.ndarray:
        """
        Los ceros "respirando" en el campo de frecuencia.
        
        Modulación de la amplitud de cada cero por el campo.
        
        Args:
            t_zeros: Partes imaginarias de los ceros de Riemann
            
        Returns:
            Amplitudes moduladas
        """
        amplitudes = np.array([
            abs(self.wave_field(0, t)) for t in t_zeros
        ])
        return amplitudes
    
    def eternal_wind(self) -> Dict[str, Any]:
        """
        El viento eterno que canta entre las ramas del árbol.
        
        Returns:
            Propiedades del viento eterno (campo de frecuencia)
        """
        return {
            'frecuencia': self.f0,
            'frecuencia_angular': self.omega0,
            'periodo': 1.0 / self.f0,
            'longitud_onda': 2 * np.pi / self.omega0,
            'coherencia': COHERENCE_C,
            'naturaleza': 'Campo vibracional fundamental',
            'metafora': 'El viento eterno que canta entre las ramas'
        }


class UniverseTree:
    """
    El Árbol del Universo - Visión Total.
    
    El eje no es solo vertical. Es el árbol del universo.
    +1 y -1 son sus raíces invertidas.
    Los primos son las hojas que giran.
    Y la frecuencia: el viento eterno que canta entre sus ramas.
    """
    
    def __init__(self):
        """Inicializa el árbol del universo con todos sus componentes."""
        self.eje = CriticalLineAxis()
        self.raices = VibrationalExtremes()
        self.hojas = PrimeSpiral()
        self.viento = FrequencyField()
    
    def describe_structure(self) -> Dict[str, Any]:
        """
        Describe la estructura completa del árbol del universo.
        
        Returns:
            Diccionario con la visión total
        """
        return {
            'eje_tronco': {
                'tipo': 'Línea Crítica Re(s) = 1/2',
                'naturaleza': 'Vertical perfecta, equilibrio perfecto',
                'componente': 'El árbol del universo'
            },
            'raices_invertidas': {
                'superior': {
                    'punto': self.raices.plus_one,
                    'naturaleza': 'Divergencia → ∞',
                    'simbolo': '+1'
                },
                'inferior': {
                    'punto': self.raices.minus_one,
                    'naturaleza': 'Explosión ζ(-1) = -1/12',
                    'simbolo': '-1'
                }
            },
            'hojas_giratorias': {
                'tipo': 'Primos en espiral',
                'ecuacion': 'r(p) = log(p), θ(p) = p',
                'metafora': 'Serpiente de luz, zumbido de Magicicada'
            },
            'viento_eterno': {
                'frecuencia': self.viento.f0,
                'naturaleza': 'Campo Ψ vibracional',
                'metafora': 'El viento que canta entre las ramas'
            }
        }
    
    def compute_vision_total(
        self,
        n_primes: int = 100,
        t_range: Tuple[float, float] = (0, 100)
    ) -> Dict[str, Any]:
        """
        Calcula la visión total del árbol del universo.
        
        Args:
            n_primes: Número de primos (hojas) a calcular
            t_range: Rango de alturas para el eje
            
        Returns:
            Visión completa con todos los componentes
        """
        # El eje vertical
        t_min, t_max = t_range
        t_axis = np.linspace(t_min, t_max, 1000)
        coherence_profile = np.array([
            self.eje.coherence_field(t) for t in t_axis
        ])
        
        # Las raíces
        dual_roots = self.raices.dual_code_roots()
        
        # Las hojas (primos en espiral)
        prime_nodes = self.hojas.curvature_nodes(n_primes)
        
        # El viento eterno
        wind_properties = self.viento.eternal_wind()
        
        return {
            'eje': {
                't_axis': t_axis,
                'coherence_profile': coherence_profile,
                'equilibrium': self.eje.equilibrium_point()
            },
            'raices': dual_roots,
            'hojas': prime_nodes,
            'viento': wind_properties,
            'vision_poetica': self._poetic_vision()
        }
    
    def _poetic_vision(self) -> str:
        """
        Retorna la visión poética del árbol.
        
        Returns:
            Texto poético describiendo el árbol del universo
        """
        return """
        ∞ VISIÓN TOTAL ∞
        
        El eje no es solo vertical.
        Es el árbol del universo.
        +1 y -1 son sus raíces invertidas.
        Los primos son las hojas que giran.
        Y la frecuencia:
        el viento eterno que canta entre sus ramas.
        
        Re(s) = 1/2 — La vertical perfecta
        f₀ = 141.7001 Hz — El viento que no cesa
        C = 244.36 — La coherencia que sostiene
        
        ∴ 𓂀 Ω ∞³
        """


def visualize_critical_line_regions(
    s_points: np.ndarray
) -> Dict[str, List[complex]]:
    """
    Visualiza las regiones alrededor de la línea crítica.
    
    Args:
        s_points: Array de puntos complejos
        
    Returns:
        Diccionario clasificando puntos por región
    """
    axis = CriticalLineAxis()
    
    regions = {
        'caos': [],
        'equilibrio_pulso_coherente': [],
        'simetria_oculta': []
    }
    
    for s in s_points:
        region = axis.classify_region(s)
        regions[region].append(s)
    
    return regions


def compute_prime_spiral_trajectory(
    n_primes: int = 200,
    full_turns: int = 10
) -> Dict[str, np.ndarray]:
    """
    Calcula la trayectoria completa de la espiral de primos.
    
    Args:
        n_primes: Número de primos a incluir
        full_turns: Número de vueltas completas a visualizar
        
    Returns:
        Diccionario con coordenadas de la espiral
    """
    spiral = PrimeSpiral()
    nodes = spiral.curvature_nodes(n_primes)
    
    # Añadir información de frecuencia
    frequencies = np.array([
        spiral.magicicada_frequency(p) for p in nodes['primes']
    ])
    
    nodes['frequencies'] = frequencies
    nodes['full_turns'] = full_turns
    
    return nodes


def demonstrate_el_eje():
    """
    Demostración completa de El Eje: La Línea Crítica.
    """
    print("=" * 80)
    print("EL EJE: LA LÍNEA CRÍTICA")
    print("Re(s) = 1/2 — El Árbol del Universo Vibracional")
    print("=" * 80)
    print()
    
    # Crear el árbol del universo
    universe = UniverseTree()
    
    # I. La Línea Crítica
    print("I. 🌳 LA LÍNEA CRÍTICA Re(s) = 1/2")
    print("-" * 50)
    print(f"   Equilibrio: Re(s) = {universe.eje.equilibrium_point()}")
    print(f"   Coherencia C = {COHERENCE_C:.2f}")
    print()
    
    # Clasificar algunos puntos
    test_points = [
        0.3 + 14j,  # Caos
        0.5 + 14j,  # Equilibrio
        0.7 + 14j   # Simetría oculta
    ]
    
    print("   Regiones del plano complejo:")
    for s in test_points:
        region = universe.eje.classify_region(s)
        print(f"   s = {s:.1f} → {region}")
    print()
    
    # II. Los Extremos
    print("II. ⚖️ LOS EXTREMOS: +1 y -1")
    print("-" * 50)
    print(f"   +1: Serie armónica H_100 ≈ {universe.raices.harmonic_divergence(100):.4f}")
    print(f"   -1: ζ(-1) = {universe.raices.zeta_at_minus_one():.6f}")
    print()
    
    dual_roots = universe.raices.dual_code_roots()
    print("   Código Dual:")
    print(f"   • Existencia (+1): {dual_roots['existencia']['simbolo']}")
    print(f"   • Anti-existencia (-1): {dual_roots['anti_existencia']['simbolo']}")
    print()
    
    # III. Los Primos en Espiral
    print("III. 🌀 LOS PRIMOS EN ESPIRAL")
    print("-" * 50)
    
    n_primes_display = 10
    primes = universe.hojas.get_primes(n_primes_display)
    
    print(f"   Primeros {n_primes_display} primos en coordenadas espirales:")
    print("   p    r(p)=log(p)    θ(p)=p       x          y         f_buzz(Hz)")
    print("   " + "-" * 70)
    
    for p in primes:
        r, theta = universe.hojas.spiral_coordinates(p)
        x, y = universe.hojas.spiral_cartesian(p)
        f_buzz = universe.hojas.magicicada_frequency(p)
        print(f"   {p:3.0f}  {r:8.4f}      {theta:6.1f}    {x:8.4f}   {y:8.4f}   {f_buzz:7.2f}")
    
    print()
    
    # IV. La Frecuencia como Mar
    print("IV. 🌊 LA FRECUENCIA COMO MAR")
    print("-" * 50)
    
    wind = universe.viento.eternal_wind()
    print(f"   Frecuencia fundamental: f₀ = {wind['frecuencia']:.6f} Hz")
    print(f"   Frecuencia angular: ω₀ = {wind['frecuencia_angular']:.6f} rad/s")
    print(f"   Período: T = {wind['periodo']:.8f} s")
    print(f"   Coherencia: C = {wind['coherencia']:.2f}")
    print()
    print(f"   {wind['metafora']}")
    print()
    
    # Visión Total
    print("∞ VISIÓN TOTAL")
    print("-" * 50)
    structure = universe.describe_structure()
    
    print(f"   Eje/Tronco: {structure['eje_tronco']['tipo']}")
    print(f"   Raíz Superior: {structure['raices_invertidas']['superior']['naturaleza']}")
    print(f"   Raíz Inferior: {structure['raices_invertidas']['inferior']['naturaleza']}")
    print(f"   Hojas: {structure['hojas_giratorias']['metafora']}")
    print(f"   Viento: {structure['viento_eterno']['metafora']}")
    print()
    
    # Visión poética
    print(universe._poetic_vision())
    print()
    
    print("=" * 80)
    print("✓ El Eje revelado — El Árbol del Universo visible")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_el_eje()
