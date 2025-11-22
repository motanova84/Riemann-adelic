"""
Teorema de Inversión Espectral (Primos ← Ceros)

Este módulo implementa el teorema de inversión espectral que permite
recuperar la medida de primos Π_D desde los ceros de la función Ξ(s).

Construcción:
    K_D(x,y) con ventana gaussiana e^{-tΔ}
    
Función principal:
    prime_measure_from_zeros(D, zeros, t)
    
Referencias:
    - Connes (1999), Trace formula in noncommutative geometry
    - Weil (1952), Sur les "formules explicites" de la théorie des nombres premiers
"""

import mpmath as mp
from typing import List, Tuple, Union
import numpy as np


def gaussian_kernel(x: Union[float, mp.mpf], y: Union[float, mp.mpf], t: float) -> mp.mpf:
    """
    Construye el núcleo gaussiano K_D(x, y) = e^{-t(x-y)²}.
    
    Este es el núcleo de calor que proporciona la ventana espectral
    para la inversión.
    
    Args:
        x: Primera coordenada
        y: Segunda coordenada  
        t: Parámetro de escala temporal
        
    Returns:
        Valor del núcleo gaussiano
    """
    diff = x - y
    return mp.exp(-t * diff * diff)


def construct_K_D(D: float, x: float, y: float, zeros: List[float], t: float = 1.0) -> mp.mpc:
    """
    Construye K_D(x,y) usando la ventana gaussiana e^{-tΔ}.
    
    El núcleo se construye como una suma sobre los ceros de Ξ(s),
    usando el operador de calor e^{-tΔ} como regularizador.
    
    Args:
        D: Parámetro del divisor
        x: Primera coordenada espacial
        y: Segunda coordenada espacial
        zeros: Lista de ceros de Ξ(s) (partes imaginarias γ)
        t: Parámetro temporal de difusión (default 1.0)
        
    Returns:
        Valor complejo del núcleo K_D(x,y)
    """
    mp.dps = 30  # Precisión de 30 dígitos decimales
    
    result = mp.mpc(0, 0)
    
    # Suma sobre los ceros con peso gaussiano
    for gamma in zeros:
        # Cada cero ρ = 1/2 + iγ contribuye con e^{-t|γ|²}
        weight = mp.exp(-t * gamma * gamma)
        
        # Contribución oscilatoria
        phase = mp.exp(1j * gamma * (x - y))
        
        result += weight * phase
    
    # Normalización
    normalization = mp.mpf(1) / mp.sqrt(2 * mp.pi * t)
    
    return normalization * result


def prime_measure_from_zeros(D: float, zeros: List[float], t: float = 1.0, 
                             max_log_p: float = 10.0, num_points: int = 100) -> Tuple[np.ndarray, np.ndarray]:
    """
    Recupera la aproximación de la medida de primos Π_D desde los ceros de Ξ.
    
    Este es el teorema de inversión espectral en acción:
    Dado el espectro (ceros), recuperamos la geometría (primos).
    
    Args:
        D: Parámetro del divisor
        zeros: Lista de ceros de Ξ(s) (partes imaginarias γ)
        t: Parámetro de escala temporal (default 1.0)
        max_log_p: Rango máximo de log(p) a considerar
        num_points: Número de puntos para la discretización
        
    Returns:
        Tupla (x_values, measure_values):
            x_values: Puntos en log(p)
            measure_values: Valores de la medida aproximada Π_D
    """
    mp.dps = 30
    
    # Discretización del espacio de log(p)
    x_values = np.linspace(0.1, max_log_p, num_points)
    measure_values = np.zeros(num_points)
    
    for i, x in enumerate(x_values):
        # La medida se obtiene de la traza del núcleo K_D(x,x)
        kernel_value = construct_K_D(D, x, x, zeros, t)
        measure_values[i] = float(kernel_value.real)
    
    return x_values, measure_values


def verify_prime_peaks(x_values: np.ndarray, measure_values: np.ndarray, 
                       expected_primes: List[int], tolerance: float = 0.3) -> List[Tuple[int, bool, float]]:
    """
    Verifica que la medida reconstruida tenga picos en log(p) para primos p.
    
    Args:
        x_values: Puntos en el espacio log(p)
        measure_values: Valores de la medida reconstruida
        expected_primes: Lista de primos esperados
        tolerance: Tolerancia para la detección de picos
        
    Returns:
        Lista de tuplas (primo, encontrado, posición_pico)
    """
    results = []
    
    for p in expected_primes:
        log_p = float(mp.log(p))
        
        # Buscar el índice más cercano a log(p)
        idx = np.argmin(np.abs(x_values - log_p))
        
        # Verificar si hay un pico local
        if idx > 0 and idx < len(measure_values) - 1:
            is_peak = (measure_values[idx] > measure_values[idx-1] and 
                      measure_values[idx] > measure_values[idx+1])
            
            # Verificar que el pico sea significativo
            local_max = np.max(measure_values[max(0, idx-5):min(len(measure_values), idx+6)])
            is_significant = measure_values[idx] >= (1 - tolerance) * local_max
            
            found = is_peak and is_significant
        else:
            found = False
        
        results.append((p, found, x_values[idx]))
    
    return results


def spectral_inversion_demo(zeros: List[float], max_primes: int = 10, t: float = 0.5) -> dict:
    """
    Demostración completa del teorema de inversión espectral.
    
    Args:
        zeros: Lista de ceros de Ξ(s)
        max_primes: Número máximo de primos a verificar
        t: Parámetro temporal
        
    Returns:
        Diccionario con resultados de la demostración
    """
    from sympy import primerange
    
    # Primos a verificar
    primes = list(primerange(2, 30))[:max_primes]
    
    # Reconstruir medida
    x_vals, measure_vals = prime_measure_from_zeros(D=1.0, zeros=zeros, t=t, 
                                                     max_log_p=4.0, num_points=200)
    
    # Verificar picos
    verification = verify_prime_peaks(x_vals, measure_vals, primes)
    
    num_found = sum(1 for _, found, _ in verification if found)
    success_rate = num_found / len(primes) if primes else 0
    
    return {
        'x_values': x_vals,
        'measure_values': measure_vals,
        'verification': verification,
        'num_primes_tested': len(primes),
        'num_primes_found': num_found,
        'success_rate': success_rate,
        't_parameter': t,
        'num_zeros_used': len(zeros)
    }
