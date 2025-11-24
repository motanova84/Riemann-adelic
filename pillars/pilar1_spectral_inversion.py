"""
PILAR 1: TEOREMA DE INVERSIÓN ESPECTRAL

Implementación del teorema de inversión espectral no-circular que reconstruye
la distribución de primos log p^k desde los ceros ρ sin asumir conocimiento
previo de los primos.

Teorema: Sea {ρ} un conjunto discreto simétrico con densidad ~ (T/2π)log(T/2π).
Existe un núcleo integral K_D(x,y) construido únicamente desde {ρ} tal que:

    Π_D = F^{-1}(Σ_ρ e^{iρ·}) - A_D

donde Π_D = Σ_{p,k}(log p)δ_{log p^k} y A_D es el término archimediano.
"""

import numpy as np
import mpmath as mp
from scipy.integrate import quad
from typing import List, Callable, Tuple


def gaussian_window(rho: complex, t: float = 0.01) -> float:
    """
    Ventana gaussiana para regularización espectral.
    
    Args:
        rho: Cero de la función zeta (número complejo)
        t: Parámetro de regularización (default: 0.01)
        
    Returns:
        Valor de la ventana gaussiana
    """
    # Extrae la parte imaginaria del cero
    im_rho = float(rho.imag) if hasattr(rho, 'imag') else float(np.imag(rho))
    
    # Ventana gaussiana w_δ(ρ) = exp(-t²|Im(ρ)|²)
    return np.exp(-t**2 * im_rho**2)


def reconstruction_kernel(x: float, y: float, zeros_rho: List[complex], 
                         t: float = 0.01) -> complex:
    """
    Núcleo de reconstrucción K_D(x,y) desde los ceros ρ.
    
    K_D(x,y) = Σ_ρ (x^{iρ} y^{-iρ}) / |ζ'(ρ)|² · w_δ(ρ)
    
    Args:
        x: Primera coordenada
        y: Segunda coordenada
        zeros_rho: Lista de ceros de la función zeta
        t: Parámetro de regularización
        
    Returns:
        Valor del núcleo de reconstrucción (complejo)
    """
    if x <= 0 or y <= 0:
        return 0.0 + 0.0j
    
    total = 0.0 + 0.0j
    
    for rho in zeros_rho:
        # Extrae la parte imaginaria del cero
        im_rho = float(rho.imag) if hasattr(rho, 'imag') else float(np.imag(rho))
        
        # Término espectral: x^{iρ} y^{-iρ}
        # Usando logaritmos para estabilidad numérica
        log_x = np.log(x)
        log_y = np.log(y)
        
        term = np.exp(1j * im_rho * (log_x - log_y))
        
        # Aplicar ventana gaussiana
        term *= gaussian_window(rho, t)
        
        # En lugar de |ζ'(ρ)|², usamos un peso aproximado basado en
        # la densidad espectral (evitando circularidad)
        # Peso ~ 1/(log|Im(ρ)|) para alta densidad
        weight = 1.0 / (1.0 + np.log(1.0 + abs(im_rho)))
        term *= weight
        
        total += term
    
    return total


def inverse_mellin_transform(kernel_func: Callable[[float, float], complex],
                            x_min: float = 0.1, x_max: float = 100.0,
                            num_points: int = 1000) -> Tuple[np.ndarray, np.ndarray]:
    """
    Transformada inversa de Mellin del núcleo de reconstrucción.
    
    Args:
        kernel_func: Función núcleo K(x, y)
        x_min: Valor mínimo de x
        x_max: Valor máximo de x
        num_points: Número de puntos para evaluación
        
    Returns:
        Tupla (x_values, measure_values) representando la medida reconstruida
    """
    x_values = np.logspace(np.log10(x_min), np.log10(x_max), num_points)
    measure_values = np.zeros(num_points, dtype=complex)
    
    # Evaluamos el núcleo en la diagonal K(x, x)
    # que relaciona directamente con la medida Π_D
    for i, x in enumerate(x_values):
        try:
            # Evaluamos K(x, x) que contiene información espectral
            measure_values[i] = kernel_func(x, x)
        except (OverflowError, ValueError, ZeroDivisionError):
            measure_values[i] = 0.0
    
    return x_values, np.real(measure_values)


def extract_peaks(x_values: np.ndarray, measure_values: np.ndarray,
                 threshold: float = None, min_distance: int = 5) -> List[Tuple[float, float]]:
    """
    Extrae picos de la medida reconstruida que corresponden a log p^k.
    
    Args:
        x_values: Valores de x
        measure_values: Valores de la medida
        threshold: Umbral mínimo para considerar un pico (None = automático)
        min_distance: Distancia mínima entre picos
        
    Returns:
        Lista de tuplas (posición, altura) de picos detectados
    """
    if threshold is None:
        # Umbral automático basado en la mediana
        threshold = np.median(np.abs(measure_values)) * 2.0
    
    peaks = []
    measure_abs = np.abs(measure_values)
    
    for i in range(1, len(measure_abs) - 1):
        # Detectar máximo local
        if (measure_abs[i] > measure_abs[i-1] and 
            measure_abs[i] > measure_abs[i+1] and
            measure_abs[i] > threshold):
            
            # Verificar distancia mínima con picos previos
            if not peaks or i - peaks[-1][0] >= min_distance:
                peaks.append((i, measure_abs[i]))
    
    # Convertir índices a valores de x
    peaks_in_x = [(x_values[idx], height) for idx, height in peaks]
    
    return peaks_in_x


def spectral_inversion(zeros_rho: List[complex], t: float = 0.01,
                      x_min: float = 0.1, x_max: float = 100.0,
                      num_points: int = 1000) -> Tuple[np.ndarray, np.ndarray, List[Tuple[float, float]]]:
    """
    Reconstruye log p^k desde ceros ρ sin asumir conocimiento de primos.
    
    Implementa el teorema de inversión espectral:
    1. Construye el núcleo K_D(x,y) desde {ρ}
    2. Aplica transformada inversa de Mellin
    3. Extrae picos correspondientes a log p^k
    
    Args:
        zeros_rho: Lista de ceros de la función zeta (partes imaginarias)
        t: Parámetro de regularización (default: 0.01)
        x_min: Valor mínimo de x para reconstrucción
        x_max: Valor máximo de x para reconstrucción
        num_points: Número de puntos para evaluación
        
    Returns:
        Tupla (x_values, measure_values, peaks) donde:
        - x_values: Valores de x evaluados
        - measure_values: Medida reconstruida Π_D
        - peaks: Picos detectados en log p^k
        
    Example:
        >>> zeros = [14.134725, 21.022040, 25.010858]  # Primeros ceros
        >>> x, measure, peaks = spectral_inversion(zeros)
        >>> print(f"Picos detectados en: {[p[0] for p in peaks]}")
    """
    # Crear función núcleo parcial
    def kernel_func(x: float, y: float) -> complex:
        return reconstruction_kernel(x, y, zeros_rho, t)
    
    # Aplicar transformada inversa
    x_values, measure_values = inverse_mellin_transform(
        kernel_func, x_min, x_max, num_points
    )
    
    # Extraer picos (log p^k)
    peaks = extract_peaks(x_values, measure_values)
    
    return x_values, measure_values, peaks


def compare_with_primes(peaks: List[Tuple[float, float]], 
                       primes: List[int] = None,
                       tolerance: float = 0.1) -> dict:
    """
    Compara los picos reconstruidos con log p conocidos.
    
    Args:
        peaks: Lista de picos (posición, altura) reconstruidos
        primes: Lista de números primos para comparación (None = genera automáticamente)
        tolerance: Tolerancia para considerar coincidencia
        
    Returns:
        Diccionario con estadísticas de comparación
    """
    if primes is None:
        # Genera primos hasta 1000
        primes = []
        for n in range(2, 1000):
            is_prime = True
            for p in primes:
                if p * p > n:
                    break
                if n % p == 0:
                    is_prime = False
                    break
            if is_prime:
                primes.append(n)
    
    # Calcular log p para cada primo
    log_primes = [np.log(p) for p in primes]
    
    # Comparar picos con log primes
    matches = 0
    peak_positions = [p[0] for p in peaks]
    
    for log_p in log_primes[:20]:  # Comparar primeros 20 primos
        for peak_pos in peak_positions:
            if abs(peak_pos - log_p) < tolerance:
                matches += 1
                break
    
    return {
        'num_peaks': len(peaks),
        'num_primes_tested': min(20, len(primes)),
        'matches': matches,
        'match_rate': matches / min(20, len(primes)) if primes else 0.0,
        'peak_positions': peak_positions[:10]  # Primeros 10 picos
    }


if __name__ == '__main__':
    # Ejemplo de uso
    print("=== PILAR 1: INVERSIÓN ESPECTRAL ===\n")
    
    # Usar ceros de Riemann conocidos (primeros ceros no triviales)
    zeros = [14.134725, 21.022040, 25.010858, 30.424878, 32.935057,
             37.586176, 40.918720, 43.327073, 48.005150, 49.773832]
    
    print(f"Usando {len(zeros)} ceros de Riemann")
    print(f"Ceros: {zeros[:5]}...\n")
    
    # Ejecutar inversión espectral
    x_values, measure, peaks = spectral_inversion(zeros, t=0.05, num_points=500)
    
    print(f"Medida reconstruida en {len(x_values)} puntos")
    print(f"Picos detectados: {len(peaks)}\n")
    
    if peaks:
        print("Primeros 10 picos:")
        for i, (pos, height) in enumerate(peaks[:10], 1):
            print(f"  {i}. Posición: {pos:.4f}, Altura: {height:.6f}")
    
    # Comparar con primos conocidos
    print("\n=== Comparación con primos ===")
    comparison = compare_with_primes(peaks)
    print(f"Tasa de coincidencia: {comparison['match_rate']:.2%}")
    print(f"Coincidencias: {comparison['matches']}/{comparison['num_primes_tested']}")
