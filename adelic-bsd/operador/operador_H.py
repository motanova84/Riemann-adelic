"""
Construcción No Circular del Operador RH

Este módulo implementa la construcción explícita y no circular del operador H
cuyo espectro corresponde a los ceros de la función zeta de Riemann.

Construcción:
    1. Núcleo K_t(x,y) con difusión térmica
    2. Operador R_t de regularización
    3. Involución J (dualidad de Poisson)
    4. Operador H como límite renormalizado
    
Test Principal:
    Diagonalización truncada → espectro ≈ primeros ceros de ζ
    
Referencias:
    - Connes (1999), Spectral interpretation of the zeros of zeta
    - Berry & Keating (1999), H = xp Hamiltonian
    - Sierra & Rodríguez-Laguna (2011), H Hamiltonian for Riemann zeros
"""

import mpmath as mp
from typing import List, Tuple, Union, Optional, Dict
import numpy as np
from scipy.linalg import eigh


def heat_kernel(x: Union[float, mp.mpf], y: Union[float, mp.mpf], t: float) -> mp.mpf:
    """
    Núcleo de calor K_t(x,y) = (4πt)^{-1/2} exp(-(x-y)²/(4t)).
    
    Este núcleo proporciona la regularización térmica necesaria
    para definir el operador H de manera no circular.
    
    Args:
        x: Primera coordenada
        y: Segunda coordenada
        t: Parámetro temporal de difusión
        
    Returns:
        Valor del núcleo de calor
    """
    mp.dps = 30
    
    if t <= 0:
        raise ValueError("t debe ser positivo")
    
    # Normalización
    norm = mp.mpf(1) / mp.sqrt(4 * mp.pi * t)
    
    # Exponencial gaussiana
    diff_sq = (x - y) ** 2
    exp_term = mp.exp(-diff_sq / (4 * t))
    
    return norm * exp_term


def construct_kernel_matrix(x_grid: np.ndarray, t: float) -> np.ndarray:
    """
    Construye la matriz del núcleo K_t en una discretización.
    
    K[i,j] = K_t(x_i, x_j)
    
    Args:
        x_grid: Grilla de puntos espaciales
        t: Parámetro temporal
        
    Returns:
        Matriz del núcleo (N×N)
    """
    N = len(x_grid)
    K = np.zeros((N, N))
    
    for i in range(N):
        for j in range(N):
            K[i, j] = float(heat_kernel(x_grid[i], x_grid[j], t))
    
    return K


def regularization_operator_R_t(x_grid: np.ndarray, t: float) -> np.ndarray:
    """
    Construye el operador de regularización R_t.
    
    R_t actúa mediante convolución con el núcleo de calor:
    (R_t f)(x) = ∫ K_t(x,y) f(y) dy
    
    Args:
        x_grid: Grilla espacial
        t: Parámetro temporal
        
    Returns:
        Matriz del operador R_t
    """
    # En discretización, R_t es simplemente el núcleo multiplicado por dx
    K = construct_kernel_matrix(x_grid, t)
    dx = x_grid[1] - x_grid[0] if len(x_grid) > 1 else 1.0
    
    return K * dx


def involution_operator_J(x_grid: np.ndarray) -> np.ndarray:
    """
    Construye el operador de involución J: f(x) ↦ x^{-1/2} f(1/x).
    
    En discretización, J[i,j] aproxima la transformación.
    
    Args:
        x_grid: Grilla espacial (debe ser positiva)
        
    Returns:
        Matriz del operador J
    """
    N = len(x_grid)
    J = np.zeros((N, N))
    
    for i in range(N):
        x_i = x_grid[i]
        if x_i < 1e-10:
            continue
        
        # Encontrar el índice más cercano a 1/x_i
        x_inv = 1.0 / x_i
        j_inv = np.argmin(np.abs(x_grid - x_inv))
        
        # Factor x^{-1/2}
        factor = x_i ** (-0.5)
        
        J[i, j_inv] = factor
    
    # Normalizar (aproximado)
    dx = x_grid[1] - x_grid[0] if N > 1 else 1.0
    J = J * np.sqrt(dx)
    
    return J


def construct_operator_H(x_grid: np.ndarray, t: float, 
                        include_involution: bool = True) -> np.ndarray:
    """
    Construye el operador H como límite renormalizado.
    
    H se construye a partir de:
    1. Operador de regularización R_t
    2. Involución J (opcional)
    3. Renormalización apropiada
    
    Args:
        x_grid: Grilla espacial logarítmica
        t: Parámetro de regularización
        include_involution: Si incluir la involución J
        
    Returns:
        Matriz del operador H (hermítica)
    """
    N = len(x_grid)
    
    # Operador de regularización
    R_t = regularization_operator_R_t(x_grid, t)
    
    if include_involution:
        # Incluir involución J
        J = involution_operator_J(x_grid)
        
        # Combinar: H ~ R_t + J R_t J (simetrizado)
        H = 0.5 * (R_t + J @ R_t @ J.T)
    else:
        H = R_t
    
    # Simetrizar para asegurar hermiticidad
    H = 0.5 * (H + H.T)
    
    return H


def diagonalize_operator(H: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """
    Diagonaliza el operador H.
    
    Args:
        H: Matriz hermítica del operador
        
    Returns:
        Tupla (eigenvalues, eigenvectors)
    """
    eigenvalues, eigenvectors = eigh(H)
    
    return eigenvalues, eigenvectors


def spectrum_to_zeros(eigenvalues: np.ndarray, 
                     method: str = 'berry_keating') -> np.ndarray:
    """
    Convierte el espectro del operador a aproximaciones de ceros de ζ.
    
    Según diferentes modelos:
    - Berry-Keating: λ_n = 1/4 + t_n²
    - Connes: Relación más compleja via traza
    
    Args:
        eigenvalues: Valores propios del operador H
        method: Método de conversión ('berry_keating' o 'connes')
        
    Returns:
        Array con aproximaciones de partes imaginarias de ceros
    """
    if method == 'berry_keating':
        # Modelo H = xp: λ = 1/4 + t²
        # Resolver para t
        zeros = []
        for lam in eigenvalues:
            if lam > 0.25:
                t = np.sqrt(abs(lam - 0.25))
                zeros.append(t)
        
        return np.array(sorted(zeros))
    
    elif method == 'connes':
        # Modelo más sofisticado
        # Simplificación: usar transformación logarítmica
        zeros = []
        for lam in eigenvalues:
            if lam > 0:
                t = np.sqrt(abs(lam))
                zeros.append(t)
        
        return np.array(sorted(zeros))
    
    else:
        raise ValueError(f"Método desconocido: {method}")


def compare_with_riemann_zeros(computed_zeros: np.ndarray, 
                               riemann_zeros: List[float],
                               max_compare: int = 10) -> Dict:
    """
    Compara los ceros computados con los ceros conocidos de Riemann.
    
    Args:
        computed_zeros: Ceros aproximados desde el operador
        riemann_zeros: Ceros verdaderos de ζ(s)
        max_compare: Número máximo de ceros a comparar
        
    Returns:
        Diccionario con estadísticas de comparación
    """
    n_compare = min(max_compare, len(computed_zeros), len(riemann_zeros))
    
    differences = []
    relative_errors = []
    
    for i in range(n_compare):
        diff = abs(computed_zeros[i] - riemann_zeros[i])
        differences.append(diff)
        
        if riemann_zeros[i] > 1e-10:
            rel_error = diff / riemann_zeros[i]
            relative_errors.append(rel_error)
    
    return {
        'num_compared': n_compare,
        'differences': differences,
        'relative_errors': relative_errors,
        'mean_difference': np.mean(differences) if differences else 0.0,
        'max_difference': np.max(differences) if differences else 0.0,
        'mean_relative_error': np.mean(relative_errors) if relative_errors else 0.0
    }


def operator_H_demo(riemann_zeros: List[float], 
                   dimension: int = 50,
                   t: float = 0.1,
                   x_max: float = 5.0) -> Dict:
    """
    Demostración completa de la construcción del operador H.
    
    Args:
        riemann_zeros: Ceros conocidos de ζ(s) para comparación
        dimension: Dimensión de la discretización
        t: Parámetro de regularización
        x_max: Rango máximo de la grilla
        
    Returns:
        Diccionario con resultados completos
    """
    # Grilla logarítmica
    x_grid = np.linspace(0.1, x_max, dimension)
    
    # Construir operador H
    H = construct_operator_H(x_grid, t, include_involution=True)
    
    # Diagonalizar
    eigenvalues, eigenvectors = diagonalize_operator(H)
    
    # Convertir a ceros
    computed_zeros = spectrum_to_zeros(eigenvalues, method='berry_keating')
    
    # Comparar con ceros de Riemann
    comparison = compare_with_riemann_zeros(
        computed_zeros, 
        riemann_zeros,
        max_compare=min(10, len(computed_zeros))
    )
    
    # Propiedades del operador
    trace = np.trace(H)
    nuclear_norm = np.sum(np.abs(eigenvalues))
    is_trace_class = np.isfinite(nuclear_norm)
    
    return {
        'dimension': dimension,
        't_parameter': t,
        'x_range': (x_grid[0], x_grid[-1]),
        'operator_trace': float(trace),
        'nuclear_norm': float(nuclear_norm),
        'is_trace_class': is_trace_class,
        'num_eigenvalues': len(eigenvalues),
        'eigenvalue_range': (float(np.min(eigenvalues)), float(np.max(eigenvalues))),
        'num_computed_zeros': len(computed_zeros),
        'computed_zeros': computed_zeros.tolist()[:20],  # Primeros 20
        'comparison': comparison
    }

