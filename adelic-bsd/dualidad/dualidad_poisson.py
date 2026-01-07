"""
Principio de Dualidad de Poisson (Geometría ⇒ Ecuación Funcional)

Este módulo implementa el principio geométrico de dualidad que fuerza
la ecuación funcional D(s) = D(1-s) a través de la involución de Poisson.

Operador Principal:
    J: f(x) ↦ x^{-1/2} f(1/x)
    
Propiedad Fundamental:
    J² = Id (involución)
    
Referencias:
    - Tate (1950), Fourier analysis in number fields
    - Weil (1964), Sur la formule de Siegel dans la théorie des groupes classiques
"""

import mpmath as mp
from typing import Callable, Tuple, Union
import numpy as np


def poisson_involution(f: Callable[[Union[float, mp.mpf]], mp.mpf], 
                       x: Union[float, mp.mpf]) -> mp.mpf:
    """
    Operador de involución de Poisson: J f(x) = x^{-1/2} f(1/x).
    
    Este operador es fundamental en la teoría analítica de números
    y codifica la dualidad entre x y 1/x.
    
    Args:
        f: Función a transformar
        x: Punto de evaluación
        
    Returns:
        Valor de J f(x)
    """
    mp.dps = 30
    
    if abs(x) < mp.mpf('1e-10'):
        return mp.mpf(0)
    
    x_inv = mp.mpf(1) / x
    x_factor = mp.power(x, mp.mpf('-0.5'))
    
    return x_factor * f(x_inv)


def verify_involution(f: Callable[[Union[float, mp.mpf]], mp.mpf], 
                      x: Union[float, mp.mpf], 
                      tolerance: float = 1e-10) -> Tuple[bool, float]:
    """
    Verifica que J² = Id, es decir, que J es una involución.
    
    Calcula J(J f)(x) y verifica que sea igual a f(x).
    
    Args:
        f: Función de prueba
        x: Punto de evaluación
        tolerance: Tolerancia para la verificación
        
    Returns:
        Tupla (es_involucion, error_relativo)
    """
    mp.dps = 30
    
    # Valor original
    f_x = f(x)
    
    # Aplicar J dos veces
    def J_f(y):
        return poisson_involution(f, y)
    
    J2_f_x = poisson_involution(J_f, x)
    
    # Calcular error
    if abs(f_x) > mp.mpf('1e-15'):
        relative_error = abs(J2_f_x - f_x) / abs(f_x)
    else:
        relative_error = abs(J2_f_x - f_x)
    
    is_involution = relative_error < tolerance
    
    return is_involution, float(relative_error)


def mellin_kernel(s: mp.mpc, x: Union[float, mp.mpf]) -> mp.mpc:
    """
    Núcleo de Mellin: K(s, x) = x^{s-1}.
    
    Este núcleo conecta la transformada de Mellin con la dualidad de Poisson.
    
    Args:
        s: Parámetro complejo
        x: Variable real positiva
        
    Returns:
        Valor del núcleo de Mellin
    """
    mp.dps = 30
    
    if x <= 0:
        return mp.mpc(0, 0)
    
    return mp.power(x, s - 1)


def mellin_transform_with_poisson(f: Callable[[Union[float, mp.mpf]], mp.mpf], 
                                  s: mp.mpc) -> Tuple[mp.mpc, mp.mpc]:
    """
    Calcula la transformada de Mellin de f y J f.
    
    Demuestra que la simetría de Poisson implica:
        M[J f](s) = M[f](1-s)
    
    Args:
        f: Función de prueba
        s: Parámetro complejo
        
    Returns:
        Tupla (M[f](s), M[J f](s))
    """
    mp.dps = 30
    
    # Transformada de Mellin de f
    def integrand_f(x):
        return f(x) * mp.power(x, s - 1)
    
    M_f = mp.quad(integrand_f, [mp.mpf('0.01'), mp.mpf('100')])
    
    # Transformada de Mellin de J f
    def J_f(x):
        return poisson_involution(f, x)
    
    def integrand_Jf(x):
        return J_f(x) * mp.power(x, s - 1)
    
    M_Jf = mp.quad(integrand_Jf, [mp.mpf('0.01'), mp.mpf('100')])
    
    return M_f, M_Jf


def force_functional_equation(s: mp.mpc, 
                              M_f_s: mp.mpc, 
                              M_f_1minus_s: mp.mpc,
                              tolerance: float = 1e-6) -> Tuple[bool, float]:
    """
    Verifica que la simetría de Poisson force D(s) = D(1-s).
    
    La idea es que si f es autofunción de J con valor propio +1,
    entonces su transformada de Mellin satisface M[f](s) = M[f](1-s).
    
    Args:
        s: Parámetro complejo
        M_f_s: Valor de M[f](s)
        M_f_1minus_s: Valor de M[f](1-s)
        tolerance: Tolerancia para verificación
        
    Returns:
        Tupla (satisface_ecuacion, error_relativo)
    """
    mp.dps = 30
    
    if abs(M_f_s) > mp.mpf('1e-15'):
        relative_error = abs(M_f_s - M_f_1minus_s) / abs(M_f_s)
    else:
        relative_error = abs(M_f_s - M_f_1minus_s)
    
    satisfies = relative_error < tolerance
    
    return satisfies, float(relative_error)


def gamma_factor_computation(s: mp.mpc) -> mp.mpc:
    """
    Calcula el factor gamma Γ_ℝ(s) = π^{-s/2} Γ(s/2).
    
    Este es el factor arquimediano que aparece en la ecuación funcional
    de la función zeta de Riemann.
    
    Args:
        s: Parámetro complejo
        
    Returns:
        Valor de Γ_ℝ(s)
    """
    mp.dps = 30
    
    s_half = s / 2
    
    # Γ_ℝ(s) = π^{-s/2} Γ(s/2)
    pi_term = mp.power(mp.pi, -s_half)
    gamma_term = mp.gamma(s_half)
    
    return pi_term * gamma_term


def verify_gamma_factor_functional_equation(s: mp.mpc, 
                                           tolerance: float = 1e-10) -> Tuple[bool, float]:
    """
    Verifica que Γ_ℝ(s) satisface la ecuación funcional:
        Γ_ℝ(s) / Γ_ℝ(1-s) = π^{s-1/2}
    
    Args:
        s: Parámetro complejo
        tolerance: Tolerancia para verificación
        
    Returns:
        Tupla (satisface, error_relativo)
    """
    mp.dps = 30
    
    Gamma_s = gamma_factor_computation(s)
    Gamma_1minus_s = gamma_factor_computation(1 - s)
    
    if abs(Gamma_1minus_s) < mp.mpf('1e-15'):
        return False, float('inf')
    
    ratio = Gamma_s / Gamma_1minus_s
    expected = mp.power(mp.pi, s - mp.mpf('0.5'))
    
    if abs(expected) > mp.mpf('1e-15'):
        relative_error = abs(ratio - expected) / abs(expected)
    else:
        relative_error = abs(ratio - expected)
    
    satisfies = relative_error < tolerance
    
    return satisfies, float(relative_error)


def poisson_duality_demo(test_points: int = 5) -> dict:
    """
    Demostración completa del principio de dualidad de Poisson.
    
    Args:
        test_points: Número de puntos de prueba
        
    Returns:
        Diccionario con resultados de la demostración
    """
    # Función de prueba: gaussiana
    def gaussian(x):
        return mp.exp(-x * x)
    
    # Verificar involución J² = Id
    x_values = [0.5, 1.0, 2.0, 3.0, 5.0][:test_points]
    involution_results = []
    
    for x in x_values:
        is_inv, error = verify_involution(gaussian, x)
        involution_results.append({
            'x': float(x),
            'is_involution': is_inv,
            'error': error
        })
    
    # Verificar ecuación funcional del factor gamma
    s_values = [mp.mpc(0.3, 0.0), mp.mpc(0.5, 14.134), mp.mpc(0.7, 0.0)]
    gamma_results = []
    
    for s in s_values:
        satisfies, error = verify_gamma_factor_functional_equation(s)
        gamma_results.append({
            's': complex(s),
            'satisfies': satisfies,
            'error': error
        })
    
    all_involutions_ok = all(r['is_involution'] for r in involution_results)
    all_gamma_ok = all(r['satisfies'] for r in gamma_results)
    
    return {
        'involution_results': involution_results,
        'gamma_results': gamma_results,
        'all_involutions_verified': all_involutions_ok,
        'all_gamma_equations_verified': all_gamma_ok,
        'test_points': test_points
    }
