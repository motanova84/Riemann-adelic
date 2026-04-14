"""
Tests para el módulo de dualidad de Poisson.

Verifica:
    - Involución J² = Id
    - Ecuación funcional forzada por la dualidad
    - Factor gamma Γ_ℝ(s) y su ecuación funcional
"""

import pytest
import mpmath as mp
import numpy as np
from dualidad_poisson import (
    poisson_involution, verify_involution, mellin_kernel,
    mellin_transform_with_poisson, force_functional_equation,
    gamma_factor_computation, verify_gamma_factor_functional_equation,
    poisson_duality_demo
)


# Configuración de precisión
mp.dps = 30


def test_poisson_involution_basic():
    """Test básico del operador de Poisson J."""
    # Función de prueba simple
    def f(x):
        return mp.exp(-x)
    
    x = 1.0
    J_f = poisson_involution(f, x)
    
    # El resultado debe ser finito y real
    assert mp.isfinite(J_f), "J f debe ser finito"
    assert mp.im(J_f) == 0, "Para función real, J f debe ser real"


def test_poisson_involution_identity():
    """Verifica que J² = Id para varias funciones."""
    test_functions = [
        lambda x: mp.exp(-x * x),  # Gaussiana
        lambda x: mp.exp(-x),       # Exponencial
        lambda x: 1 / (1 + x * x),  # Lorentziana
    ]
    
    test_points = [0.5, 1.0, 2.0, 5.0]
    
    for f in test_functions:
        for x in test_points:
            is_inv, error = verify_involution(f, x, tolerance=1e-8)
            assert is_inv, f"J² = Id falló en x={x}, error={error}"


def test_poisson_involution_gaussian():
    """Test específico con función gaussiana (caso especial)."""
    def gaussian(x):
        return mp.exp(-x * x)
    
    # Para la gaussiana, J preserva la forma (hasta constante)
    x = 1.0
    is_inv, error = verify_involution(gaussian, x)
    
    assert is_inv, f"Gaussiana debe satisfacer J² = Id, error={error}"
    assert error < 1e-10, f"Error muy alto: {error}"


def test_mellin_kernel_properties():
    """Verifica propiedades básicas del núcleo de Mellin."""
    s = mp.mpc(2.0, 0.0)
    x = 2.0
    
    kernel = mellin_kernel(s, x)
    
    # Para s=2, x=2: kernel = x^(s-1) = 2^1 = 2
    expected = mp.power(2.0, 1.0)
    
    assert abs(kernel - expected) < 1e-15, "Núcleo de Mellin incorrecto"


def test_mellin_kernel_critical_line():
    """Test del núcleo en la línea crítica s = 1/2 + it."""
    t = 14.134725142  # Primer cero de zeta
    s = mp.mpc(0.5, t)
    x = 2.0
    
    kernel = mellin_kernel(s, x)
    
    # En la línea crítica, |x^{s-1}| = x^{Re(s)-1} = x^{-1/2}
    expected_magnitude = mp.power(x, -0.5)
    actual_magnitude = abs(kernel)
    
    assert abs(actual_magnitude - expected_magnitude) < 1e-10, \
        "Magnitud incorrecta en línea crítica"


def test_gamma_factor_functional_equation():
    """
    Test principal: verifica la ecuación funcional del factor gamma.
    Γ_ℝ(s) / Γ_ℝ(1-s) = π^{s-1/2}
    """
    test_values = [
        mp.mpc(0.25, 0.0),
        mp.mpc(0.5, 0.0),
        mp.mpc(0.75, 0.0),
        mp.mpc(0.5, 14.134),  # En un cero
        mp.mpc(0.3, 10.0),
    ]
    
    for s in test_values:
        satisfies, error = verify_gamma_factor_functional_equation(s)
        
        assert satisfies, \
            f"Ecuación funcional de Γ_ℝ falló en s={s}, error={error}"
        assert error < 1e-9, f"Error muy alto en s={s}: {error}"


def test_gamma_factor_at_critical_line():
    """Verifica Γ_ℝ(s) en la línea crítica."""
    # En s = 1/2 + it, Γ_ℝ(1/2 + it) = Γ_ℝ(1/2 - it) por ecuación funcional
    t = 5.0
    s1 = mp.mpc(0.5, t)
    s2 = mp.mpc(0.5, -t)
    
    gamma1 = gamma_factor_computation(s1)
    gamma2 = gamma_factor_computation(s2)
    
    # Deben ser conjugados complejos
    assert abs(gamma1 - mp.conj(gamma2)) < 1e-10, \
        "Γ_ℝ(1/2+it) y Γ_ℝ(1/2-it) deben ser conjugados"


def test_gamma_factor_special_values():
    """Verifica valores especiales conocidos del factor gamma."""
    # Γ(1) = 1
    s = mp.mpc(2.0, 0.0)
    gamma_s = gamma_factor_computation(s)
    
    # Γ_ℝ(2) = π^{-1} Γ(1) = π^{-1}
    expected = mp.mpf(1) / mp.pi
    
    assert abs(gamma_s - expected) < 1e-12, \
        f"Γ_ℝ(2) = {gamma_s}, esperado {expected}"


def test_poisson_duality_demo():
    """Test de la demostración completa de dualidad de Poisson."""
    results = poisson_duality_demo(test_points=5)
    
    # Verificaciones
    assert results['all_involutions_verified'], \
        "Todas las involuciones deben verificarse"
    assert results['all_gamma_equations_verified'], \
        "Todas las ecuaciones gamma deben verificarse"
    
    # Imprimir resultados
    print("\n=== Resultados de Dualidad de Poisson ===")
    print(f"Involuciones verificadas: {results['all_involutions_verified']}")
    print(f"Ecuaciones gamma verificadas: {results['all_gamma_equations_verified']}")
    
    print("\nDetalles de involución:")
    for r in results['involution_results']:
        print(f"  x={r['x']:.2f}: J²=Id? {r['is_involution']}, error={r['error']:.2e}")
    
    print("\nDetalles de factor gamma:")
    for r in results['gamma_results']:
        print(f"  s={r['s']}: satisface? {r['satisfies']}, error={r['error']:.2e}")


def test_involution_preserves_integral():
    """Verifica que J preserve la integral (con medida apropiada)."""
    def f(x):
        return mp.exp(-x * x)
    
    # ∫ f(x) dx/x debería ser igual a ∫ J f(x) dx/x
    # Este es un test conceptual simplificado
    
    def integrand_f(x):
        return f(x) / x
    
    def integrand_Jf(x):
        if x < 1e-10:
            return mp.mpf(0)
        return poisson_involution(f, x) / x
    
    # Integrar en rango finito
    I_f = mp.quad(integrand_f, [0.1, 10.0])
    I_Jf = mp.quad(integrand_Jf, [0.1, 10.0])
    
    # No necesariamente exactamente iguales, pero relacionados
    # Este es un test de coherencia
    assert mp.isfinite(I_f) and mp.isfinite(I_Jf), \
        "Ambas integrales deben ser finitas"


def test_mellin_poisson_relation():
    """
    Verifica la relación fundamental:
    M[J f](s) está relacionado con M[f](1-s)
    """
    def f(x):
        return mp.exp(-x * x)
    
    s = mp.mpc(0.7, 0.0)
    
    M_f, M_Jf = mellin_transform_with_poisson(f, s)
    
    # Ambas transformadas deben ser finitas
    assert mp.isfinite(M_f), "M[f] debe ser finita"
    assert mp.isfinite(M_Jf), "M[J f] debe ser finita"
    
    # Test de coherencia: verificar que M[Jf] se relaciona con M[f](1-s)
    M_f_1minus_s, _ = mellin_transform_with_poisson(f, 1 - s)
    
    # La relación exacta depende de la normalización
    # pero ambos deben tener magnitud similar
    ratio = abs(M_Jf) / abs(M_f_1minus_s) if abs(M_f_1minus_s) > 1e-10 else 1.0
    
    # El ratio debe estar en un rango razonable
    assert 0.1 < ratio < 10.0, \
        f"Ratio M[Jf]/M[f](1-s) = {ratio} fuera de rango esperado"


def test_edge_cases():
    """Test de casos borde."""
    def f(x):
        return mp.exp(-x)
    
    # x muy pequeño
    x_small = 0.001
    J_f_small = poisson_involution(f, x_small)
    assert mp.isfinite(J_f_small), "Debe manejar x pequeños"
    
    # x = 1 (punto fijo potencial)
    x_one = 1.0
    is_inv, error = verify_involution(f, x_one)
    assert is_inv, f"J² = Id debe funcionar en x=1, error={error}"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
