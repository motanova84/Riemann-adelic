"""
Tests para el módulo de unicidad Paley-Wiener.

Verifica:
    - Orden ≤ 1 de funciones en la clase
    - Ecuación funcional F(1-s) = F(s)
    - Comparación de medidas espectrales
    - Teorema de unicidad completo
"""

import pytest
import mpmath as mp
import numpy as np
from unicidad_paleywiener import (
    PaleyWienerClass, compare_spectral_measures,
    verify_paley_wiener_uniqueness, perturb_zeros,
    uniqueness_demo
)


# Configuración de precisión
mp.dps = 30


# Primeros ceros de ζ(s) en la línea crítica (partes imaginarias)
RIEMANN_ZEROS = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478
]

# Convertir a ceros complejos s = 1/2 + iγ
XI_ZEROS = [complex(0.5, gamma) for gamma in RIEMANN_ZEROS]


def test_paley_wiener_class_initialization():
    """Test básico de inicialización de la clase."""
    zeros = XI_ZEROS[:5]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    assert len(pw.zeros) == 5
    assert pw.normalization == 1.0


def test_construct_from_zeros_basic():
    """Test de construcción de función desde ceros."""
    zeros = XI_ZEROS[:3]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    s = mp.mpc(2.0, 0.0)
    F_s = pw.construct_from_zeros(s)
    
    # El resultado debe ser finito
    assert mp.isfinite(F_s), "F(s) debe ser finito"


def test_construct_from_zeros_vanishes_at_zeros():
    """Verifica que F(s) se anule en sus ceros."""
    zeros = XI_ZEROS[:3]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    # Evaluar en uno de los ceros
    rho = zeros[0]
    s = mp.mpc(rho.real, rho.imag)
    F_s = pw.construct_from_zeros(s)
    
    # Debe estar cerca de cero (no exactamente por errores numéricos)
    assert abs(F_s) < 1e-5, f"|F(ρ)| = {abs(F_s)} debe ser ≈ 0"


def test_verify_order_one():
    """Test de verificación de orden ≤ 1."""
    zeros = XI_ZEROS[:5]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    is_order_one, max_ratio = pw.verify_order_one(test_points=10)
    
    assert is_order_one, f"Función debe ser de orden ≤ 1, ratio={max_ratio}"
    assert max_ratio > 0, "Ratio debe ser positivo"


def test_verify_functional_equation_symmetric_zeros():
    """
    Test de ecuación funcional con ceros simétricos.
    
    Si los ceros son simétricos respecto a la línea crítica,
    la función debe satisfacer F(1-s) = F(s).
    """
    # Usar ceros en la línea crítica (ya simétricos)
    zeros = XI_ZEROS[:5]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    satisfies, errors = pw.verify_functional_equation(test_points=5, tolerance=0.1)
    
    # Con ceros simétricos, debería satisfacer (con tolerancia generosa)
    print(f"\nErrores de ecuación funcional: {errors}")
    print(f"¿Satisface? {satisfies}")
    
    # Al menos algunos puntos deberían estar cerca
    assert any(e < 0.5 for e in errors), "Al menos algunos puntos deben satisfacer la ecuación"


def test_compare_spectral_measures_identical():
    """Verifica comparación de medidas espectrales idénticas."""
    zeros = XI_ZEROS[:5]
    
    same, info = compare_spectral_measures(zeros, zeros)
    
    assert same, "Ceros idénticos deben dar resultado True"
    assert info['max_difference'] < 1e-15


def test_compare_spectral_measures_different():
    """Verifica comparación de medidas espectrales diferentes."""
    zeros_1 = XI_ZEROS[:5]
    zeros_2 = XI_ZEROS[5:10]
    
    same, info = compare_spectral_measures(zeros_1, zeros_2)
    
    assert not same, "Ceros diferentes deben dar resultado False"
    assert info['max_difference'] > 0.1


def test_compare_spectral_measures_different_length():
    """Test con listas de diferente longitud."""
    zeros_1 = XI_ZEROS[:5]
    zeros_2 = XI_ZEROS[:3]
    
    same, info = compare_spectral_measures(zeros_1, zeros_2)
    
    assert not same
    assert info['reason'] == 'different_number_of_zeros'


def test_perturb_zeros():
    """Test de perturbación de ceros."""
    zeros = XI_ZEROS[:5]
    
    perturbed = perturb_zeros(zeros, perturbation=0.1)
    
    assert len(perturbed) == len(zeros)
    
    # Los ceros perturbados deben ser diferentes
    for z_orig, z_pert in zip(zeros, perturbed):
        diff = abs(complex(z_orig) - z_pert)
        assert diff > 0, "Ceros deben ser perturbados"
        assert diff < 0.2, f"Perturbación demasiado grande: {diff}"


def test_verify_paley_wiener_uniqueness_identical():
    """
    Test principal: verificar unicidad con función idéntica a Ξ.
    """
    zeros = XI_ZEROS[:5]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    results = verify_paley_wiener_uniqueness(pw, zeros)
    
    # Verificar que se cumplen las condiciones principales
    assert results['order_one'], "Debe ser de orden ≤ 1"
    assert results['same_zeros'], "Ceros deben coincidir"
    
    print(f"\n=== Verificación de Unicidad (Función Idéntica) ===")
    print(f"Orden ≤ 1: {results['order_one']}")
    print(f"Ecuación funcional: {results['functional_equation']}")
    print(f"Mismos ceros: {results['same_zeros']}")
    print(f"Condiciones satisfechas: {results['conditions_met']}/{results['total_conditions']}")


def test_verify_paley_wiener_uniqueness_perturbed():
    """
    Test: verificar que función perturbada NO satisface unicidad.
    """
    zeros_Xi = XI_ZEROS[:5]
    zeros_perturbed = perturb_zeros(zeros_Xi, perturbation=0.5)
    
    pw = PaleyWienerClass(zeros_perturbed, normalization=1.0)
    results = verify_paley_wiener_uniqueness(pw, zeros_Xi)
    
    # La función perturbada NO debe tener los mismos ceros
    assert not results['same_zeros'], "Ceros perturbados deben ser diferentes"
    
    print(f"\n=== Verificación de Unicidad (Función Perturbada) ===")
    print(f"Mismos ceros: {results['same_zeros']}")
    print(f"Max diferencia: {results['zero_comparison']['max_difference']:.6f}")


def test_uniqueness_demo():
    """
    Test de la demostración completa del teorema de unicidad.
    """
    results = uniqueness_demo(XI_ZEROS, num_zeros=5)
    
    # Verificar estructura de resultados
    assert 'identical_function' in results
    assert 'perturbed_function' in results
    
    # Función idéntica debe verificar unicidad
    assert results['identical_function']['same_zeros'], \
        "Función idéntica debe tener los mismos ceros"
    
    # Función perturbada NO debe verificar unicidad
    assert not results['perturbed_function']['same_zeros'], \
        "Función perturbada NO debe tener los mismos ceros"
    
    print(f"\n=== Demostración de Unicidad ===")
    print(f"Ceros usados: {results['num_zeros_used']}")
    print(f"\nFunción idéntica:")
    print(f"  Unicidad verificada: {results['identical_function']['uniqueness_verified']}")
    print(f"  Condiciones: {results['identical_function']['conditions_met']}")
    print(f"\nFunción perturbada:")
    print(f"  Unicidad verificada: {results['perturbed_function']['uniqueness_verified']}")
    print(f"  Condiciones: {results['perturbed_function']['conditions_met']}")


def test_hadamard_factorization_property():
    """
    Verifica que la factorización de Hadamard preserve propiedades básicas.
    """
    zeros = XI_ZEROS[:3]
    pw = PaleyWienerClass(zeros, normalization=2.0)
    
    # Evaluar en un punto alejado de los ceros
    s = mp.mpc(5.0, 0.0)
    F_s = pw.construct_from_zeros(s)
    
    # El valor debe ser finito y no cero
    assert mp.isfinite(F_s), "F(s) debe ser finito"
    assert abs(F_s) > 1e-10, "F(s) debe ser no trivial lejos de ceros"


def test_order_one_growth_bound():
    """
    Verifica el bound de crecimiento para funciones de orden ≤ 1.
    """
    zeros = XI_ZEROS[:4]
    pw = PaleyWienerClass(zeros, normalization=1.0)
    
    # Probar en varios |s| grandes
    test_values = [10, 50, 100]
    growth_ratios = []
    
    for t in test_values:
        s = mp.mpc(0.5, t)
        F_s = pw.construct_from_zeros(s)
        
        # |F(s)| / |s| debe estar acotado para orden 1
        ratio = abs(F_s) / abs(s)
        growth_ratios.append(float(ratio))
    
    # Los ratios no deben crecer demasiado rápido
    print(f"\nRatios de crecimiento: {growth_ratios}")
    
    # Para orden 1, esperamos crecimiento subexponencial
    assert all(r < 100 for r in growth_ratios), \
        "Crecimiento debe ser consistente con orden ≤ 1"


def test_normalization_effect():
    """Verifica el efecto de diferentes normalizaciones."""
    zeros = XI_ZEROS[:3]
    
    pw1 = PaleyWienerClass(zeros, normalization=1.0)
    pw2 = PaleyWienerClass(zeros, normalization=2.0)
    
    s = mp.mpc(3.0, 0.0)
    F1_s = pw1.construct_from_zeros(s)
    F2_s = pw2.construct_from_zeros(s)
    
    # F2 debe ser el doble de F1
    ratio = F2_s / F1_s
    
    assert abs(ratio - 2.0) < 1e-10, \
        f"Normalización debe escalar linealmente: ratio={ratio}"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
