"""
Tests para el módulo del operador H.

Verifica:
    - Construcción del núcleo de calor K_t(x,y)
    - Operador de regularización R_t
    - Involución J
    - Construcción del operador H
    - Diagonalización y espectro
    - Aproximación a ceros de Riemann
"""

import pytest
import mpmath as mp
import numpy as np
from operador_H import (
    heat_kernel, construct_kernel_matrix, regularization_operator_R_t,
    involution_operator_J, construct_operator_H, diagonalize_operator,
    spectrum_to_zeros, compare_with_riemann_zeros, operator_H_demo
)


# Configuración
mp.dps = 30


# Primeros ceros de ζ(s) (partes imaginarias)
RIEMANN_ZEROS = [
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478
]


def test_heat_kernel_symmetry():
    """Verifica que el núcleo de calor sea simétrico."""
    x, y, t = 1.0, 2.0, 0.5
    
    k_xy = heat_kernel(x, y, t)
    k_yx = heat_kernel(y, x, t)
    
    assert abs(k_xy - k_yx) < 1e-15, "Núcleo de calor debe ser simétrico"


def test_heat_kernel_normalization():
    """Verifica normalización del núcleo de calor."""
    t = 1.0
    x = 0.0
    
    k_00 = heat_kernel(x, x, t)
    
    # En x=x, el núcleo es (4πt)^{-1/2}
    expected = float(mp.mpf(1) / mp.sqrt(4 * mp.pi * t))
    
    assert abs(k_00 - expected) < 1e-12, f"Normalización incorrecta: {k_00} vs {expected}"


def test_heat_kernel_positive():
    """Verifica que el núcleo de calor sea siempre positivo."""
    t = 0.5
    test_points = [(0.0, 0.0), (1.0, 1.5), (2.0, 3.0), (0.5, 2.5)]
    
    for x, y in test_points:
        k = heat_kernel(x, y, t)
        assert k > 0, f"Núcleo debe ser positivo: K({x},{y})={k}"


def test_heat_kernel_decreases_with_distance():
    """Verifica que el núcleo decrezca con la distancia."""
    x, t = 1.0, 0.5
    
    k_1 = heat_kernel(x, x, t)
    k_2 = heat_kernel(x, x + 0.5, t)
    k_3 = heat_kernel(x, x + 1.0, t)
    
    assert k_1 > k_2 > k_3, "Núcleo debe decrecer con distancia"


def test_construct_kernel_matrix_shape():
    """Test de forma de la matriz del núcleo."""
    x_grid = np.linspace(0.1, 5.0, 20)
    t = 0.5
    
    K = construct_kernel_matrix(x_grid, t)
    
    assert K.shape == (20, 20), "Matriz debe ser cuadrada"
    assert np.all(np.isfinite(K)), "Todos los elementos deben ser finitos"


def test_construct_kernel_matrix_symmetric():
    """Verifica que la matriz del núcleo sea simétrica."""
    x_grid = np.linspace(0.1, 5.0, 10)
    t = 0.5
    
    K = construct_kernel_matrix(x_grid, t)
    
    assert np.allclose(K, K.T), "Matriz del núcleo debe ser simétrica"


def test_construct_kernel_matrix_positive_definite():
    """Verifica que la matriz del núcleo sea definida positiva."""
    x_grid = np.linspace(0.1, 5.0, 10)
    t = 0.5
    
    K = construct_kernel_matrix(x_grid, t)
    
    # Verificar valores propios positivos
    eigenvalues = np.linalg.eigvalsh(K)
    
    assert np.all(eigenvalues > -1e-10), "Matriz debe ser semidefinida positiva"


def test_regularization_operator_R_t():
    """Test del operador de regularización."""
    x_grid = np.linspace(0.1, 5.0, 15)
    t = 0.5
    
    R_t = regularization_operator_R_t(x_grid, t)
    
    assert R_t.shape == (15, 15)
    assert np.all(np.isfinite(R_t))
    assert np.allclose(R_t, R_t.T), "R_t debe ser simétrico"


def test_involution_operator_J_shape():
    """Test de forma del operador de involución."""
    x_grid = np.linspace(0.1, 5.0, 20)
    
    J = involution_operator_J(x_grid)
    
    assert J.shape == (20, 20), "J debe ser cuadrada"
    assert np.all(np.isfinite(J))


def test_involution_operator_J_approximately_involution():
    """
    Verifica aproximadamente que J² ≈ I.
    
    Nota: En discretización, esta propiedad es aproximada.
    """
    x_grid = np.linspace(0.5, 2.0, 20)  # Rango simétrico alrededor de 1
    
    J = involution_operator_J(x_grid)
    J2 = J @ J
    I = np.eye(20)
    
    # Verificar que J² esté razonablemente cerca de I
    frobenius_error = np.linalg.norm(J2 - I, 'fro') / np.linalg.norm(I, 'fro')
    
    print(f"\nError Frobenius de J²-I: {frobenius_error:.4f}")
    
    # Error debe ser menor que 50% (la discretización no es perfecta)
    assert frobenius_error < 0.5, f"J² muy diferente de I: error={frobenius_error}"


def test_construct_operator_H_hermitian():
    """Verifica que el operador H sea hermítico."""
    x_grid = np.linspace(0.1, 5.0, 20)
    t = 0.5
    
    H = construct_operator_H(x_grid, t, include_involution=True)
    
    assert np.allclose(H, H.T), "H debe ser hermítico"


def test_construct_operator_H_without_involution():
    """Test de H sin involución."""
    x_grid = np.linspace(0.1, 5.0, 20)
    t = 0.5
    
    H_without = construct_operator_H(x_grid, t, include_involution=False)
    
    assert H_without.shape == (20, 20)
    assert np.allclose(H_without, H_without.T)


def test_diagonalize_operator():
    """Test de diagonalización del operador."""
    x_grid = np.linspace(0.1, 5.0, 20)
    t = 0.5
    
    H = construct_operator_H(x_grid, t)
    eigenvalues, eigenvectors = diagonalize_operator(H)
    
    assert len(eigenvalues) == 20
    assert eigenvectors.shape == (20, 20)
    
    # Todos los valores propios deben ser reales (H es hermítico)
    assert np.all(np.isreal(eigenvalues))


def test_spectrum_to_zeros_berry_keating():
    """Test de conversión de espectro a ceros (método Berry-Keating)."""
    # Eigenvalues artificiales
    eigenvalues = np.array([0.3, 0.5, 1.0, 2.0, 5.0])
    
    zeros = spectrum_to_zeros(eigenvalues, method='berry_keating')
    
    # Debe filtrar eigenvalues < 0.25 y calcular t = sqrt(λ - 0.25)
    assert len(zeros) == 5  # Todos > 0.25
    assert np.all(zeros >= 0), "Ceros deben ser no negativos"
    assert np.all(np.diff(zeros) >= 0), "Ceros deben estar ordenados"


def test_spectrum_to_zeros_connes():
    """Test de conversión con método Connes."""
    eigenvalues = np.array([0.5, 1.0, 2.0, 5.0])
    
    zeros = spectrum_to_zeros(eigenvalues, method='connes')
    
    assert len(zeros) == 4
    assert np.all(zeros >= 0)


def test_compare_with_riemann_zeros():
    """Test de comparación con ceros de Riemann."""
    computed_zeros = np.array([14.0, 21.5, 25.2, 30.1, 33.0])
    
    comparison = compare_with_riemann_zeros(
        computed_zeros,
        RIEMANN_ZEROS,
        max_compare=5
    )
    
    assert comparison['num_compared'] == 5
    assert len(comparison['differences']) == 5
    assert comparison['mean_difference'] >= 0
    
    print(f"\nComparación con ceros de Riemann:")
    print(f"  Diferencia media: {comparison['mean_difference']:.4f}")
    print(f"  Error relativo medio: {comparison['mean_relative_error']:.4%}")


def test_operator_H_demo_basic():
    """
    Test principal: demostración completa del operador H.
    """
    results = operator_H_demo(
        riemann_zeros=RIEMANN_ZEROS,
        dimension=30,
        t=0.2,
        x_max=4.0
    )
    
    # Verificaciones básicas
    assert results['dimension'] == 30
    assert results['is_trace_class'], "Operador debe ser de clase traza"
    assert results['num_eigenvalues'] == 30
    assert results['num_computed_zeros'] > 0
    
    # Verificar que se aproximan algunos ceros
    comparison = results['comparison']
    assert comparison['num_compared'] > 0
    
    print(f"\n=== Demostración del Operador H ===")
    print(f"Dimensión: {results['dimension']}")
    print(f"Parámetro t: {results['t_parameter']}")
    print(f"Traza: {results['operator_trace']:.6f}")
    print(f"Norma nuclear: {results['nuclear_norm']:.6f}")
    print(f"Ceros computados: {results['num_computed_zeros']}")
    print(f"\nComparación con ceros de Riemann:")
    print(f"  Ceros comparados: {comparison['num_compared']}")
    print(f"  Diferencia media: {comparison['mean_difference']:.4f}")
    print(f"  Error relativo medio: {comparison['mean_relative_error']:.4%}")
    
    # El error relativo debe ser razonable (< 50% para aproximación burda)
    assert comparison['mean_relative_error'] < 0.5, \
        f"Error relativo demasiado alto: {comparison['mean_relative_error']:.2%}"


def test_operator_H_trace_class():
    """Verifica que H sea de clase traza."""
    x_grid = np.linspace(0.1, 5.0, 25)
    t = 0.3
    
    H = construct_operator_H(x_grid, t)
    eigenvalues, _ = diagonalize_operator(H)
    
    nuclear_norm = np.sum(np.abs(eigenvalues))
    
    assert np.isfinite(nuclear_norm), "Norma nuclear debe ser finita"
    print(f"\nNorma nuclear: {nuclear_norm:.6f}")


def test_operator_H_different_parameters():
    """Test con diferentes parámetros."""
    x_grid = np.linspace(0.1, 5.0, 20)
    
    # Diferentes valores de t
    t_values = [0.1, 0.5, 1.0]
    traces = []
    
    for t in t_values:
        H = construct_operator_H(x_grid, t)
        trace = np.trace(H)
        traces.append(trace)
    
    print(f"\nTrazas para diferentes t: {traces}")
    
    # La traza debería variar con t
    assert not np.allclose(traces[0], traces[-1]), "Trazas deben variar con t"


def test_numerical_stability():
    """Test de estabilidad numérica."""
    x_grid = np.linspace(0.1, 5.0, 30)
    t = 0.5
    
    H = construct_operator_H(x_grid, t)
    
    # Verificar que no hay NaN o Inf
    assert np.all(np.isfinite(H)), "Operador debe ser numéricamente estable"
    
    # Diagonalizar y verificar
    eigenvalues, _ = diagonalize_operator(H)
    assert np.all(np.isfinite(eigenvalues)), "Eigenvalues deben ser finitos"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
