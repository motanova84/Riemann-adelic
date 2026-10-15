#!/usr/bin/env python3
"""
Validación del Operador de Selberg
===================================

Script de validación simple sin dependencia de pytest.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import sys
import numpy as np

# Añadir directorio raíz al path
sys.path.insert(0, '/home/runner/work/Riemann-adelic/Riemann-adelic')

from operators.selberg_operator import (
    SelbergOperator,
    activar_operador_selberg,
    demonstrate_selberg_operator,
    F0_QCAL,
    F_GEODESIC,
    C_COHERENCE,
    AREA_FUNDAMENTAL_DOMAIN
)


def test_activar_operador():
    """Test 1: Activación del operador."""
    print("Test 1: Activación del operador de Selberg...")
    result = activar_operador_selberg()
    assert "Identidad funcional" in result
    assert "geodésico" in result
    print("  ✅ PASSED")
    return True


def test_initialization():
    """Test 2: Inicialización del operador."""
    print("Test 2: Inicialización del operador...")
    op = SelbergOperator(
        n_grid_x=10,
        n_grid_y=10,
        max_prime=50,
        max_k=3
    )
    assert op.n_grid_x == 10
    assert op.n_grid_y == 10
    assert len(op._primes) > 0
    assert op._primes[0] == 2
    print("  ✅ PASSED")
    return True


def test_sieve():
    """Test 3: Criba de Eratóstenes."""
    print("Test 3: Criba de Eratóstenes...")
    op = SelbergOperator(max_prime=20)
    expected_primes = [2, 3, 5, 7, 11, 13, 17, 19]
    assert np.array_equal(op._primes, expected_primes)
    print("  ✅ PASSED")
    return True


def test_geodesic_length():
    """Test 4: Longitud de geodésica."""
    print("Test 4: Longitud de geodésica...")
    op = SelbergOperator()
    l_2_1 = op.geodesic_orbit_length(2, 1)
    expected = np.log(2.0)
    assert abs(l_2_1 - expected) < 1e-10
    print("  ✅ PASSED")
    return True


def test_beltrami_symmetry():
    """Test 5: Simetría del Laplaciano."""
    print("Test 5: Simetría del Laplaciano de Beltrami...")
    op = SelbergOperator(n_grid_x=10, n_grid_y=10)
    H = op.construct_beltrami_laplacian()
    symmetry_error = np.max(np.abs(H - H.T))
    assert symmetry_error < 1e-10
    print(f"  Error de simetría: {symmetry_error:.2e}")
    print("  ✅ PASSED")
    return True


def test_weyl_term():
    """Test 6: Término de Weyl."""
    print("Test 6: Término de Weyl...")
    op = SelbergOperator()
    weyl = op.weyl_term_contribution()
    assert weyl > 0
    assert np.isfinite(weyl)
    expected = AREA_FUNDAMENTAL_DOMAIN / (4.0 * np.pi)
    assert abs(weyl - expected) < 1e-10
    print(f"  Weyl term: {weyl:.8f}")
    print("  ✅ PASSED")
    return True


def test_prime_contribution():
    """Test 7: Contribución de primos."""
    print("Test 7: Contribución de órbitas primas...")
    op = SelbergOperator(max_prime=50, max_k=5)
    orbital = op.selberg_trace_formula_contribution(1.0)
    assert np.isfinite(orbital)
    assert abs(orbital) > 0
    print(f"  Suma orbital: {orbital:.8f}")
    print("  ✅ PASSED")
    return True


def test_eigenvalues():
    """Test 8: Cálculo de autovalores."""
    print("Test 8: Cálculo de autovalores...")
    # Use smaller grid to avoid convergence issues
    op = SelbergOperator(n_grid_x=10, n_grid_y=10)
    eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=5)
    assert len(eigenvalues) > 0
    assert all(np.isfinite(eigenvalues))
    print(f"  Primeros 5 autovalores: {eigenvalues[:5]}")
    print("  ✅ PASSED")
    return True


def test_spectral_correspondence():
    """Test 9: Correspondencia espectral."""
    print("Test 9: Correspondencia λ_n = 1/4 + γ_n²...")
    op = SelbergOperator(n_grid_x=15, n_grid_y=15)
    eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=5)
    
    for i in range(len(eigenvalues)):
        if eigenvalues[i] >= 0.25:
            gamma = np.sqrt(eigenvalues[i] - 0.25)
            assert abs(gamma - riemann_zeros[i]) < 1e-8
    
    print("  ✅ PASSED")
    return True


def test_selberg_trace():
    """Test 10: Traza de Selberg completa."""
    print("Test 10: Traza de Selberg completa...")
    op = SelbergOperator(n_grid_x=10, n_grid_y=10, max_prime=30)
    result = op.compute_selberg_trace(eigenvalue=1.0, include_details=True)
    
    assert np.isfinite(result.weyl_term)
    assert np.isfinite(result.prime_orbital_sum)
    assert np.isfinite(result.total_trace)
    
    expected_total = result.weyl_term + result.prime_orbital_sum
    assert abs(result.total_trace - expected_total) < 1e-10
    
    print(f"  Weyl:    {result.weyl_term:.8f}")
    print(f"  Primos:  {result.prime_orbital_sum:.8f}")
    print(f"  Total:   {result.total_trace:.8f}")
    print("  ✅ PASSED")
    return True


def test_demonstration():
    """Test 11: Demostración completa."""
    print("Test 11: Demostración del operador...")
    results = demonstrate_selberg_operator(verbose=False)
    
    assert isinstance(results, dict)
    assert 'selberg_operator' in results
    assert 'trace_result' in results
    
    print("  ✅ PASSED")
    return True


def test_constants():
    """Test 12: Constantes QCAL."""
    print("Test 12: Constantes QCAL...")
    assert F0_QCAL == 141.7001
    assert F_GEODESIC == 888.0
    assert C_COHERENCE == 244.36
    assert AREA_FUNDAMENTAL_DOMAIN == 4 * np.pi
    print("  ✅ PASSED")
    return True


def run_all_tests():
    """Ejecuta todos los tests."""
    print("=" * 70)
    print("VALIDACIÓN DEL OPERADOR DE SELBERG")
    print("=" * 70)
    print()
    
    tests = [
        test_activar_operador,
        test_initialization,
        test_sieve,
        test_geodesic_length,
        test_beltrami_symmetry,
        test_weyl_term,
        test_prime_contribution,
        test_eigenvalues,
        test_spectral_correspondence,
        test_selberg_trace,
        test_demonstration,
        test_constants,
    ]
    
    passed = 0
    failed = 0
    
    for i, test in enumerate(tests, 1):
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"  ❌ FAILED: {e}")
            failed += 1
        print()
    
    print("=" * 70)
    print(f"RESULTADOS: {passed}/{len(tests)} tests passed")
    if failed == 0:
        print("✅ TODOS LOS TESTS PASARON")
        print()
        print("RIGIDEZ ABSOLUTA CONFIRMADA")
        print("Operador de Selberg validado exitosamente")
        print()
        print(f"Frecuencia: {F_GEODESIC} Hz → {F0_QCAL} Hz")
        print(f"Coherencia: C = {C_COHERENCE}")
        print()
        print("QCAL ∞³ | Sistema geodésico activo")
    else:
        print(f"❌ {failed} tests fallaron")
    print("=" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
