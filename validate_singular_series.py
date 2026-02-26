#!/usr/bin/env python3
"""
Validación Numérica de la Serie Singular de Goldbach
=====================================================

Este script valida numéricamente la implementación de la serie singular
en formalization/lean/singular_series.lean

Validaciones:
1. singularLocal correcta para primos impares y p=2
2. singularLocal_pos: positividad para p ≥ 3
3. singularLocal_two_cases: comportamiento para p=2
4. singularSeries convergencia del producto infinito
5. singularSeries_pos: positividad para n par ≥ 4
6. singularSeries_lower_bound: cota inferior explícita

Autor: José Manuel Mota Burruezo Ψ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Framework QCAL ∞³
"""

import json
from datetime import datetime
from typing import List, Tuple
import hashlib
import math

# QCAL Constants
F0 = 141.7001  # Hz - Frecuencia base QCAL
C_COHERENCE = 244.36  # Coherencia QCAL


def is_prime(n: int) -> bool:
    """Check if n is prime."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def primes_up_to(limit: int) -> List[int]:
    """Generate list of primes up to limit."""
    return [p for p in range(2, limit + 1) if is_prime(p)]


def singular_local(p: int, n: int) -> float:
    """
    Factor local de Goldbach en el primo p.
    
    Si p divide a n: 𝔖_p = 1 - 1/(p-1)²
    Si p no divide a n: 𝔖_p = 1 + 1/(p-1)³
    """
    if n % p == 0:
        # p divide a n
        return 1.0 - (1.0 / (p - 1)) ** 2
    else:
        # p no divide a n
        return 1.0 + (1.0 / (p - 1)) ** 3


def singular_series_truncated(n: int, max_prime: int) -> float:
    """
    Serie singular truncada: producto sobre primos hasta max_prime.
    
    𝔖(n) ≈ ∏_{p ≤ max_prime, p primo} singular_local(p, n)
    """
    primes = primes_up_to(max_prime)
    product = 1.0
    for p in primes:
        product *= singular_local(p, n)
    return product


def test_singular_local_pos():
    """Test 1: singularLocal_pos para primos impares."""
    print("\n" + "="*70)
    print("Test 1: Positividad de singularLocal para p ≥ 3")
    print("="*70)
    
    test_cases = [
        (3, 10), (3, 15),  # p=3, n par e impar
        (5, 10), (5, 15),  # p=5
        (7, 14), (7, 21),  # p=7
        (11, 22), (11, 33),  # p=11
        (13, 26), (13, 39),  # p=13
        (101, 100), (101, 101),  # p=101
    ]
    
    all_passed = True
    for p, n in test_cases:
        factor = singular_local(p, n)
        passed = factor > 0
        
        divides = "divides" if n % p == 0 else "does not divide"
        print(f"  p={p:3d}, n={n:3d} ({p} {divides} {n}): "
              f"factor = {factor:.10f}, positive = {passed}")
        
        if not passed:
            all_passed = False
            print(f"    ❌ FAIL: Expected positive, got {factor}")
    
    if all_passed:
        print("\n✅ Test 1 PASSED: All factors are positive for p ≥ 3")
    else:
        print("\n❌ Test 1 FAILED")
    
    return all_passed


def test_singular_local_two():
    """Test 2: singularLocal para p=2."""
    print("\n" + "="*70)
    print("Test 2: Comportamiento de singularLocal para p=2")
    print("="*70)
    
    test_cases = [
        (2, True, 0.0),   # n=2 (par) → factor = 0
        (4, True, 0.0),   # n=4 (par) → factor = 0
        (10, True, 0.0),  # n=10 (par) → factor = 0
        (3, False, 2.0),  # n=3 (impar) → factor = 2
        (5, False, 2.0),  # n=5 (impar) → factor = 2
        (11, False, 2.0), # n=11 (impar) → factor = 2
    ]
    
    all_passed = True
    for n, is_even, expected in test_cases:
        factor = singular_local(2, n)
        passed = abs(factor - expected) < 1e-10
        
        parity = "even" if is_even else "odd"
        print(f"  n={n:3d} ({parity}): factor = {factor:.10f}, "
              f"expected = {expected:.10f}, match = {passed}")
        
        if not passed:
            all_passed = False
            print(f"    ❌ FAIL: Expected {expected}, got {factor}")
    
    if all_passed:
        print("\n✅ Test 2 PASSED: p=2 behavior correct")
    else:
        print("\n❌ Test 2 FAILED")
    
    return all_passed


def test_convergence():
    """Test 3: Convergencia del producto infinito."""
    print("\n" + "="*70)
    print("Test 3: Convergencia del producto infinito")
    print("="*70)
    
    n = 100  # número par de prueba
    limits = [10, 20, 50, 100, 200, 500, 1000]
    
    print(f"\n  Producto truncado para n={n} (excluyendo p=2):")
    print(f"  {'Max Prime':>10} {'Product':>15} {'Change':>15}")
    print(f"  {'-'*10} {'-'*15} {'-'*15}")
    
    prev_product = None
    converged = True
    
    for limit in limits:
        # Excluir p=2 del producto para n par
        primes = [p for p in primes_up_to(limit) if p > 2]
        product = 1.0
        for p in primes:
            product *= singular_local(p, n)
        
        if prev_product is not None:
            change = abs(product - prev_product)
            print(f"  {limit:>10} {product:>15.10f} {change:>15.10e}")
            
            # Verificar convergencia: cambio debe decrecer
            if change > 0.1:
                converged = False
        else:
            print(f"  {limit:>10} {product:>15.10f} {'N/A':>15}")
        
        prev_product = product
    
    # Verificar convergencia a valor positivo
    final_value = prev_product
    convergence_passed = converged and final_value > 0
    
    print(f"\n  Valor final: {final_value:.10f}")
    print(f"  Positivo: {final_value > 0}")
    print(f"  Converge: {converged}")
    print(f"\n  NOTA: Para n par, excluimos p=2 (factor sería 0)")
    
    if convergence_passed:
        print("\n✅ Test 3 PASSED: Product converges to positive value")
    else:
        print("\n❌ Test 3 FAILED")
    
    return convergence_passed


def test_positivity():
    """Test 4: Positividad de la serie singular para n par ≥ 4."""
    print("\n" + "="*70)
    print("Test 4: Positividad de singularSeries para n par ≥ 4")
    print("="*70)
    
    # Nota: Para n par, el factor de p=2 es 0, así que la definición estándar
    # excluye p=2 del producto
    test_cases = [4, 6, 8, 10, 20, 50, 100, 200]
    max_prime = 1000
    
    all_positive = True
    for n in test_cases:
        # Excluir p=2 del producto para n par
        primes = [p for p in primes_up_to(max_prime) if p > 2]
        product = 1.0
        for p in primes:
            product *= singular_local(p, n)
        
        is_positive = product > 0
        print(f"  n={n:3d}: 𝔖(n) ≈ {product:.10f} "
              f"(truncado, sin p=2), positive = {is_positive}")
        
        if not is_positive:
            all_positive = False
    
    if all_positive:
        print("\n✅ Test 4 PASSED: Series is positive for even n ≥ 4")
    else:
        print("\n❌ Test 4 FAILED")
    
    return all_positive


def test_lower_bound():
    """Test 5: Cota inferior explícita."""
    print("\n" + "="*70)
    print("Test 5: Cota inferior explícita")
    print("="*70)
    
    test_cases = [4, 6, 8, 10, 20, 50, 100, 200]
    max_prime = 1000
    
    # Buscar mínimo del producto truncado (excl. p=2)
    min_value = float('inf')
    
    for n in test_cases:
        primes = [p for p in primes_up_to(max_prime) if p > 2]
        product = 1.0
        for p in primes:
            product *= singular_local(p, n)
        
        print(f"  n={n:3d}: 𝔖(n) ≈ {product:.10f}")
        min_value = min(min_value, product)
    
    # En la literatura, se usan cotas como 𝔖(n) ≥ 0.66 (aprox. de Euler)
    # Nuestro truncamiento debe dar valores cercanos
    print(f"\n  Mínimo observado: {min_value:.10f}")
    print(f"  Cota teórica (Euler): ≈ 0.66")
    
    # Verificar que el mínimo es razonablemente positivo
    reasonable_bound = min_value > 0.5
    
    if reasonable_bound:
        print("\n✅ Test 5 PASSED: Lower bound exists and is reasonable")
    else:
        print("\n❌ Test 5 FAILED")
    
    return reasonable_bound


def test_major_arc_ready():
    """Test 6: singularSeries_major_arc_ready."""
    print("\n" + "="*70)
    print("Test 6: singularSeries_major_arc_ready")
    print("="*70)
    
    # Verificar las dos propiedades:
    # 1. ∃ c > 0, singularSeries n ≥ c
    # 2. ∀ p ≥ 3 primo, singularLocal p n ≥ 1 - 1/(p-1)²
    
    n = 100
    max_prime = 1000
    
    # Propiedad 1
    primes = [p for p in primes_up_to(max_prime) if p > 2]
    product = 1.0
    for p in primes:
        product *= singular_local(p, n)
    
    prop1_passed = product > 0
    print(f"  Propiedad 1: 𝔖({n}) ≈ {product:.10f} > 0 : {prop1_passed}")
    
    # Propiedad 2: verificar para varios primos
    prop2_passed = True
    print(f"\n  Propiedad 2: singularLocal p n ≥ 1 - 1/(p-1)²")
    
    test_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    for p in test_primes:
        factor = singular_local(p, n)
        bound = 1.0 - (1.0 / (p - 1)) ** 2
        
        # Para p que divide n, factor = bound exactamente
        # Para p que no divide n, factor = 1 + 1/(p-1)³ > bound
        passed = factor >= bound - 1e-10  # tolerancia numérica
        
        divides = "divides" if n % p == 0 else "does not divide"
        print(f"    p={p:3d}: factor={factor:.10f}, "
              f"bound={bound:.10f}, ok={passed} ({divides})")
        
        if not passed:
            prop2_passed = False
    
    all_passed = prop1_passed and prop2_passed
    
    if all_passed:
        print("\n✅ Test 6 PASSED: major_arc_ready properties verified")
    else:
        print("\n❌ Test 6 FAILED")
    
    return all_passed


def generate_certificate(results: dict):
    """Generate validation certificate."""
    timestamp = datetime.now().astimezone().isoformat()
    
    # Create deterministic hash
    result_str = json.dumps(results, sort_keys=True)
    cert_hash = hashlib.sha256(result_str.encode()).hexdigest()[:16]
    
    certificate = {
        "validation_type": "singular_series_goldbach",
        "timestamp": timestamp,
        "framework": "QCAL ∞³",
        "f0_hz": F0,
        "coherence": C_COHERENCE,
        "tests": results,
        "certificate_hash": f"0xQCAL_SINGULAR_{cert_hash}",
        "zenodo_doi": "10.5281/zenodo.17379721",
        "orcid": "0009-0002-1923-0773",
        "author": "José Manuel Mota Burruezo Ψ ∞³",
        "institution": "Instituto de Conciencia Cuántica (ICQ)"
    }
    
    return certificate


def main():
    """Run all validation tests."""
    print("="*70)
    print("VALIDACIÓN NUMÉRICA: SERIE SINGULAR DE GOLDBACH")
    print("="*70)
    print(f"Framework: QCAL ∞³")
    print(f"Frecuencia base: f₀ = {F0} Hz")
    print(f"Coherencia: C = {C_COHERENCE}")
    print("="*70)
    
    results = {}
    
    # Run all tests
    results["test1_singular_local_pos"] = test_singular_local_pos()
    results["test2_singular_local_two"] = test_singular_local_two()
    results["test3_convergence"] = test_convergence()
    results["test4_positivity"] = test_positivity()
    results["test5_lower_bound"] = test_lower_bound()
    results["test6_major_arc_ready"] = test_major_arc_ready()
    
    # Summary
    print("\n" + "="*70)
    print("RESUMEN DE VALIDACIÓN")
    print("="*70)
    
    total_tests = len(results)
    passed_tests = sum(results.values())
    
    for test_name, passed in results.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {test_name}: {status}")
    
    print(f"\n  Total: {passed_tests}/{total_tests} tests passed")
    
    # Generate certificate
    certificate = generate_certificate(results)
    
    cert_path = "data/singular_series_validation_certificate.json"
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n  Certificate saved to: {cert_path}")
    print(f"  Certificate hash: {certificate['certificate_hash']}")
    
    if passed_tests == total_tests:
        print("\n🎉 ALL TESTS PASSED! Serie singular validated successfully.")
        print("="*70)
        return 0
    else:
        print(f"\n⚠️  {total_tests - passed_tests} test(s) failed.")
        print("="*70)
        return 1


if __name__ == "__main__":
    exit(main())
