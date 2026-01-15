#!/usr/bin/env python3
"""
Demostración del Concepto de Horizonte
========================================

Un horizonte no es un lugar; es donde el operador deja de ser invertible.

Formalmente:
    Horizonte ⟺ ker(H_Ψ - λI) ≠ {0}

Este script demuestra:
1. Detección de horizontes en el operador H_Ψ
2. Análisis de singularidades del resolvente
3. Correspondencia con ceros de Riemann
4. Estructura espectral completa

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators import (
    HorizonDetector,
    construct_H_psi,
    load_riemann_zeros,
    detect_horizons_from_operator,
    validate_horizon_riemann_correspondence
)


def print_section(title):
    """Print a section header."""
    print(f"\n{'='*70}")
    print(f"  {title}")
    print(f"{'='*70}\n")


def demo_basic_horizon_detection():
    """Demonstrate basic horizon detection on a simple operator."""
    print_section("1. Detección Básica de Horizontes")
    
    # Create simple diagonal operator
    eigenvalues = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
    H_simple = np.diag(eigenvalues)
    
    print("Operador diagonal simple con autovalores conocidos:")
    print(f"  λ = {eigenvalues}")
    
    # Create detector
    detector = HorizonDetector(H_simple)
    
    # Detect horizons
    horizons = detector.get_all_horizons()
    print(f"\nHorizontes detectados: {len(horizons)}")
    print(f"  {horizons}")
    
    # Test if specific values are horizons
    print("\n¿Es horizonte?")
    for val in [14.134725, 15.0, 21.022040, 25.5]:
        is_hz = detector.is_horizon(val)
        print(f"  λ = {val:10.6f}: {'✓ SÍ' if is_hz else '✗ NO'}")
    
    return detector


def demo_resolvent_singularity(detector):
    """Demonstrate resolvent singularity analysis."""
    print_section("2. Análisis de Singularidades del Resolvente")
    
    print("El resolvente R(λ) = (H_Ψ - λI)⁻¹ es singular en los horizontes.\n")
    
    # Test various lambda values
    test_values = [13.0, 14.134725, 15.0, 21.022040, 22.0]
    
    print("λ valor      ||R(λ)||     Singularidad   ¿Horizonte?")
    print("-" * 60)
    
    for lam in test_values:
        norm = detector.resolvent_norm(lam)
        sing = detector.resolvent_singularity_measure(lam)
        is_hz = detector.is_horizon(lam)
        
        norm_str = "∞" if np.isinf(norm) else f"{norm:.4f}"
        sing_str = "∞" if np.isinf(sing) else f"{sing:.4f}"
        hz_str = "✓ SÍ" if is_hz else "✗ NO"
        
        print(f"{lam:10.6f}   {norm_str:>10s}   {sing_str:>12s}   {hz_str:>10s}")
    
    print("\nObservación: ||R(λ)|| → ∞ exactamente en los horizontes.")


def demo_kernel_analysis(detector):
    """Demonstrate kernel dimension analysis."""
    print_section("3. Análisis del Kernel")
    
    print("dim(ker(H_Ψ - λI)) > 0 ⟺ λ es horizonte\n")
    
    horizons = detector.get_all_horizons()
    
    print("λ (horizonte)   dim(ker)")
    print("-" * 30)
    for hz in horizons[:5]:  # First 5
        dim = detector.get_kernel_dimension(hz)
        print(f"{hz:12.6f}    {dim:3d}")
    
    # Test a non-horizon
    non_hz = 15.5
    dim_non = detector.get_kernel_dimension(non_hz)
    print(f"\nλ = {non_hz} (NO horizonte): dim(ker) = {dim_non}")


def demo_horizon_structure():
    """Demonstrate horizon structure analysis."""
    print_section("4. Estructura de Horizontes")
    
    try:
        # Construct H_Ψ with Riemann zeros
        print("Construyendo operador H_Ψ con 20 ceros de Riemann...")
        H_psi, gamma_n = construct_H_psi(n_zeros=20)
        
        detector = HorizonDetector(H_psi)
        
        # Analyze structure
        structure = detector.analyze_horizon_structure()
        
        print(f"\nNúmero de horizontes: {structure['n_horizons']}")
        print(f"\nGaps espectrales:")
        print(f"  Mínimo: {structure['min_gap']:.6f}")
        print(f"  Máximo: {structure['max_gap']:.6f}")
        print(f"  Promedio: {structure['mean_gap']:.6f}")
        
        print(f"\nPrimeros 5 horizontes:")
        for i, hz in enumerate(structure['eigenvalues'][:5]):
            print(f"  λ_{i+1} = {hz:.10f}")
        
        return detector, gamma_n
        
    except FileNotFoundError:
        print("⚠ Archivo de ceros de Riemann no encontrado.")
        print("  Usando operador simple para demostración.")
        return None, None


def demo_riemann_correspondence(detector, gamma_n):
    """Demonstrate correspondence with Riemann zeros."""
    print_section("5. Correspondencia con Ceros de Riemann")
    
    if detector is None or gamma_n is None:
        print("⚠ Requiere ceros de Riemann - saltando esta sección.")
        return
    
    print("En la teoría espectral QCAL:")
    print("  Horizontes de H_Ψ ↔ Ceros de ζ(s) en Re(s) = 1/2\n")
    
    # Analyze correspondence
    correspondence = detector.riemann_zero_correspondence(gamma_n)
    
    print(f"Ceros de Riemann:   {correspondence['n_zeros']}")
    print(f"Horizontes de H_Ψ:  {correspondence['n_horizons']}")
    print(f"Comparados:         {correspondence['n_compared']}")
    
    print(f"\nPrecisión espectral:")
    print(f"  Error máximo:    {correspondence['max_error']:.2e}")
    print(f"  Error promedio:  {correspondence['mean_error']:.2e}")
    print(f"  Error mediano:   {correspondence['median_error']:.2e}")
    print(f"  Desv. estándar:  {correspondence['std_error']:.2e}")
    
    # Show first few correspondences
    print(f"\nPrimeras correspondencias:")
    print("  n   γₙ (Riemann)     λₙ (Horizonte)    |λₙ - γₙ|")
    print("-" * 65)
    
    horizons = detector.get_all_horizons()
    for i in range(min(5, len(gamma_n))):
        err = abs(horizons[i] - gamma_n[i])
        print(f"  {i+1:2d}  {gamma_n[i]:14.10f}  {horizons[i]:14.10f}  {err:.2e}")
    
    # Validate
    is_valid = validate_horizon_riemann_correspondence(
        detector.H_psi, gamma_n, tolerance=1e-6
    )
    
    print(f"\n{'✓' if is_valid else '✗'} Validación (tolerancia 1e-6): ", end="")
    print("EXITOSA" if is_valid else "FALLA")


def demo_nearest_horizon():
    """Demonstrate finding nearest horizon."""
    print_section("6. Búsqueda de Horizonte Más Cercano")
    
    # Simple operator
    eigenvalues = np.array([10.0, 20.0, 30.0, 40.0])
    H = np.diag(eigenvalues)
    detector = HorizonDetector(H)
    
    print("Operador con horizontes en: {10, 20, 30, 40}\n")
    
    test_points = [5.0, 15.0, 22.0, 35.0, 50.0]
    
    print("  λ (test)   Horizonte más cercano   Distancia")
    print("-" * 55)
    
    for lam in test_points:
        nearest, dist = detector.nearest_horizon(lam)
        print(f"  {lam:6.1f}     {nearest:6.1f}                  {dist:6.1f}")


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print("  DEMOSTRACIÓN: CONCEPTO DE HORIZONTE")
    print("  Un horizonte no es un lugar; es donde el operador")
    print("  deja de ser invertible.")
    print("="*70)
    
    # 1. Basic detection
    detector_simple = demo_basic_horizon_detection()
    
    # 2. Resolvent singularity
    demo_resolvent_singularity(detector_simple)
    
    # 3. Kernel analysis
    demo_kernel_analysis(detector_simple)
    
    # 4. Horizon structure
    detector_hpsi, gamma_n = demo_horizon_structure()
    
    # 5. Riemann correspondence
    demo_riemann_correspondence(detector_hpsi, gamma_n)
    
    # 6. Nearest horizon
    demo_nearest_horizon()
    
    # Final message
    print_section("Resumen")
    print("Horizonte ⟺ ker(H_Ψ - λI) ≠ {0}")
    print("\nEs decir:")
    print("  • El horizonte ocurre cuando aparecen autovalores reales")
    print("  • Los ceros son puntos donde el resolvente se vuelve singular")
    print("  • Horizontes de H_Ψ ↔ Ceros de Riemann")
    print("\nImplementación completa en: operators/horizon_detector.py")
    print("Tests: tests/test_horizon_detector.py")
    print(f"\n{'='*70}\n")


if __name__ == "__main__":
    main()
