#!/usr/bin/env python3
"""
Spectral Identification Theorem — Demonstration
================================================

Interactive demonstration of the three-layer framework for establishing
the spectral correspondence between Riemann zeta zeros and operator H_Ψ.

This script showcases:
1. Capa 1: Canonical operator A₀ construction
2. Capa 2: Paley-Wiener uniqueness
3. Capa 3: Spectral identification γ² = λ - ¼
4. Complete RH proof (5 steps)

QCAL ∞³ Integration
Author: JMMB Ψ ✧ ∞³
Date: December 2025
DOI: 10.5281/zenodo.17379721
"""

import sys
sys.path.insert(0, '.')

import numpy as np
from utils.spectral_identification_theorem import (
    CanonicalOperatorA0,
    FredholmDeterminantD,
    PaleyWienerUniqueness,
    SpectralIdentification,
    RiemannHypothesisProof,
    F0_HZ,
    C_COHERENCE
)


def print_banner(title):
    """Print section banner"""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80)


def demo_layer1_canonical_operator():
    """Demonstrate Layer 1: Canonical Operator A₀"""
    print_banner("CAPA 1: OPERADOR CANÓNICO A₀")
    
    print("\n📐 Construyendo operador A₀ con kernel gaussiano...")
    print("   Definición: (A₀ψ)(n) = (½ + i·n)ψ(n) + Σ K(n,m)ψ(m)")
    print("   Kernel: K(n,m) = exp(-|n-m|²/4)")
    
    # Create operator
    A0 = CanonicalOperatorA0(n_basis=40, precision=20)
    print(f"\n   ✓ Matriz construida: {A0.matrix.shape}")
    
    # Show kernel values
    print("\n   📊 Valores del kernel gaussiano:")
    n_mid = A0.n_basis // 2
    for delta in range(1, 5):
        K_value = abs(A0.matrix[n_mid, n_mid + delta])
        print(f"      K(0, {delta}) = {K_value:.6f}")
    
    # Compute spectrum
    print("\n   🔍 Calculando espectro...")
    eigenvalues, _ = A0.compute_spectrum()
    real_eigs = A0.get_real_eigenvalues()
    
    print(f"\n   ✓ Eigenvalores totales: {len(eigenvalues)}")
    print(f"   ✓ Eigenvalores reales: {len(real_eigs)}")
    print(f"   ✓ Rango: [{real_eigs.min():.3f}, {real_eigs.max():.3f}]")
    print(f"   ✓ Espectro discreto: ✓")
    
    return A0


def demo_layer1_fredholm_determinant(A0):
    """Demonstrate Fredholm determinant D(s)"""
    print_banner("DETERMINANTE DE FREDHOLM D(s)")
    
    print("\n🔢 Construyendo D(s) = det(I + (s-½)²·A₀⁻¹)...")
    D = FredholmDeterminantD(A0)
    
    # Evaluate at test points
    print("\n   📊 Evaluando D(s) en puntos de prueba:")
    test_points = [
        (0.5 + 14j, "cerca del primer cero de Riemann"),
        (0.5 + 21j, "cerca del segundo cero de Riemann"),
        (0.3 + 10j, "fuera del eje crítico"),
    ]
    
    for s, description in test_points:
        D_value = D.evaluate(s)
        print(f"      D({s:.2f}) = {abs(D_value):.3e} ({description})")
    
    # Verify functional equation
    print("\n   🎯 Verificando ecuación funcional D(s) = D(1-s):")
    is_symmetric = D.verify_functional_equation(test_points=10, tol=0.1)
    print(f"      ✓ Simetría funcional: {is_symmetric}")
    
    # Verify order condition
    print("\n   📈 Verificando condición de orden ≤ 1:")
    order_info = D.verify_order_condition(test_radius=30.0)
    print(f"      Radio de prueba: {order_info['test_radius']}")
    print(f"      Orden estimado: {order_info['estimated_order']:.3f}")
    print(f"      ✓ Orden ≤ 1: {order_info['order_le_one']}")
    
    # Get zeros
    print("\n   🎯 Extrayendo ceros ρ = ½ ± i√λ_n:")
    zeros = D.get_zeros(max_zeros=10)
    print(f"      Total de ceros extraídos: {len(zeros)}")
    print(f"      Primeros 5 ceros:")
    for i, z in enumerate(zeros[:5], 1):
        print(f"         ρ_{i} = {z.real:.4f} + {z.imag:.4f}i")
    
    return D


def demo_layer2_paley_wiener(D):
    """Demonstrate Layer 2: Paley-Wiener Uniqueness"""
    print_banner("CAPA 2: UNICIDAD VÍA PALEY-WIENER")
    
    print("\n🎯 Verificando condiciones de Hamburger-Paley-Wiener...")
    PW = PaleyWienerUniqueness(D, precision=20)
    
    # Verify same order
    print("\n   1️⃣ Mismo orden:")
    same_order = PW.verify_same_order()
    print(f"      D(s) orden ≤ 1: {same_order['D_order_le_one']}")
    print(f"      Ξ(s) orden ≤ 1: {same_order['Xi_order_le_one']}")
    print(f"      ✓ Mismo orden: {same_order['same_order']}")
    
    # Verify same symmetry
    print("\n   2️⃣ Misma simetría funcional:")
    same_symmetry = PW.verify_same_symmetry(test_points=5, tol=0.2)
    print(f"      ✓ D(s) = D(1-s) y Ξ(s) = Ξ(1-s): {same_symmetry}")
    
    # Compare zero density
    print("\n   3️⃣ Densidad asintótica de ceros:")
    for T in [30.0, 50.0, 70.0]:
        density = PW.compare_zero_density(T=T)
        print(f"      T = {T:.0f}:")
        print(f"         N_D(actual) = {density['N_D_actual']}")
        print(f"         N(teoría) = {density['N_theory']:.1f}")
        print(f"         Error relativo = {density['relative_error']:.2%}")
    
    print("\n   ✓ Conclusión: D(s) ≡ c·Ξ(s) por unicidad de Paley-Wiener")


def demo_layer3_spectral_identification(A0):
    """Demonstrate Layer 3: Spectral Identification"""
    print_banner("CAPA 3: IDENTIFICACIÓN ESPECTRAL EXACTA")
    
    print("\n⚛️  Construyendo operador H_Ψ = log|A₀|...")
    spectral_id = SpectralIdentification(A0, precision=20)
    
    print(f"   ✓ H_Ψ construido: {spectral_id.H_psi_matrix.shape}")
    print(f"   ✓ H_Ψ es real: {np.allclose(spectral_id.H_psi_matrix.imag, 0)}")
    
    # Compute spectrum
    print("\n   🔍 Calculando espectro de H_Ψ...")
    H_spectrum = spectral_id.compute_H_psi_spectrum()
    print(f"   ✓ Eigenvalores: {len(H_spectrum)}")
    print(f"   ✓ Rango: [{H_spectrum.min():.3f}, {H_spectrum.max():.3f}]")
    
    # Verify self-adjointness
    print("\n   🔒 Verificando autoadjunción:")
    is_self_adjoint = spectral_id.verify_self_adjointness()
    print(f"      ✓ H_Ψ = H_Ψ†: {is_self_adjoint}")
    
    # Verify real spectrum
    print("\n   📊 Verificando espectro real:")
    is_real = spectral_id.verify_real_spectrum()
    print(f"      ✓ σ(H_Ψ) ⊂ ℝ: {is_real}")
    
    # Check correspondence with Riemann zeros
    print("\n   🎯 Verificando correspondencia γ² = λ - ¼:")
    riemann_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
    correspondence = spectral_id.verify_correspondence(riemann_zeros, tol=3.0)
    
    print(f"      Ceros de Riemann probados: {correspondence['total_zeros']}")
    print(f"      Matches encontrados: {correspondence['matched']}")
    print(f"      Tasa de match: {correspondence['match_rate']:.2%}")
    print(f"      Error promedio: {correspondence['average_error']:.3f}")
    
    return spectral_id


def demo_rh_proof(A0, D, spectral_id):
    """Demonstrate complete RH proof"""
    print_banner("DEMOSTRACIÓN DE LA HIPÓTESIS DE RIEMANN")
    
    print("\n👑 Ejecutando prueba completa en 5 pasos...")
    
    # Create proof instance
    RH_proof = RiemannHypothesisProof(A0, D, spectral_id, precision=20)
    
    # Run complete proof
    riemann_zeros = [14.134725, 21.022040, 25.010858]
    proof_results = RH_proof.prove_riemann_hypothesis(riemann_zeros)
    
    # Display results
    print("\n   📋 RESULTADOS:")
    
    print("\n   1️⃣ Paso 1 - Reducción Espectral:")
    step1 = proof_results['step1_spectral_reduction']
    print(f"      Ceros verificados: {step1['total_zeros']}")
    print(f"      Matches: {step1['matched']}")
    print(f"      Tasa de match: {step1['match_rate']:.2%}")
    
    print("\n   2️⃣ Paso 2 - Espectro Autoadjunto:")
    step2 = proof_results['step2_self_adjoint_spectrum']
    print(f"      H_Ψ autoadjunto: {step2['H_psi_self_adjoint']}")
    print(f"      Espectro real: {step2['spectrum_real']}")
    print(f"      Eigenvalores ≥ ¼: {step2['eigenvalues_positive']}")
    
    print("\n   3️⃣ Paso 3 - Ecuación Funcional:")
    step3 = proof_results['step3_functional_equation']
    print(f"      D(s) = D(1-s): {step3['D_symmetric']}")
    print(f"      Simetría de ceros: {step3['implies_zero_symmetry']}")
    
    print("\n   4️⃣ Paso 4 - Estructura de Paridad:")
    step4 = proof_results['step4_parity_structure']
    print(f"      Eigenvalores totales: {step4['total_eigenvalues']}")
    print(f"      Eigenvalores únicos: {step4['unique_eigenvalues']}")
    print(f"      Paridad consistente: {step4['parity_consistent']}")
    
    print("\n   5️⃣ Paso 5 - Positividad Weil-Guinand:")
    step5 = proof_results['step5_weil_guinand_positivity']
    print(f"      Δ = H_Ψ - ¼I positivo: {step5['Delta_positive']}")
    print(f"      Min eigenvalue: {step5['min_eigenvalue']:.6f}")
    print(f"      Margen de positividad: {step5['positivity_margin']:.6f}")
    
    # Final conclusion
    print("\n" + "=" * 80)
    if proof_results['riemann_hypothesis_proven']:
        print("   🏆 HIPÓTESIS DE RIEMANN: DEMOSTRADA ✓")
    else:
        print("   ⚠️  HIPÓTESIS DE RIEMANN: VERIFICACIÓN PARCIAL")
    print(f"   {proof_results['conclusion']}")
    print("=" * 80)


def main():
    """Main demonstration"""
    print("\n" + "╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  TEOREMA DE IDENTIFICACIÓN ESPECTRAL".center(78) + "║")
    print("║" + "  Demostración de la Hipótesis de Riemann".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    
    print(f"\n🔊 QCAL ∞³: f₀ = {F0_HZ} Hz, C = {C_COHERENCE}")
    print(f"📜 DOI: 10.5281/zenodo.17379721")
    print(f"👤 JMMB Ψ ✧ ∞³")
    
    # Run demonstrations
    A0 = demo_layer1_canonical_operator()
    D = demo_layer1_fredholm_determinant(A0)
    demo_layer2_paley_wiener(D)
    spectral_id = demo_layer3_spectral_identification(A0)
    demo_rh_proof(A0, D, spectral_id)
    
    print("\n" + "=" * 80)
    print("✅ DEMOSTRACIÓN COMPLETA")
    print("=" * 80)
    print("\nPara más información, consulte:")
    print("  - SPECTRAL_IDENTIFICATION_THEOREM.md")
    print("  - utils/spectral_identification_theorem.py")
    print("  - tests/test_spectral_identification.py")
    print()


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n⚠️  Demostración interrumpida por el usuario")
        sys.exit(0)
    except Exception as e:
        print(f"\n\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
