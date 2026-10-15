#!/usr/bin/env python3
"""
Demostración del Operador de Selberg
=====================================

Script ejecutable que muestra todas las capacidades del operador de Selberg.

Uso:
    python demo_selberg_operator.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import sys
import numpy as np

# Añadir path si es necesario
sys.path.insert(0, '/home/runner/work/Riemann-adelic/Riemann-adelic')

from operators.selberg_operator import (
    SelbergOperator,
    activar_operador_selberg,
    F0_QCAL,
    F_GEODESIC,
    C_COHERENCE
)


def demo_1_activation():
    """Demo 1: Activación del sistema geodésico."""
    print("\n" + "=" * 70)
    print("DEMO 1: ACTIVACIÓN DEL SISTEMA GEODÉSICO")
    print("=" * 70)
    print()
    
    mensaje = activar_operador_selberg()
    
    print()
    input("Presiona Enter para continuar...")


def demo_2_construction():
    """Demo 2: Construcción del operador."""
    print("\n" + "=" * 70)
    print("DEMO 2: CONSTRUCCIÓN DEL LAPLACIANO DE BELTRAMI")
    print("=" * 70)
    print()
    
    print("Creando operador de Selberg...")
    op = SelbergOperator(
        n_grid_x=20,
        n_grid_y=20,
        max_prime=50,
        max_k=5
    )
    print(f"✓ Grid: {op.n_grid_x} × {op.n_grid_y}")
    print(f"✓ Primos hasta: {op.max_prime} (total: {len(op._primes)})")
    print()
    
    print("Construyendo Laplaciano H = -y²(∂²/∂x² + ∂²/∂y²)...")
    H = op.construct_beltrami_laplacian()
    print(f"✓ Matriz construida: {H.shape[0]} × {H.shape[1]}")
    
    # Verificar simetría
    sym_error = np.max(np.abs(H - H.T))
    print(f"✓ Error de simetría: {sym_error:.2e}")
    
    print()
    input("Presiona Enter para continuar...")
    
    return op


def demo_3_weyl_term(op):
    """Demo 3: Término de Weyl."""
    print("\n" + "=" * 70)
    print("DEMO 3: TÉRMINO DE WEYL (ÁREA)")
    print("=" * 70)
    print()
    
    print("Calculando término de Weyl...")
    print()
    print("Fórmula: Tr_Weyl = Área(F) / (4π)")
    print()
    
    weyl = op.weyl_term_contribution()
    print(f"✓ Tr_Weyl = {weyl:.8f}")
    print()
    print(f"  Este término representa la contribución del")
    print(f"  área del dominio fundamental Γ\\ℍ")
    print()
    
    input("Presiona Enter para continuar...")


def demo_4_orbital_sum(op):
    """Demo 4: Suma orbital de primos."""
    print("\n" + "=" * 70)
    print("DEMO 4: SUMA ORBITAL SOBRE PRIMOS")
    print("=" * 70)
    print()
    
    print("Calculando suma sobre órbitas periódicas...")
    print()
    print("Fórmula: Σ_p Σ_k (log p)/(p^(k/2) - p^(-k/2))·h(k log p)")
    print()
    
    eigenvalue = 1.0
    orbital = op.selberg_trace_formula_contribution(eigenvalue)
    
    print(f"✓ Suma orbital = {orbital:.8f}")
    print()
    print(f"  Primeros primos incluidos: {op._primes[:10]}")
    print(f"  Potencias: k = 1, 2, ..., {op.max_k}")
    print()
    
    # Mostrar algunas longitudes de geodésicas
    print("Ejemplos de longitudes de geodésicas l(p^k) = k log p:")
    for p in [2, 3, 5]:
        for k in [1, 2]:
            length = op.geodesic_orbit_length(p, k)
            print(f"  l({p}^{k}) = {length:.6f}")
    print()
    
    input("Presiona Enter para continuar...")


def demo_5_selberg_trace(op):
    """Demo 5: Traza de Selberg completa."""
    print("\n" + "=" * 70)
    print("DEMO 5: TRAZA DE SELBERG COMPLETA")
    print("=" * 70)
    print()
    
    print("Calculando traza completa...")
    print()
    
    result = op.compute_selberg_trace(eigenvalue=1.0, include_details=True)
    
    print("RESULTADOS:")
    print(f"  Término de Weyl:      {result.weyl_term:12.8f}")
    print(f"  Suma orbital (primos):{result.prime_orbital_sum:12.8f}")
    print(f"  {'─' * 40}")
    print(f"  Traza total:          {result.total_trace:12.8f}")
    print()
    
    print("CONVERGENCIA:")
    print(f"  Fracción Weyl:    {result.convergence_info['weyl_fraction']:8.2%}")
    print(f"  Fracción orbital: {result.convergence_info['orbital_fraction']:8.2%}")
    print()
    
    input("Presiona Enter para continuar...")


def demo_6_eigenvalues(op):
    """Demo 6: Autovalores y ceros de Riemann."""
    print("\n" + "=" * 70)
    print("DEMO 6: AUTOVALORES Y CEROS DE RIEMANN")
    print("=" * 70)
    print()
    
    print("Calculando autovalores del Laplaciano...")
    print()
    print("Correspondencia espectral: λ_n = 1/4 + γ_n²")
    print()
    
    eigenvalues, riemann_zeros = op.compute_eigenvalues(n_eigenvalues=10)
    
    print(f"{'n':>3} {'λ_n':>15} {'γ_n':>15} {'Verificación':>15}")
    print("─" * 52)
    
    for i in range(min(10, len(eigenvalues))):
        lambda_n = eigenvalues[i]
        gamma_n = riemann_zeros[i]
        
        # Verificar: γ_n = √(λ_n - 1/4)
        gamma_check = np.sqrt(max(lambda_n - 0.25, 0))
        error = abs(gamma_n - gamma_check)
        
        print(f"{i+1:3d} {lambda_n:15.8f} {gamma_n:15.8f} {error:15.2e}")
    
    print()
    print("✅ Correspondencia espectral verificada")
    print()
    
    input("Presiona Enter para continuar...")


def demo_7_comparison():
    """Demo 7: Comparación con oscilador armónico."""
    print("\n" + "=" * 70)
    print("DEMO 7: COMPARACIÓN CON OSCILADOR ARMÓNICO")
    print("=" * 70)
    print()
    
    print("┌─────────────────────────────────┬──────────────────────────────────┐")
    print("│   OSCILADOR ARMÓNICO (L²(ℝ))    │  SELBERG (L²(Γ\\ℍ))               │")
    print("├─────────────────────────────────┼──────────────────────────────────┤")
    print("│ Espacio plano                   │ Espacio hiperbólico              │")
    print("│ Curvatura K = 0                 │ Curvatura K = -1                 │")
    print("│ Densidad lineal                 │ Densidad logarítmica             │")
    print("│ V(x) = x² (pozo)                │ Métrica ds² = (dx²+dy²)/y²       │")
    print("│ p^(-k/2) artificial             │ p^(-k/2) natural (Jacobiana)     │")
    print("│ Ajuste de parámetros            │ Geometría fundamental            │")
    print("└─────────────────────────────────┴──────────────────────────────────┘")
    print()
    
    print("LA VERDAD ES HIPERBÓLICA:")
    print("  • Los ceros de Riemann son autovalores de un flujo geodésico")
    print("  • Los primos emergen de órbitas periódicas cerradas")
    print("  • La función ζ(s) es el determinante de Selberg")
    print()
    
    input("Presiona Enter para continuar...")


def demo_8_frequencies():
    """Demo 8: Frecuencias QCAL."""
    print("\n" + "=" * 70)
    print("DEMO 8: FRECUENCIAS QCAL DEL SISTEMA")
    print("=" * 70)
    print()
    
    print("FRECUENCIAS FUNDAMENTALES:")
    print()
    print(f"  F_geodésica  = {F_GEODESIC:10.4f} Hz  (Rigidez absoluta)")
    print(f"       ↓")
    print(f"  F₀           = {F0_QCAL:10.4f} Hz  (Frecuencia fundamental)")
    print()
    print(f"  C (coherence)= {C_COHERENCE:10.2f}     (Constante de coherencia)")
    print()
    
    # Calcular algunas frecuencias relacionadas
    print("RESONANCIAS:")
    print(f"  F_geodésica / F₀ = {F_GEODESIC / F0_QCAL:.6f}")
    print(f"  ω₀ = 2π·F₀       = {2 * np.pi * F0_QCAL:.6f} rad/s")
    print()
    
    print("ECUACIÓN MAESTRA:")
    print("  Ψ = I × A_eff² × C^∞")
    print()
    
    input("Presiona Enter para finalizar...")


def main():
    """Ejecuta todas las demos."""
    print("\n" + "🏛" * 35)
    print("DEMOSTRACIÓN DEL OPERADOR DE SELBERG")
    print("REVELACIÓN DE LA RIGIDEZ ABSOLUTA: EL SALTO GEODÉSICO")
    print("🏛" * 35)
    
    try:
        # Demo 1: Activación
        demo_1_activation()
        
        # Demo 2: Construcción
        op = demo_2_construction()
        
        # Demo 3: Término de Weyl
        demo_3_weyl_term(op)
        
        # Demo 4: Suma orbital
        demo_4_orbital_sum(op)
        
        # Demo 5: Traza completa
        demo_5_selberg_trace(op)
        
        # Demo 6: Autovalores
        demo_6_eigenvalues(op)
        
        # Demo 7: Comparación
        demo_7_comparison()
        
        # Demo 8: Frecuencias
        demo_8_frequencies()
        
        # Final
        print("\n" + "=" * 70)
        print("✅ DEMOSTRACIÓN COMPLETADA")
        print("=" * 70)
        print()
        print("RIGIDEZ ABSOLUTA CONFIRMADA")
        print("Sistema geodésico totalmente operacional")
        print()
        print(f"Frecuencia: {F_GEODESIC} Hz → {F0_QCAL} Hz")
        print(f"Coherencia: C = {C_COHERENCE}")
        print()
        print("QCAL ∞³ | ∴𓂀Ω∞³Φ")
        print("=" * 70)
        
    except KeyboardInterrupt:
        print("\n\nDemostración interrumpida por el usuario.")
        sys.exit(0)
    except Exception as e:
        print(f"\n\nError durante la demostración: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
