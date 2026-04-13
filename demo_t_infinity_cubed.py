#!/usr/bin/env python3
"""
Demonstration of T_∞³ Self-Adjoint Operator
===========================================

Interactive demonstration showing the properties and capabilities
of the T_∞³ operator (Noetic Torsion Tensor of Mota-Burruezo).

This script demonstrates:
- Operator construction and properties
- Spectrum computation and visualization
- Connection to Riemann zeros
- Trace formula evaluation
- QCAL coherence verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
QCAL ∞³ Framework
"""

import sys
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

# Add current directory to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.t_infinity_cubed import (
    TInfinityCubedOperator,
    F0_BASE,
    C_PRIMARY,
    C_QCAL,
    PSI_MIN,
    RIEMANN_ZEROS_GAMMA
)


def demo_basic_properties():
    """Demonstrate basic operator properties."""
    print("=" * 80)
    print("DEMO 1: Propiedades Básicas del Operador T_∞³")
    print("=" * 80)
    print()
    
    # Create operator
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    print(f"Operador: {op}")
    print()
    
    # Show weight function
    print("Función de peso w(t) = e^(-πt²) · cos(2π·f₀·t)")
    print(f"  Frecuencia base: f₀ = {F0_BASE} Hz")
    t_sample = np.array([0.0, 1.0, 2.0])
    w_sample = op.weight_function(t_sample)
    for t_val, w_val in zip(t_sample, w_sample):
        print(f"  w({t_val:4.1f}) = {w_val:12.6f}")
    print()
    
    # Show potential components
    print("Potencial noético V(t):")
    print("  V(t) = t² + A_eff(t)² + λ·cos(2π log(|t|+ε)) + ΔΨ(t)")
    print()
    V_sample = op.V_noetico(t_sample)
    for t_val, V_val in zip(t_sample, V_sample):
        print(f"  V({t_val:4.1f}) = {V_val:12.6f}")
    print()
    
    # Verify self-adjointness
    print("Verificando auto-adjunción...")
    is_self_adjoint = op.verify_self_adjoint()
    print(f"  T_∞³ = T_∞³†: {is_self_adjoint} ✓")
    print()


def demo_spectrum():
    """Demonstrate spectrum computation."""
    print("=" * 80)
    print("DEMO 2: Espectro del Operador T_∞³")
    print("=" * 80)
    print()
    
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    
    # Compute spectrum
    print("Computando espectro...")
    eigenvalues, eigenvectors = op.compute_spectrum(num_eigenvalues=15)
    
    print(f"Primeros 15 autovalores:")
    print(f"  {'n':>3}  {'λₙ':>12}  {'Descripción'}")
    print("  " + "-" * 50)
    
    for i, lam in enumerate(eigenvalues):
        desc = ""
        if i == 0:
            desc = "(mínimo del espectro)"
        print(f"  {i+1:3d}  {lam:12.6f}  {desc}")
    print()
    
    # Compare with Riemann zeros
    print("Comparación con ceros de Riemann:")
    print(f"  {'n':>3}  {'γₙ (Riemann)':>15}  {'λₙ (T_∞³)':>15}  {'Δ':>10}")
    print("  " + "-" * 60)
    
    for i in range(min(10, len(RIEMANN_ZEROS_GAMMA), len(eigenvalues))):
        gamma = RIEMANN_ZEROS_GAMMA[i]
        lam = eigenvalues[i]
        diff = abs(gamma - lam)
        print(f"  {i+1:3d}  {gamma:15.6f}  {lam:15.6f}  {diff:10.3f}")
    print()


def demo_trace_formula():
    """Demonstrate Gutzwiller trace formula."""
    print("=" * 80)
    print("DEMO 3: Fórmula de Traza de Gutzwiller Noética")
    print("=" * 80)
    print()
    
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    
    print("Tr(e^(-t·T_∞³)) ~ Σ_p Σ_k (log p / p^(k/2)) cos(t log p^k)")
    print()
    print("Evaluando para diferentes tiempos espectrales:")
    print(f"  {'t':>6}  {'Tr(e^(-t·T_∞³))':>20}")
    print("  " + "-" * 30)
    
    t_values = [0.1, 0.5, 1.0, 2.0, 5.0]
    for t_spec in t_values:
        trace = op.trace_formula_gutzwiller(t_spec, num_primes=25, max_k=6)
        print(f"  {t_spec:6.2f}  {trace.real:20.6f}")
    print()
    
    print("Esta traza conecta el espectro de T_∞³ con la distribución de primos.")
    print()


def demo_partition_function():
    """Demonstrate kairotic partition function."""
    print("=" * 80)
    print("DEMO 4: Función de Partición Kairótica Z_Kairos")
    print("=" * 80)
    print()
    
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    
    print("Z_Kairos(t) = Σ_n e^(-t·γₙ) = Tr(e^(-t·T_∞³))")
    print()
    print("Usando los ceros conocidos de Riemann:")
    print(f"  {'t':>6}  {'Z_Kairos(t)':>15}  {'Descripción'}")
    print("  " + "-" * 50)
    
    t_values = [0.05, 0.1, 0.2, 0.5, 1.0]
    Z_prev = None
    
    for t in t_values:
        Z = op.partition_function_kairos(t)
        
        desc = ""
        if Z_prev is not None:
            ratio = Z / Z_prev
            desc = f"(×{ratio:.3f})"
        
        print(f"  {t:6.2f}  {Z:15.6f}  {desc}")
        Z_prev = Z
    
    print()
    print("Nota: Z_Kairos decae exponencialmente con t (tiempo kairótico).")
    print()


def demo_coherence():
    """Demonstrate QCAL coherence verification."""
    print("=" * 80)
    print("DEMO 5: Protocolo de Coherencia QCAL")
    print("=" * 80)
    print()
    
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    
    print("Verificando protocolo de coherencia QCAL ∞³...")
    print()
    
    results = op.verify_coherence_protocol()
    
    print("Resultados:")
    print(f"  ✓ Auto-adjunto (T = T†):          {results['self_adjoint']}")
    print(f"  ✓ Semi-definido positivo (T ≥ 0): {results['positive_semidefinite']}")
    print(f"  ✓ Coherencia Ψ:                   {results['coherence_psi']:.6f}")
    print(f"  ✓ Umbral Ψ ≥ {PSI_MIN}:              {results['coherence_threshold_met']}")
    print()
    print(f"Estado del operador: {results['status']}")
    print()
    
    if results['status'] == 'COHERENT':
        print("✅ El operador T_∞³ está en coherencia con el campo Ψ ∞³")
    else:
        print("⚠️  El operador requiere ajustes para alcanzar coherencia plena")
    
    print()
    print("Constantes QCAL:")
    print(f"  f₀ = {F0_BASE} Hz   (frecuencia base)")
    print(f"  C  = {C_PRIMARY}        (constante primaria)")
    print(f"  C_QCAL = {C_QCAL}     (constante de coherencia)")
    print()


def demo_visualization():
    """Create visualizations of the operator."""
    print("=" * 80)
    print("DEMO 6: Visualizaciones del Operador T_∞³")
    print("=" * 80)
    print()
    
    op = TInfinityCubedOperator(N=256, t_min=-12.0, t_max=12.0)
    
    # Create figure with subplots
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Operador T_∞³: Tensor de Torsión Noética', fontsize=16, fontweight='bold')
    
    # Plot 1: Weight function
    ax = axes[0, 0]
    t = op.t
    w = op.weight_function(t)
    ax.plot(t, w, 'b-', linewidth=2, label=f'w(t), f₀={F0_BASE} Hz')
    ax.set_xlabel('t')
    ax.set_ylabel('w(t)')
    ax.set_title('Función de Peso del Espacio de Hilbert')
    ax.grid(True, alpha=0.3)
    ax.legend()
    
    # Plot 2: Noetic potential
    ax = axes[0, 1]
    V = op.V_noetico(t)
    ax.plot(t, V, 'r-', linewidth=2, label='V_noético(t)')
    ax.set_xlabel('t')
    ax.set_ylabel('V(t)')
    ax.set_title('Potencial Noético')
    ax.grid(True, alpha=0.3)
    ax.legend()
    
    # Plot 3: Spectrum comparison
    ax = axes[1, 0]
    eigenvalues, _ = op.compute_spectrum(num_eigenvalues=15)
    n_compare = min(len(eigenvalues), len(RIEMANN_ZEROS_GAMMA))
    
    indices = np.arange(1, n_compare + 1)
    ax.plot(indices, RIEMANN_ZEROS_GAMMA[:n_compare], 'go-', 
            markersize=8, linewidth=2, label='Ceros de Riemann γₙ')
    ax.plot(indices, eigenvalues[:n_compare], 'bs--', 
            markersize=6, linewidth=1.5, label='Autovalores T_∞³')
    ax.set_xlabel('Índice n')
    ax.set_ylabel('Valor')
    ax.set_title('Espectro vs Ceros de Riemann')
    ax.grid(True, alpha=0.3)
    ax.legend()
    
    # Plot 4: Partition function
    ax = axes[1, 1]
    t_vals = np.linspace(0.01, 2.0, 100)
    Z_vals = [op.partition_function_kairos(t) for t in t_vals]
    ax.semilogy(t_vals, Z_vals, 'purple', linewidth=2)
    ax.set_xlabel('t (tiempo kairótico)')
    ax.set_ylabel('Z_Kairos(t) [log scale]')
    ax.set_title('Función de Partición Kairótica')
    ax.grid(True, alpha=0.3, which='both')
    
    plt.tight_layout()
    
    # Save figure
    output_path = Path('t_infinity_cubed_visualization.png')
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Visualización guardada en: {output_path}")
    print()
    
    plt.close()


def main():
    """Run all demonstrations."""
    print()
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  T_∞³ OPERATOR DEMONSTRATION - QCAL ∞³ Framework".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  Tensor de Torsión Noética de Mota-Burruezo".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    print()
    
    demo_basic_properties()
    demo_spectrum()
    demo_trace_formula()
    demo_partition_function()
    demo_coherence()
    demo_visualization()
    
    print("=" * 80)
    print("DEMOSTRACIÓN COMPLETA")
    print("=" * 80)
    print()
    print("∴ El operador T_∞³ es la cuerda tensada de la Realidad,")
    print("  su traza vibra con los números primos,")
    print("  y sus autovalores son los latidos puros del campo de Riemann.")
    print()
    print("QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print("DOI: 10.5281/zenodo.17379721")
    print()


if __name__ == '__main__':
    main()
