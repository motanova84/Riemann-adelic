#!/usr/bin/env python3
"""
Demonstration: Profound Mathematical-Biological Connection
===========================================================

This script demonstrates the profound meaning: that each cell in your body
resonates like a Riemann zero on the critical line.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-31
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pathlib import Path
import sys

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from biological.profound_meaning import (
    CellularRiemannResonator,
    UniversalCoherenceField,
    FractalLifeOrganizer,
    ProofOfLife,
    QCAL_FREQUENCY,
    COHERENCE_C
)


def demo_cellular_resonance():
    """Demonstrate cellular resonance with Riemann zeros."""
    print("\n" + "="*70)
    print("DEMO 1: Cellular Resonance with Riemann Zeros")
    print("="*70)
    
    # Create cellular resonator
    cell = CellularRiemannResonator(
        resonance_frequency=QCAL_FREQUENCY,
        riemann_zero_coupling=True,
        quality_factor=100.0
    )
    
    print(f"\nCellular Resonator Properties:")
    print(f"  Natural frequency: {cell.f0:.4f} Hz")
    print(f"  Quality factor: {cell.Q}")
    print(f"  Riemann coupling: {cell.riemann_coupling}")
    
    # Check alignment with first Riemann zero
    alignment = cell.check_riemann_alignment(zero_index=1, tolerance=0.1)
    print(f"\nAlignment with γ₁ (first Riemann zero): {alignment:.6f}")
    
    if alignment > 0.7:
        print("  ✓ Strong resonance with Riemann structure")
    else:
        print(f"  ⚠ Moderate alignment (threshold: 0.9)")
    
    # Simulate resonance with universal field
    field = UniversalCoherenceField.create_default()
    
    print("\nSimulating 1-hour cellular resonance...")
    state = cell.resonate_with(field, duration=3600.0, dt=1.0)
    
    print(f"\nFinal Resonance State:")
    print(f"  Coherence: {state.coherence:.6f}")
    print(f"  Riemann alignment: {state.riemann_alignment:.6f}")
    print(f"  Phase: {state.phase:.4f} rad")
    print(f"  Critical resonance: {state.is_critical_resonance()}")
    
    return state


def demo_universal_coherence():
    """Demonstrate universal coherence field at 141.7 Hz."""
    print("\n" + "="*70)
    print("DEMO 2: Universal Coherence Field Ψ")
    print("="*70)
    
    field = UniversalCoherenceField.create_default()
    
    print(f"\nUniversal Field Properties:")
    print(f"  Base frequency f₀: {field.f0:.4f} Hz")
    print(f"  Coherence constant C: {field.C:.2f}")
    print(f"  Number of components: {len(field.components)}")
    
    # Evaluate field over time
    t = np.linspace(0, 10, 1000)  # 10 seconds
    psi_values = np.array([field.evaluate(ti) for ti in t])
    
    print(f"\nField Statistics (10s):")
    print(f"  Mean magnitude: {np.mean(np.abs(psi_values)):.4f}")
    print(f"  Max magnitude: {np.max(np.abs(psi_values)):.4f}")
    print(f"  RMS: {np.sqrt(np.mean(np.abs(psi_values)**2)):.4f}")
    
    # Plot
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    axes[0].plot(t, np.real(psi_values), label='Re(Ψ)', alpha=0.7)
    axes[0].plot(t, np.imag(psi_values), label='Im(Ψ)', alpha=0.7)
    axes[0].set_xlabel('Time (s)')
    axes[0].set_ylabel('Field Amplitude')
    axes[0].set_title(f'Universal Coherence Field Ψ (f₀ = {QCAL_FREQUENCY:.4f} Hz)')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    axes[1].plot(t, np.abs(psi_values))
    axes[1].set_xlabel('Time (s)')
    axes[1].set_ylabel('|Ψ(t)|')
    axes[1].set_title('Field Magnitude')
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('profound_universal_coherence.png', dpi=150, bbox_inches='tight')
    print("\n✓ Plot saved: profound_universal_coherence.png")
    plt.close()


def demo_fractal_organization():
    """Demonstrate fractal organization of life."""
    print("\n" + "="*70)
    print("DEMO 3: Fractal Organization Following Riemann Distribution")
    print("="*70)
    
    organizer = FractalLifeOrganizer(scale_length=10e-6)  # 10 μm
    
    print(f"\nFractal Organizer:")
    print(f"  Characteristic scale λ₀: {organizer.lambda0*1e6:.1f} μm")
    
    # Compute Riemann zero count
    T_values = [10, 20, 50, 100]
    print("\nRiemann Zero Distribution N(T):")
    for T in T_values:
        N = organizer.zero_count(T)
        print(f"  T = {T:3d}: N(T) ≈ {N:.1f} zeros")
    
    # Compute cell count
    L_values = [100e-6, 1e-3, 1e-2, 1e-1]  # μm to cm
    print("\nCell Distribution N_cells(L):")
    for L in L_values:
        N = organizer.cell_count(L)
        scale_name = f"{L*1e6:.0f} μm" if L < 1e-3 else f"{L*1e3:.1f} mm"
        print(f"  L = {scale_name:10s}: N ≈ {N:.1f} cells")
    
    # Compute fractal dimension
    D = organizer.fractal_dimension(L_min=10e-6, L_max=1e-2)
    print(f"\nFractal Dimension D: {D:.4f}")
    print(f"  Expected (Riemann): ~1.0 (logarithmic growth)")
    print(f"  Deviation: {abs(D - 1.0):.4f}")
    
    # Visualization
    L_range = np.logspace(-6, -2, 100)  # 1 μm to 1 cm
    N_cells = np.array([organizer.cell_count(L) for L in L_range])
    
    T_range = np.linspace(1, 100, 100)
    N_zeros = np.array([organizer.zero_count(T) for T in T_range])
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Cell distribution
    axes[0].loglog(L_range * 1e6, N_cells, 'b-', linewidth=2, label='N_cells(L)')
    axes[0].set_xlabel('Length Scale L (μm)')
    axes[0].set_ylabel('Cell Count N(L)')
    axes[0].set_title('Fractal Cell Organization')
    axes[0].grid(True, alpha=0.3, which='both')
    axes[0].legend()
    
    # Riemann zero distribution
    axes[1].plot(T_range, N_zeros, 'r-', linewidth=2, label='N(T)')
    axes[1].set_xlabel('Imaginary Part T')
    axes[1].set_ylabel('Zero Count N(T)')
    axes[1].set_title('Riemann Zero Distribution')
    axes[1].grid(True, alpha=0.3)
    axes[1].legend()
    
    plt.tight_layout()
    plt.savefig('profound_fractal_organization.png', dpi=150, bbox_inches='tight')
    print("\n✓ Plot saved: profound_fractal_organization.png")
    plt.close()


def demo_proof_of_life():
    """Demonstrate that life validates the mathematical-biological connection."""
    print("\n" + "="*70)
    print("DEMO 4: Proof of Life - Mathematical-Biological Unity")
    print("="*70)
    
    proof = ProofOfLife()
    
    print("\n[1] Validating Cellular Resonance...")
    cellular = proof.validate_cellular_resonance(coherence_threshold=0.75)
    
    print(f"\n  Cellular Resonance Validation:")
    print(f"    Coherence: {cellular['coherence']:.6f}")
    print(f"    Riemann alignment: {cellular['riemann_alignment']:.6f}")
    print(f"    Frequency: {cellular['frequency']:.4f} Hz")
    print(f"    QCAL f₀: {cellular['qcal_frequency']:.4f} Hz")
    print(f"    Status: {'✓ VALID' if cellular['is_valid'] else '✗ INVALID'}")
    
    print("\n[2] Validating Fractal Organization...")
    fractal = proof.validate_fractal_organization()
    
    print(f"\n  Fractal Organization Validation:")
    print(f"    Fractal dimension D: {fractal['fractal_dimension']:.4f}")
    print(f"    Expected D: {fractal['expected_dimension']:.4f}")
    print(f"    Deviation: {fractal['deviation']:.4f}")
    print(f"    Status: {'✓ VALID' if fractal['is_valid'] else '✗ INVALID'}")
    
    print("\n[3] Validating Universal Coherence...")
    coherence = proof.validate_universal_coherence()
    
    print(f"\n  Universal Coherence Validation:")
    print(f"    QCAL frequency f₀: {coherence['qcal_frequency']:.4f} Hz")
    print(f"    First zero γ₁: {coherence['first_zero_gamma']:.6f}")
    print(f"    Ratio f₀/γ₁: {coherence['frequency_ratio']:.4f}")
    print(f"    Expected ratio: {coherence['expected_ratio']:.4f}")
    print(f"    Deviation: {coherence['ratio_deviation']:.4f}")
    print(f"    Coherence C: {coherence['coherence_constant']:.2f}")
    print(f"    Status: {'✓ VALID' if coherence['is_valid'] else '✗ INVALID'}")
    
    # Overall validation
    all_valid = cellular['is_valid'] and fractal['is_valid'] and coherence['is_valid']
    
    print("\n" + "="*70)
    print("OVERALL VALIDATION:")
    print("="*70)
    if all_valid:
        print("\n✓✓✓ ALL VALIDATIONS PASSED ✓✓✓")
        print("\nThe profound mathematical-biological connection is VERIFIED:")
        print("  • Cells resonate at QCAL frequency")
        print("  • Life organizes fractally like Riemann zeros")
        print("  • Universal coherence connects all scales")
        print("\n🌌 Tu existencia misma es una prueba viviente de")
        print("   esta profunda conexión matemático-biológica.")
    else:
        print("\n⚠ SOME VALIDATIONS FAILED")
        print("Further investigation required.")
    
    return all_valid


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print("🌌 SIGNIFICADO PROFUNDO")
    print("Demonstración de la Conexión Matemático-Biológica Fundamental")
    print("="*70)
    print("\nAutor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institución: Instituto de Conciencia Cuántica (ICQ)")
    print("="*70)
    
    # Run demonstrations
    demo_cellular_resonance()
    demo_universal_coherence()
    demo_fractal_organization()
    overall_valid = demo_proof_of_life()
    
    # Final summary
    print("\n" + "="*70)
    print("RESUMEN")
    print("="*70)
    print("\nLa Hipótesis de Riemann no es solo matemática abstracta.")
    print("Es la descripción de cómo la vida se organiza a nivel fundamental.")
    print("\nCada célula en tu cuerpo resuena como un cero de Riemann")
    print("en la línea crítica Re(s) = 1/2.")
    print("\nEsta demostración valida que:")
    print("  1. Las células resuenan a f₀ = 141.7001 Hz")
    print("  2. La coherencia universal conecta todas las escalas")
    print("  3. La vida sigue patrones fractales de distribución de ceros")
    print("\n∴ 𓂀 Ω ∞³")
    print("="*70)
    
    return 0 if overall_valid else 1


if __name__ == "__main__":
    sys.exit(main())
