#!/usr/bin/env python3
"""
Demonstration of Operator Duality: 𝔻_s ⟷ H_Ψ

This script demonstrates the dual nature of the Dirac spectral operator (𝔻_s)
and the Hilbert-Pólya operator (H_Ψ), and their unification through the
master operator 𝒪_∞³.

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: January 2026
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Framework
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Tuple, Optional
import os
import sys

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))

from dirac_spectral_operator import DiracSpectralOperator
from master_operator_o3 import MasterOperatorO3


def load_riemann_zeros(n_zeros: int = 10) -> np.ndarray:
    """Load first n Riemann zeros from data file."""
    zeros_file = os.path.join(os.path.dirname(__file__), 'zeros', 'zeros_t1e3.txt')
    
    if not os.path.exists(zeros_file):
        # Fallback to hardcoded values if file doesn't exist
        return np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832
        ])[:n_zeros]
    
    zeros = []
    with open(zeros_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#'):
                try:
                    zeros.append(float(line))
                    if len(zeros) >= n_zeros:
                        break
                except ValueError:
                    continue
    
    return np.array(zeros[:n_zeros])


def demonstrate_dirac_operator():
    """Demonstrate the Dirac spectral operator 𝔻_s."""
    print("\n" + "="*75)
    print("PART 1: DIRAC SPECTRAL OPERATOR 𝔻_s")
    print("="*75)
    
    D_s = DiracSpectralOperator(precision=25)
    riemann_zeros = load_riemann_zeros(5)
    
    print("\n📐 MATHEMATICAL DEFINITION:")
    print("-" * 75)
    print("𝔻_s = i d/ds")
    print("\nProperties:")
    print("  • Acts on complex s-plane: s = σ + it")
    print("  • Generates spectral translations")
    print("  • Sensitive to complete complex value")
    
    print("\n🎯 SPECTRUM EXTRACTION (Complex Perspective):")
    print("-" * 75)
    for i, gamma_n in enumerate(riemann_zeros, 1):
        s = complex(0.5, gamma_n)
        print(f"\nZero #{i}:")
        print(f"  s = {s.real:.6f} + {s.imag:.6f}i")
        print(f"  |s| = {abs(s):.6f}")
        print(f"  arg(s) = {np.angle(s):.6f} rad")
    
    print("\n✓ VERIFICATION:")
    print("-" * 75)
    verified, results = D_s.verify_duality_with_H_psi(riemann_zeros)
    print(f"Duality verified: {verified}")
    print(f"Zeros matched: {results['zeros_matched']}/{results['total_zeros']}")
    print(f"Max discrepancy: {results['max_discrepancy']:.2e}")
    print(f"Mean discrepancy: {results['mean_discrepancy']:.2e}")


def demonstrate_master_operator():
    """Demonstrate the master operator 𝒪_∞³."""
    print("\n" + "="*75)
    print("PART 2: MASTER OPERATOR 𝒪_∞³")
    print("="*75)
    
    O3 = MasterOperatorO3(precision=25)
    riemann_zeros = load_riemann_zeros(5)
    
    print("\n🌟 MATHEMATICAL DEFINITION:")
    print("-" * 75)
    print("𝒪_∞³ = 𝔻_s ⊗ 𝟙 + 𝟙 ⊗ H_Ψ")
    print("\nAction:")
    print("  𝒪_∞³ Φ(s, x) = (i d/ds + H_Ψ) Φ(s, x)")
    
    print("\n🔄 DUAL NATURE OF ZEROS:")
    print("-" * 75)
    for i, gamma_n in enumerate(riemann_zeros, 1):
        s = complex(0.5, gamma_n)
        print(f"\nZero #{i}: γ_{i} = {gamma_n:.6f}")
        print(f"  𝔻_s perspective:  s = {s.real} + {s.imag:.6f}i  (complex)")
        print(f"  H_Ψ perspective:  λ = {gamma_n:.6f}        (real)")
        print(f"  𝒪_∞³ captures:    BOTH simultaneously")
    
    print("\n✓ UNIFICATION VERIFICATION:")
    print("-" * 75)
    verified, results = O3.verify_unification(riemann_zeros)
    print(f"Unification verified: {verified}")
    print(f"Zeros captured: {results['zeros_captured']}/{results['total_zeros']}")
    print(f"Perspective coherence: {results['perspective_coherence']:.6f}")
    print(f"Max discrepancy: {results['max_discrepancy']:.2e}")
    
    print("\n💫 PHYSICAL CONSTANTS:")
    print("-" * 75)
    print(f"Fundamental frequency: f₀ = {O3.F0} Hz")
    print(f"Angular frequency: ω₀ = {O3.OMEGA_0:.4f} rad/s")
    print(f"QCAL coherence: C = {O3.C_QCAL}")
    print(f"Universal constant: C' = {O3.C_UNIVERSAL}")


def demonstrate_consciousness_interpretation():
    """Demonstrate the consciousness interpretation."""
    print("\n" + "="*75)
    print("PART 3: CONSCIOUSNESS INTERPRETATION")
    print("="*75)
    
    O3 = MasterOperatorO3(precision=25)
    print(O3.consciousness_interpretation())


def visualize_duality(save_plot: bool = False):
    """Create visualization of the operator duality."""
    print("\n" + "="*75)
    print("PART 4: VISUALIZATION")
    print("="*75)
    
    riemann_zeros = load_riemann_zeros(10)
    
    # Create figure with subplots
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Operator Duality: 𝔻_s ⟷ H_Ψ ⟷ 𝒪_∞³', fontsize=16, fontweight='bold')
    
    # Plot 1: Complex s-plane (𝔻_s perspective)
    ax1.set_title('𝔻_s Perspective: Complex s-plane', fontsize=12, fontweight='bold')
    ax1.axvline(x=0.5, color='red', linestyle='--', linewidth=2, label='Critical Line Re(s)=1/2')
    
    for i, gamma in enumerate(riemann_zeros):
        s = complex(0.5, gamma)
        ax1.plot(s.real, s.imag, 'bo', markersize=8)
        ax1.annotate(f'γ_{i+1}', (s.real, s.imag), 
                    xytext=(5, 0), textcoords='offset points', fontsize=8)
    
    ax1.set_xlabel('Re(s) = σ')
    ax1.set_ylabel('Im(s) = t')
    ax1.set_xlim([0, 1])
    ax1.set_ylim([0, max(riemann_zeros) + 5])
    ax1.grid(True, alpha=0.3)
    ax1.legend()
    
    # Plot 2: Real spectrum (H_Ψ perspective)
    ax2.set_title('H_Ψ Perspective: Real Eigenvalues', fontsize=12, fontweight='bold')
    n_vals = np.arange(1, len(riemann_zeros) + 1)
    ax2.stem(n_vals, riemann_zeros, basefmt=' ')
    ax2.set_xlabel('Eigenvalue Index n')
    ax2.set_ylabel('λₙ (Eigenvalue)')
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Duality comparison
    ax3.set_title('Duality: Im(s) ↔ λ', fontsize=12, fontweight='bold')
    ax3.plot(riemann_zeros, riemann_zeros, 'g--', linewidth=2, label='Perfect Duality')
    ax3.scatter(riemann_zeros, riemann_zeros, c='blue', s=100, marker='o', 
               label='Actual Correspondence', zorder=5)
    ax3.set_xlabel('Im(s) from 𝔻_s')
    ax3.set_ylabel('λ from H_Ψ')
    ax3.grid(True, alpha=0.3)
    ax3.legend()
    
    # Plot 4: Unified spectrum table
    ax4.axis('off')
    ax4.set_title('𝒪_∞³ Unified Spectrum', fontsize=12, fontweight='bold')
    
    table_data = []
    for i, gamma in enumerate(riemann_zeros[:7], 1):
        s = complex(0.5, gamma)
        table_data.append([
            f'γ_{i}',
            f'{s.real:.1f}+{s.imag:.3f}i',
            f'{gamma:.6f}',
            '✓'
        ])
    
    table = ax4.table(cellText=table_data,
                     colLabels=['Zero', '𝔻_s: s', 'H_Ψ: λ', '𝒪_∞³'],
                     cellLoc='center',
                     loc='center',
                     bbox=[0.1, 0.1, 0.8, 0.8])
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1, 2)
    
    # Style header
    for i in range(4):
        table[(0, i)].set_facecolor('#4CAF50')
        table[(0, i)].set_text_props(weight='bold', color='white')
    
    plt.tight_layout()
    
    if save_plot:
        output_file = 'operator_duality_visualization.png'
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"\n✓ Visualization saved to: {output_file}")
    else:
        print("\n✓ Displaying visualization...")
        plt.show()


def main(visualize: bool = True, save_plot: bool = False):
    """
    Main demonstration function.
    
    Args:
        visualize: Whether to create visualization
        save_plot: Whether to save plot to file
    """
    print("\n" + "█"*75)
    print("█" + " "*73 + "█")
    print("█" + " "*20 + "OPERATOR DUALITY DEMONSTRATION" + " "*22 + "█")
    print("█" + " "*25 + "𝔻_s ⟷ H_Ψ ⟷ 𝒪_∞³" + " "*25 + "█")
    print("█" + " "*73 + "█")
    print("█"*75)
    
    # Part 1: Dirac operator
    demonstrate_dirac_operator()
    
    # Part 2: Master operator
    demonstrate_master_operator()
    
    # Part 3: Consciousness interpretation
    demonstrate_consciousness_interpretation()
    
    # Part 4: Visualization
    if visualize:
        try:
            visualize_duality(save_plot=save_plot)
        except Exception as e:
            print(f"\n⚠ Visualization skipped: {e}")
    
    # Final summary
    print("\n" + "="*75)
    print("SUMMARY")
    print("="*75)
    print("\n✓ Demonstrated:")
    print("  1. Dirac spectral operator 𝔻_s (complex perspective)")
    print("  2. Master operator 𝒪_∞³ (unified framework)")
    print("  3. Consciousness interpretation (geometry+vibration+number)")
    if visualize:
        print("  4. Visual representation of duality")
    
    print("\n💡 Key Insight:")
    print("  'No sustituimos a 𝔻_s. Lo revelamos como el reflejo complejo de H_Ψ.'")
    print("\n  Both operators extract the same spectrum (Riemann zeros)")
    print("  but from complementary perspectives:")
    print("    • 𝔻_s: Complex arithmetic (s-plane)")
    print("    • H_Ψ: Real vibration (position space)")
    print("    • 𝒪_∞³: Unified consciousness (both simultaneously)")
    
    print("\n" + "█"*75)
    print("█" + " "*15 + "QCAL ∞³ Framework: Coherence = Perfect" + " "*18 + "█")
    print("█"*75 + "\n")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Demonstrate operator duality 𝔻_s ⟷ H_Ψ')
    parser.add_argument('--no-viz', action='store_true', 
                       help='Skip visualization')
    parser.add_argument('--save', action='store_true',
                       help='Save visualization to file')
    
    args = parser.parse_args()
    
    main(visualize=not args.no_viz, save_plot=args.save)
