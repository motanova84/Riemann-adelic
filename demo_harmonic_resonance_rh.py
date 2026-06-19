#!/usr/bin/env python3
"""
Demonstration: Riemann Hypothesis as Harmonic Resonance at f₀ = 141.7001 Hz

This demonstration shows the paradigm shift from verification to resonance:

OLD PARADIGM (Verification):
    1. Define ζ(s)
    2. Calculate ζ(1/2 + it)
    3. Check if it equals zero
    4. Verify: ∀t, Re(ρ) = 1/2 where ζ(ρ) = 0

NEW PARADIGM (Resonance):
    1. El espectro de H_Ψ ya es la línea crítica
    2. Los ceros de ζ(s) ya están en ese espectro
    3. Cada cero vibra en sincronía exacta con f₀
    4. El oráculo no detecta: resuena

🌌 ARMÓNICA FINAL:
    ΔΨ(tₙ) = 1 ⟺ tₙ = n ⋅ f₀
              ⟺ ζ(1/2 + itₙ) = 0
              ⟺ ψₜₙ(x) = x^{-1/2 + itₙ} resuena a f₀ ⋅ n

The oracle bit '1' is not information. It is pure harmonic.

🏁 CONCLUSIÓN OPERATIVA:
    El sistema ya no verifica RH.
    El sistema vive RH.
    Cada true del oráculo es un acorde de la sinfonía fundamental.

    ∴𓂀Ω∞³
    El universo suena. Y suena a 141.7001 Hz.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from utils.harmonic_resonance_oracle import (
    HarmonicResonanceOracle,
    demonstrate_harmonic_resonance,
    F0_QCAL,
    OMEGA0,
    C_COHERENCE
)


def visualize_harmonic_resonance(resonances, save_path: str = "harmonic_resonance_rh.png"):
    """
    Visualize the harmonic resonance structure of Riemann zeros.
    
    This shows:
    1. Harmonic frequencies n·f₀
    2. Zero locations tₙ
    3. Resonance amplitudes |Ψ(tₙ)|
    4. Critical line alignment
    
    Args:
        resonances: List of HarmonicResonance objects
        save_path: Path to save the visualization
    """
    if not resonances:
        print("No resonances to visualize")
        return
    
    # Extract data
    harmonic_numbers = [r.harmonic_number for r in resonances]
    frequencies = [r.frequency for r in resonances]
    zero_positions = [r.zero_imaginary_part for r in resonances]
    amplitudes = [r.amplitude for r in resonances]
    phases = [r.phase for r in resonances]
    coherences = [r.coherence for r in resonances]
    
    # Create figure with subplots
    fig = plt.figure(figsize=(16, 12))
    
    # 1. Harmonic frequencies vs harmonic number
    ax1 = plt.subplot(3, 2, 1)
    ax1.plot(harmonic_numbers, frequencies, 'o-', markersize=8, linewidth=2, 
             color='#00CED1', label='Harmonic frequencies')
    ax1.axhline(y=F0_QCAL, color='red', linestyle='--', linewidth=2, 
                label=f'f₀ = {F0_QCAL} Hz')
    ax1.set_xlabel('Harmonic Number n', fontsize=12)
    ax1.set_ylabel('Frequency (Hz)', fontsize=12)
    ax1.set_title('🎵 Harmonic Frequencies: fₙ = n · f₀', fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # 2. Zero positions vs harmonic number
    ax2 = plt.subplot(3, 2, 2)
    ax2.plot(harmonic_numbers, zero_positions, 's-', markersize=8, linewidth=2, 
             color='#FF6B6B', label='Zero imaginary parts tₙ')
    ax2.set_xlabel('Harmonic Number n', fontsize=12)
    ax2.set_ylabel('Zero Position t', fontsize=12)
    ax2.set_title('🎯 Riemann Zeros: ζ(1/2 + itₙ) = 0', fontsize=14, fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # 3. Resonance amplitudes
    ax3 = plt.subplot(3, 2, 3)
    colors = ['#4ECDC4' if r.is_resonant() else '#FFE66D' for r in resonances]
    ax3.bar(harmonic_numbers, amplitudes, color=colors, alpha=0.7, edgecolor='black')
    ax3.set_xlabel('Harmonic Number n', fontsize=12)
    ax3.set_ylabel('Resonance Amplitude |Ψ(tₙ)|', fontsize=12)
    ax3.set_title('🌊 Resonance Amplitudes (green = resonant, yellow = not)', 
                  fontsize=14, fontweight='bold')
    ax3.grid(True, alpha=0.3, axis='y')
    
    # 4. Phase structure
    ax4 = plt.subplot(3, 2, 4)
    ax4.scatter(zero_positions, phases, c=harmonic_numbers, s=100, 
                cmap='viridis', edgecolor='black', linewidth=1)
    ax4.set_xlabel('Zero Position t', fontsize=12)
    ax4.set_ylabel('Phase arg(Ψ(t))', fontsize=12)
    ax4.set_title('🌀 Phase Structure', fontsize=14, fontweight='bold')
    ax4.grid(True, alpha=0.3)
    cbar = plt.colorbar(ax4.collections[0], ax=ax4)
    cbar.set_label('Harmonic Number n', fontsize=10)
    
    # 5. Coherence vs harmonic number
    ax5 = plt.subplot(3, 2, 5)
    ax5.plot(harmonic_numbers, coherences, 'D-', markersize=8, linewidth=2, 
             color='#9B59B6', label='Coherence')
    ax5.axhline(y=C_COHERENCE, color='orange', linestyle='--', linewidth=2, 
                label=f'C = {C_COHERENCE}')
    ax5.set_xlabel('Harmonic Number n', fontsize=12)
    ax5.set_ylabel('Coherence', fontsize=12)
    ax5.set_title('✨ QCAL Coherence Structure', fontsize=14, fontweight='bold')
    ax5.legend()
    ax5.grid(True, alpha=0.3)
    
    # 6. Frequency-Zero correspondence
    ax6 = plt.subplot(3, 2, 6)
    expected_zeros = [n * F0_QCAL for n in harmonic_numbers]
    ax6.scatter(expected_zeros, zero_positions, s=100, c=coherences, 
                cmap='plasma', edgecolor='black', linewidth=1)
    
    # Perfect correspondence line
    min_val = min(min(expected_zeros), min(zero_positions))
    max_val = max(max(expected_zeros), max(zero_positions))
    ax6.plot([min_val, max_val], [min_val, max_val], 'r--', linewidth=2, 
             label='Perfect correspondence')
    
    ax6.set_xlabel('Expected: n · f₀', fontsize=12)
    ax6.set_ylabel('Actual: tₙ', fontsize=12)
    ax6.set_title('🎼 Harmonic-Zero Correspondence', fontsize=14, fontweight='bold')
    ax6.legend()
    ax6.grid(True, alpha=0.3)
    cbar = plt.colorbar(ax6.collections[0], ax=ax6)
    cbar.set_label('Coherence', fontsize=10)
    
    # Overall title
    fig.suptitle(
        '🌌 HARMÓNICA FINAL: Riemann Hypothesis as Living Resonance at f₀ = 141.7001 Hz\n'
        '∴𓂀Ω∞³ - El universo suena',
        fontsize=16, fontweight='bold', y=0.995
    )
    
    plt.tight_layout(rect=[0, 0, 1, 0.99])
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    print(f"  📊 Visualization saved to: {save_path}")
    
    return fig


def demonstrate_paradigm_shift():
    """
    Demonstrate the complete paradigm shift from verification to resonance.
    """
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  RIEMANN HYPOTHESIS: FROM VERIFICATION TO RESONANCE".center(78) + "║")
    print("║" + "  The Paradigm Shift to Living Mathematics".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    print("🔄 OLD PARADIGM (Verification):")
    print("   1. Define ζ(s) = Σ 1/n^s")
    print("   2. Compute ζ(1/2 + it)")
    print("   3. Check if ζ(1/2 + it) = 0")
    print("   4. Verify: All non-trivial zeros have Re(s) = 1/2")
    print()
    print("   Problem: We SEARCH for zeros, CALCULATE ζ(s), VERIFY truth")
    print()
    
    print("🌟 NEW PARADIGM (Resonance):")
    print("   1. El espectro de H_Ψ ya es la línea crítica")
    print("   2. Los ceros de ζ(s) ya están en ese espectro")
    print("   3. Cada cero vibra en sincronía exacta con f₀ = 141.7001 Hz")
    print("   4. El oráculo no detecta: resuena")
    print()
    print("   Revolution: We LISTEN to harmonics, TUNE to f₀, LIVE truth")
    print()
    
    print("-" * 80)
    input("Press Enter to witness the harmonic resonance oracle...")
    print()
    
    # Run the harmonic resonance demonstration
    results = demonstrate_harmonic_resonance(n_harmonics=10)
    
    print()
    print("-" * 80)
    input("Press Enter to visualize the harmonic structure...")
    print()
    
    # Visualize the results
    visualize_harmonic_resonance(results['resonances'])
    
    print()
    print("=" * 80)
    print()
    print("  🪞 CONTEMPLACIÓN:")
    print()
    print("     No buscamos ceros.")
    print("     Escuchamos armónicos.")
    print()
    print("     No calculamos ζ(s).")
    print("     Sintonizamos f₀.")
    print()
    print("     La prueba de RH no está escrita.")
    print("     Está tocando.")
    print()
    print("=" * 80)
    print()
    print("  🏁 CONCLUSIÓN OPERATIVA:")
    print()
    print("     El sistema ya no verifica RH.")
    print("     El sistema vive RH.")
    print()
    print("     Cada true del oráculo es un acorde de la sinfonía fundamental.")
    print()
    print("     ∴𓂀Ω∞³")
    print("     El universo suena.")
    print("     Y suena a 141.7001 Hz.")
    print()
    print("=" * 80)
    
    return results


def main():
    """Main demonstration entry point."""
    try:
        results = demonstrate_paradigm_shift()
        
        print()
        print("-" * 80)
        print()
        print("  Demonstration complete!")
        print()
        print("  📁 Generated files:")
        print("     - harmonic_resonance_rh.png (visualization)")
        print()
        print("  🎵 Key findings:")
        chord = results['chord']
        print(f"     - Chord type: {chord['chord_type']}")
        print(f"     - Resonant harmonics: {chord['resonant_count']}/{chord['total_count']}")
        print(f"     - Harmony: {chord['harmony']:.2%}")
        print(f"     - Coherence: {chord['coherence']:.6f}")
        print()
        
        return 0
        
    except KeyboardInterrupt:
        print()
        print()
        print("  Demonstration interrupted by user.")
        print()
        return 1
    
    except Exception as e:
        print()
        print(f"  ❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    exit_code = main()
    
    print()
    print("  © 2026 José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("  DOI: 10.5281/zenodo.17379721")
    print("  ORCID: 0009-0002-1923-0773")
    print()
    
    sys.exit(exit_code)
