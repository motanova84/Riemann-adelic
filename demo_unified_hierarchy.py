#!/usr/bin/env python3
"""
Demonstration of the Unified Hierarchy Framework

This script demonstrates that all five systems converge to ζ(s) as the
fundamental base, as established by the Unified Hierarchy Theorem.

Usage:
    python demo_unified_hierarchy.py [--precision DPS] [--zeros N]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import argparse
import sys
from pathlib import Path

# Add current directory to path
sys.path.insert(0, str(Path(__file__).parent))

from utils.unified_hierarchy import UnifiedHierarchySystem
import mpmath as mp


def demonstrate_system_1(hierarchy: UnifiedHierarchySystem):
    """Demonstrate System 1: φ (Fractal Modulation)"""
    print("\n" + "="*80)
    print("💎 SYSTEM 1: φ (Golden Ratio) - FRACTAL MODULATION")
    print("="*80)
    
    sys1 = hierarchy.system1_fractal_modulation()
    
    print("\nThe golden ratio φ modulates fine fluctuations of zero spacing.")
    print(f"\nφ = {hierarchy.phi}")
    print(f"\nZero spacing formula:")
    print("  Δγ_n = γ_(n+1) - γ_n ∼ (2π/log n) × (1 + ε_n φ^(-n))")
    
    print(f"\nFirst 10 zero spacings:")
    for i in range(min(10, len(sys1['spacings']))):
        delta = sys1['spacings'][i]
        weyl = sys1['weyl_predictions'][i]
        mod = sys1['modulations'][i]
        print(f"  Δγ_{i+1} = {delta:8.4f}  (Weyl: {weyl:6.4f}, Mod: {mod:+.6f})")
    
    print(f"\nAverage modulation amplitude: {sys1['average_modulation']:.6f}")
    
    print("\nφ^(-n) decay (first 10 terms):")
    for i, val in enumerate(sys1['phi_power_decay'][:10], 1):
        print(f"  φ^(-{i}) = {val:.8f}")
    
    if sys1['self_similarity']:
        print("\nSelf-similarity analysis (f_(n+k)/f_n ≈ φ^(α·k)):")
        for ratio_data in sys1['self_similarity'][:5]:
            print(f"  Index {ratio_data['index']:2d}: ratio = {ratio_data['ratio']:.4f}, "
                  f"α ≈ {ratio_data['alpha']:.4f}")


def demonstrate_system_2(hierarchy: UnifiedHierarchySystem):
    """Demonstrate System 2: ζ(n) (Analytic Moments)"""
    print("\n" + "="*80)
    print("🔮 SYSTEM 2: ζ(n) - ANALYTIC MOMENTS")
    print("="*80)
    
    sys2 = hierarchy.system2_analytic_moments()
    
    print("\nThe values ζ(n) are the 'moments' of the zero distribution.")
    print("They contain complete information about density and correlations.")
    
    print("\nSpecial values of ζ(n):")
    for n, (exact_val, formula) in sys2['exact_forms'].items():
        computed = sys2['zeta_values'][n]
        print(f"  ζ({n}) = {computed:.10f}  (exact: {formula})")
    
    print(f"\nζ'(1/2) = {sys2['zeta_prime_half']:.10f}")
    print("  This connects to f₀ via the spectral-physical bridge")
    
    print("\nEmpirical moments from zero distribution:")
    for k, moment in sys2['empirical_moments'].items():
        print(f"  M_{k} = Σ γ_n^{k} = {moment:.6e}")


def demonstrate_system_3(hierarchy: UnifiedHierarchySystem):
    """Demonstrate System 3: QCAL Codons (Symbiotic Resonance)"""
    print("\n" + "="*80)
    print("🧬 SYSTEM 3: QCAL CODONS - SYMBIOTIC RESONANCE")
    print("="*80)
    
    sys3 = hierarchy.system3_qcal_codons()
    
    print("\nCodens are 'chords' in the spectral space of ζ(s).")
    print(f"Resonance criterion: {sys3['resonance_criterion']}")
    
    print("\nDigit → Frequency mapping:")
    for digit, freq in list(sys3['digit_map'].items())[:5]:
        print(f"  Digit {digit} → {freq:.4f} Hz")
    
    print("\nCodon Analysis:")
    print("-" * 80)
    for codon_name, data in sys3['codons'].items():
        res = data['resonance']
        status = "✓ RESONANT" if res.resonant else "✗ Non-resonant"
        print(f"\n  Codon {codon_name}: {data['digits']}")
        print(f"    Frequency: {data['frequency']:.4f} Hz")
        print(f"    Nearest zero: n={res.nearest_zero_index}, γ={res.nearest_zero_gamma:.4f}")
        print(f"    Nearest freq: {res.nearest_frequency:.4f} Hz")
        print(f"    Deviation: {res.deviation:.4f} Hz")
        print(f"    Status: {status}")


def demonstrate_system_4(hierarchy: UnifiedHierarchySystem):
    """Demonstrate System 4: Harmonics (Vibrational Overtones)"""
    print("\n" + "="*80)
    print("🎵 SYSTEM 4: HARMONICS - VIBRATIONAL OVERTONES")
    print("="*80)
    
    sys4 = hierarchy.system4_harmonics()
    
    print("\nHarmonics are integer multiples: f_n^(k) = k · f_n")
    print("They arise from the Euler product: log ζ(s) = Σ_p Σ_k p^(-ks)/k")
    
    print("\nHarmonic series for first 3 fundamentals:")
    for key in list(sys4['harmonic_series'].keys())[:3]:
        data = sys4['harmonic_series'][key]
        print(f"\n  {key} (γ = {data['gamma']:.4f}):")
        print(f"    Fundamental: {data['fundamental']:.4f} Hz")
        print(f"    Harmonics 2-5: ", end="")
        print(", ".join(f"{h:.2f}" for h in data['harmonics'][1:5]))
    
    if sys4['overlaps']:
        print("\nHarmonic-Fundamental Overlaps (cross-resonances):")
        print("-" * 80)
        for overlap in sys4['overlaps'][:5]:
            print(f"  f_{overlap['fundamental_index']}×{overlap['harmonic_number']} "
                  f"≈ f_{overlap['matches_fundamental']} "
                  f"(deviation: {overlap['deviation']:.4%})")


def demonstrate_system_5(hierarchy: UnifiedHierarchySystem):
    """Demonstrate System 5: ζ(s) (Fundamental Base)"""
    print("\n" + "="*80)
    print("🌀 SYSTEM 5: ζ(s) - FUNDAMENTAL BASE")
    print("="*80)
    
    sys5 = hierarchy.system5_zeta_base()
    
    print(f"\nDefinition: {sys5['definition']}")
    print("\nζ(s) is THE fundamental base from which ALL systems emerge.")
    
    zeros = sys5['zeros']
    print(f"\nZero Properties:")
    print(f"  Total computed: {zeros['total_computed']}")
    print(f"  First zero γ₁ = {zeros['first_zero']['gamma']:.8f}")
    print(f"  First frequency f₁ = {zeros['first_zero']['frequency']:.8f} Hz")
    print(f"  Average spacing: {zeros['average_spacing']:.4f}")
    
    curvature = sys5['spectral_curvature']
    print(f"\nSpectral Curvature δζ:")
    print(f"  δζ = f₀ - 100√2")
    print(f"  Computed: {curvature['delta_zeta']:.6f} Hz")
    print(f"  Theoretical: {curvature['theoretical']:.6f} Hz")
    print(f"  Interpretation: {curvature['interpretation']}")
    
    print("\nCritical Line Sample |ζ(1/2 + it)|:")
    for sample in sys5['critical_line_sample'][:3]:
        print(f"  t = {sample['t']:8.4f}: |ζ| = {sample['|ζ(1/2+it)|']:.6f}, "
              f"arg = {sample['arg(ζ)']:+.4f}")
    
    print(f"\nRole: {sys5['role']}")


def demonstrate_convergence(hierarchy: UnifiedHierarchySystem):
    """Demonstrate the convergence theorem"""
    print("\n" + "="*80)
    print("✨ CONVERGENCE THEOREM VALIDATION")
    print("="*80)
    
    results = hierarchy.validate_convergence()
    
    print(f"\n{results['theorem']}")
    print("\nSystem Validation:")
    print("-" * 80)
    
    for system_name, data in results['systems'].items():
        print(f"\n{system_name}:")
        print(f"  {data['status']}")
        print(f"  Convergence: {data['convergence']}")
        for key, value in data.items():
            if key not in ['status', 'convergence']:
                print(f"  {key}: {value}")
    
    print("\n" + "="*80)
    print("GLOBAL COHERENCE")
    print("="*80)
    
    coh = results['global_coherence']
    print(f"\nf₀ = {coh['f0']} Hz")
    print(f"δζ = {coh['delta_zeta']} Hz")
    print(f"C_coherence = {coh['C_coherence']}")
    print(f"Coherence factor = {coh['coherence_factor']:.6f}")
    print(f"\n{coh['interpretation']}")


def main():
    """Main demonstration"""
    parser = argparse.ArgumentParser(
        description="Demonstrate Unified Hierarchy: All systems converge to ζ(s)"
    )
    parser.add_argument(
        '--precision', 
        type=int, 
        default=25,
        help='Decimal precision for calculations (default: 25)'
    )
    parser.add_argument(
        '--zeros',
        type=int,
        default=50,
        help='Number of ζ(s) zeros to compute (default: 50)'
    )
    
    args = parser.parse_args()
    
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*20 + "🌌 UNIFIED HIERARCHY DEMONSTRATION 🌌" + " "*20 + "║")
    print("╚" + "="*78 + "╝")
    
    print(f"\nInitializing system...")
    print(f"  Precision: {args.precision} decimal places")
    print(f"  Computing {args.zeros} zeros of ζ(s)...")
    
    try:
        hierarchy = UnifiedHierarchySystem(
            precision=args.precision,
            num_zeros=args.zeros
        )
        
        print(f"\n✓ Initialization complete")
        print(f"  First zero: γ₁ = {hierarchy.gammas[0]:.8f}")
        print(f"  Base frequency: f₀ = {hierarchy.f0} Hz")
        
        # Demonstrate each system
        demonstrate_system_1(hierarchy)
        demonstrate_system_2(hierarchy)
        demonstrate_system_3(hierarchy)
        demonstrate_system_4(hierarchy)
        demonstrate_system_5(hierarchy)
        
        # Show convergence
        demonstrate_convergence(hierarchy)
        
        # Print the hierarchy diagram
        hierarchy.print_hierarchy_diagram()
        
        print("\n" + "="*80)
        print("✨ CONCLUSION")
        print("="*80)
        print("\nNo hay cinco sistemas independientes.")
        print("Hay UNO SOLO: el campo ζ(s).")
        print("\nTodo lo demás es:")
        print("  • Proyección")
        print("  • Modulación")
        print("  • Resonancia")
        print("  • Consecuencia")
        print("\nY la conciencia emerge cuando:")
        print("  π_α(ζ) = π_δζ(ζ) sobre G")
        print("\n🌌 El universo es una sinfonía de ζ(s).")
        print("Y somos los acordes que resuenan en la frecuencia f₀.")
        print("="*80)
        
        return 0
        
    except Exception as e:
        print(f"\n✗ Error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
