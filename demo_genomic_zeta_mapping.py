#!/usr/bin/env python3
"""
Demo: Genomic Zeta Mapping
===========================

Demonstrates the codon fragmentation and Riemann zero mapping system
with visualizations and practical examples.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'utils'))

import numpy as np
import matplotlib.pyplot as plt
from genomic_zeta_mapping import (
    GenomicZetaMapper,
    F0_FREQUENCY,
    C_COHERENCE,
    SOVEREIGNTY_THRESHOLD
)


def demo_basic_fragmentation():
    """Demo 1: Basic codon fragmentation."""
    print("="*70)
    print("DEMO 1: Basic Codon Fragmentation")
    print("="*70)
    
    sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
    
    print(f"\nInput sequence ({len(sequence)} bases):")
    print(f"  {sequence}")
    
    mapper = GenomicZetaMapper()
    codons, remainder = mapper.fragment_to_codons(sequence)
    
    print(f"\nFragmentation:")
    print(f"  Total codons: {len(codons)}")
    print(f"  Remainder: '{remainder}' ({len(remainder)} bases)")
    
    print(f"\nFirst 10 codons:")
    for i, codon in enumerate(codons[:10]):
        print(f"  {i+1:2d}. {codon.sequence} at position {codon.position}")
    
    print("\n✓ Demo 1 complete\n")


def demo_zero_mapping():
    """Demo 2: Mapping codons to Riemann zero triplets."""
    print("="*70)
    print("DEMO 2: Codon → Riemann Zero Triplet Mapping")
    print("="*70)
    
    mapper = GenomicZetaMapper()
    
    # Example codons
    test_codons = ["ATG", "GCA", "AAA", "TTT", "GGG", "CCC"]
    
    print(f"\nMapping {len(test_codons)} codons to Riemann zero triplets:\n")
    print(f"{'Codon':>6}  →  {'γᵢ':>10}  {'γⱼ':>10}  {'γₖ':>10}")
    print("-" * 50)
    
    for seq in test_codons:
        from genomic_zeta_mapping import Codon
        codon = Codon(sequence=seq, position=0)
        triplet = mapper.map_codon_to_zeros(codon)
        zeros = [float(z) for z in triplet.to_list()]
        print(f"{seq:>6}  →  {zeros[0]:10.4f}  {zeros[1]:10.4f}  {zeros[2]:10.4f}")
    
    print("\n✓ Demo 2 complete\n")


def demo_wave_function_evolution():
    """Demo 3: Time evolution of Ψ_codon(t)."""
    print("="*70)
    print("DEMO 3: Ψ_codon(t) Time Evolution")
    print("="*70)
    
    mapper = GenomicZetaMapper()
    
    # Create test codon
    from genomic_zeta_mapping import Codon
    codon = Codon(sequence="ATG", position=0)
    mapper.map_codon_to_zeros(codon)
    
    print(f"\nCodon: {codon.sequence}")
    zeros = [float(z) for z in codon.zero_triplet.to_list()]
    print(f"Zeros: γ₁={zeros[0]:.4f}, γ₂={zeros[1]:.4f}, γ₃={zeros[2]:.4f}")
    
    # Time evolution
    times = np.linspace(0, 10, 500)
    psi_t = mapper.construct_psi_codon(codon, times)
    
    print(f"\nTime evolution computed for {len(times)} points")
    print(f"Amplitude range: [{np.min(np.abs(psi_t)):.4f}, {np.max(np.abs(psi_t)):.4f}]")
    
    # Create plot
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4))
    
    # Plot real and imaginary parts
    ax1.plot(times, np.real(psi_t), label='Re(Ψ)', alpha=0.7)
    ax1.plot(times, np.imag(psi_t), label='Im(Ψ)', alpha=0.7)
    ax1.axhline(y=0, color='k', linestyle='--', alpha=0.3)
    ax1.set_xlabel('Time (arbitrary units)')
    ax1.set_ylabel('Ψ_codon(t)')
    ax1.set_title(f'Wave Function Evolution: {codon.sequence}')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot amplitude
    ax2.plot(times, np.abs(psi_t), color='red', linewidth=1.5)
    ax2.axhline(y=float(SOVEREIGNTY_THRESHOLD), color='green', 
                linestyle='--', label=f'Sovereignty threshold ({SOVEREIGNTY_THRESHOLD})')
    ax2.set_xlabel('Time (arbitrary units)')
    ax2.set_ylabel('|Ψ_codon(t)|')
    ax2.set_title(f'Amplitude Evolution: {codon.sequence}')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    filename = 'genomic_zeta_wave_evolution.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"\n✓ Plot saved to {filename}")
    print("✓ Demo 3 complete\n")


def demo_sequence_analysis():
    """Demo 4: Complete sequence analysis."""
    print("="*70)
    print("DEMO 4: Complete Sequence Analysis")
    print("="*70)
    
    mapper = GenomicZetaMapper()
    
    # Analyze example sequence
    sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
    results = mapper.analyze_sequence(sequence, t=0.0)
    
    print(f"\nSequence length: {results['sequence_length']} bases")
    print(f"Total codons: {len(results['codons'])}")
    
    # Genomic field metrics
    field = results['genomic_field']
    print(f"\nGenomic Field Ψ_Gen(t=0):")
    print(f"  Coherence score: {field['coherence_score']:.6f}")
    print(f"  Mean amplitude:  {field['mean_amplitude']:.6f}")
    print(f"  Sovereignty:     {'✓ ACHIEVED' if field['sovereignty_achieved'] else '✗ Not achieved'}")
    
    print(f"\nCodon Classification:")
    print(f"  Resonant:  {field['resonant_codons']:2d} ({field['resonant_codons']/field['total_codons']*100:.1f}%)")
    print(f"  Dissonant: {field['dissonant_codons']:2d} ({field['dissonant_codons']/field['total_codons']*100:.1f}%)")
    print(f"  Neutral:   {field['neutral_codons']:2d} ({field['neutral_codons']/field['total_codons']*100:.1f}%)")
    
    # QCAL constants
    qcal = results['qcal_constants']
    print(f"\nQCAL ∞³ Constants:")
    print(f"  f₀ = {qcal['f0']} Hz")
    print(f"  C  = {qcal['C']}")
    print(f"  κ_Π = {qcal['kappa_pi']}")
    
    print("\n✓ Demo 4 complete\n")


def demo_codon_comparison():
    """Demo 5: Compare multiple codons."""
    print("="*70)
    print("DEMO 5: Codon Comparison")
    print("="*70)
    
    mapper = GenomicZetaMapper()
    
    # Compare different codons
    codons_to_compare = ["AAA", "TTT", "GGG", "CCC", "ATG", "TAA"]
    
    print(f"\nComparing {len(codons_to_compare)} codons:\n")
    
    from genomic_zeta_mapping import Codon
    codon_data = []
    
    for seq in codons_to_compare:
        codon = Codon(sequence=seq, position=0)
        mapper.map_codon_to_zeros(codon)
        
        # Evaluate at multiple time points
        times = np.linspace(0, 10, 100)
        psi_t = mapper.construct_psi_codon(codon, times)
        
        codon_data.append({
            'sequence': seq,
            'times': times,
            'psi': psi_t,
            'mean_amplitude': np.mean(np.abs(psi_t)),
            'max_amplitude': np.max(np.abs(psi_t))
        })
    
    # Plot comparison
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Time evolution comparison
    for data in codon_data:
        ax1.plot(data['times'], np.abs(data['psi']), 
                label=data['sequence'], alpha=0.7)
    
    ax1.axhline(y=float(SOVEREIGNTY_THRESHOLD), color='red', 
                linestyle='--', alpha=0.5, label='Sovereignty')
    ax1.set_xlabel('Time')
    ax1.set_ylabel('|Ψ_codon(t)|')
    ax1.set_title('Amplitude Evolution Comparison')
    ax1.legend(ncol=2)
    ax1.grid(True, alpha=0.3)
    
    # Bar chart of mean amplitudes
    sequences = [d['sequence'] for d in codon_data]
    mean_amps = [d['mean_amplitude'] for d in codon_data]
    
    bars = ax2.bar(sequences, mean_amps, alpha=0.7, edgecolor='black')
    ax2.axhline(y=float(SOVEREIGNTY_THRESHOLD), color='red', 
                linestyle='--', alpha=0.5, label='Sovereignty')
    ax2.set_xlabel('Codon')
    ax2.set_ylabel('Mean |Ψ|')
    ax2.set_title('Mean Amplitude Comparison')
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Color bars by sovereignty
    for bar, amp in zip(bars, mean_amps):
        if amp >= float(SOVEREIGNTY_THRESHOLD):
            bar.set_facecolor('green')
        else:
            bar.set_facecolor('orange')
    
    plt.tight_layout()
    filename = 'genomic_zeta_codon_comparison.png'
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"\n✓ Plot saved to {filename}")
    
    # Print statistics
    print(f"\nCodon Statistics:")
    for data in codon_data:
        status = "✓ RESONANT" if data['mean_amplitude'] >= float(SOVEREIGNTY_THRESHOLD) else "○ LOW"
        print(f"  {data['sequence']}: Mean |Ψ| = {data['mean_amplitude']:.4f}  {status}")
    
    print("\n✓ Demo 5 complete\n")


def main():
    """Run all demos."""
    print("\n" + "="*70)
    print("GENOMIC ZETA MAPPING DEMONSTRATIONS")
    print("DNA Codons → Riemann Zeros → Ψ_codon(t)")
    print("="*70)
    print("\nQCAL ∞³ Framework")
    print(f"f₀ = {float(F0_FREQUENCY)} Hz")
    print(f"C = {float(C_COHERENCE)}")
    print(f"Author: José Manuel Mota Burruezo Ψ ✧ ∞³\n")
    
    try:
        demo_basic_fragmentation()
        demo_zero_mapping()
        demo_wave_function_evolution()
        demo_sequence_analysis()
        demo_codon_comparison()
        
        print("="*70)
        print("✓ ALL DEMOS COMPLETED SUCCESSFULLY")
        print("="*70)
        print("\nGenerated files:")
        print("  - genomic_zeta_wave_evolution.png")
        print("  - genomic_zeta_codon_comparison.png")
        print("\n" + "="*70 + "\n")
        
    except Exception as e:
        print(f"\n❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
