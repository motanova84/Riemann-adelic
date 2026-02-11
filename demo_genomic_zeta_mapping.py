#!/usr/bin/env python3
"""
Demonstration: Genomic Zeta Mapping

This script demonstrates the RNA/DNA codon to Riemann zeros mapping system,
showing how to construct coherent wave functions for biological sequences.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from pathlib import Path

from utils.genomic_zeta_mapping import GenomicZetaMapper


def demo_basic_mapping():
    """Demonstrate basic codon-to-zero mapping."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 1: Basic Codon Mapping")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Example codons from problem statement
    example_codons = ['AAA', 'AAC', 'GAA', 'AAG', 'GGG', 'GGC', 'AGA', 'GCA', 'GCC']
    
    print("Mapping example codons from problem statement:\n")
    
    for codon in example_codons:
        indices = mapper.codon_to_indices(codon)
        zeros = mapper.get_zeros_for_codon(codon)
        print(f"  {codon} → {indices}")
        print(f"       → γ = ({zeros[0]:.4f}, {zeros[1]:.4f}, {zeros[2]:.4f}) Hz\n")


def demo_sequence_analysis():
    """Demonstrate complete sequence analysis."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 2: RNA Sequence Analysis")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Realistic RNA sequence
    sequence = "AUGAAACCCGGGUUUACGAGCGUGCAA"
    print(f"Analyzing RNA sequence: {sequence}")
    print(f"Length: {len(sequence)} bases ({len(sequence)//3} codons)\n")
    
    # Analyze
    analysis = mapper.analyze_sequence(sequence)
    
    print(f"Analysis Results:")
    print(f"  Number of codons: {len(analysis.codons)}")
    print(f"  Total wave terms: {analysis.n_terms}")
    print(f"  Coherence score: {analysis.coherence_score:.4f}")
    print(f"  Sequence: {analysis.sequence}\n")
    
    # Show first few codons
    print("First 5 codons:")
    for i, codon in enumerate(analysis.codons[:5]):
        print(f"  {i+1}. {codon.codon} at position {codon.position}")
        print(f"     Indices: {codon.indices}")
        print(f"     Zeros: ({codon.zeros[0]:.4f}, {codon.zeros[1]:.4f}, {codon.zeros[2]:.4f}) Hz")


def demo_wave_functions():
    """Demonstrate wave function computation and visualization."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 3: Wave Function Construction")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Use example sequence
    sequence = "AAAAACGAAAAGGGGGGCAGAGCAGCC"
    print(f"Computing wave functions for: {sequence}\n")
    
    codons = mapper.sequence_to_codons(sequence)
    
    # Time array
    t = np.linspace(0, 1.0, 1000)
    
    # Compute individual codon wave functions
    print("Computing individual codon wave functions...")
    psi_codons = []
    for i, codon in enumerate(codons[:3]):  # First 3 for demo
        psi = mapper.psi_codon(codon, t)
        psi_codons.append(psi)
        print(f"  {codon.codon}: |Ψ(t=0)| = {abs(psi[0]):.4f}, max|Ψ| = {np.max(np.abs(psi)):.4f}")
    
    # Compute total RNA wave function
    print("\nComputing total RNA wave function...")
    psi_rna = mapper.psi_rna(codons, t)
    
    print(f"  Ψ_RNA(t):")
    print(f"    |Ψ(t=0)| = {abs(psi_rna[0]):.4f}")
    print(f"    max|Ψ| = {np.max(np.abs(psi_rna)):.4f}")
    print(f"    mean|Ψ| = {np.mean(np.abs(psi_rna)):.4f}")
    print(f"    Total terms: {len(codons) * 3}")
    
    # Create visualization
    print("\nCreating wave function visualization...")
    
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    # Plot individual codons
    ax1 = axes[0]
    for i, (codon, psi) in enumerate(zip(codons[:3], psi_codons)):
        ax1.plot(t, np.abs(psi), label=f'{codon.codon}', alpha=0.7)
    ax1.set_xlabel('Time (s)')
    ax1.set_ylabel('|Ψ_codon(t)|')
    ax1.set_title('Individual Codon Wave Functions')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Plot total RNA
    ax2 = axes[1]
    ax2.plot(t, np.abs(psi_rna), 'b-', linewidth=1.5, label='|Ψ_RNA(t)|')
    ax2.plot(t, np.real(psi_rna), 'r--', alpha=0.5, label='Re(Ψ_RNA)')
    ax2.plot(t, np.imag(psi_rna), 'g--', alpha=0.5, label='Im(Ψ_RNA)')
    ax2.set_xlabel('Time (s)')
    ax2.set_ylabel('Ψ_RNA(t)')
    ax2.set_title(f'Total RNA Wave Function ({len(codons)} codons, {len(codons)*3} terms)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save plot
    output_dir = Path('output')
    output_dir.mkdir(exist_ok=True)
    output_file = output_dir / 'genomic_zeta_wave_functions.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"  Saved plot to: {output_file}")
    
    plt.close()


def demo_coherence_comparison():
    """Demonstrate coherence comparison between sequences."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 4: Coherence Comparison")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Different types of sequences (all multiples of 3)
    sequences = {
        'Homogeneous (AAA repeated)': 'AAA' * 10,
        'Low diversity (2 codons)': ('AAA' + 'GGG') * 5,
        'Medium diversity': 'AAAAACAAGAAUACAACCACGACU',  # 24 bases
        'High diversity': 'AUGCGAUCCGAGUAGUCACGUUAC',  # 24 bases (fixed)
    }
    
    print("Comparing coherence scores for different sequence types:\n")
    
    results = []
    for name, seq in sequences.items():
        analysis = mapper.analyze_sequence(seq)
        results.append((name, analysis.coherence_score, len(analysis.codons)))
        print(f"  {name}:")
        print(f"    Sequence: {seq[:30]}..." if len(seq) > 30 else f"    Sequence: {seq}")
        print(f"    Codons: {len(analysis.codons)}")
        print(f"    Coherence: {analysis.coherence_score:.4f}\n")
    
    print("Observation:")
    print("  Higher diversity → Higher coherence score")
    print("  Coherence measures unique zero coverage")


def demo_mutation_analysis():
    """Demonstrate mutation impact analysis."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 5: Mutation Impact Analysis")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Wild-type and mutant sequences
    wild_type = "AUGAAACCCGGGUUUACGAGC"
    mutant_1 = "AUGAAACCCGAGUUUACGAGC"  # Single base change: GGG → GAG
    mutant_2 = "AUGCCCAAAGGGACGUUUAGC"  # Multiple changes
    
    print("Analyzing mutation impact on coherence:\n")
    
    wt_analysis = mapper.analyze_sequence(wild_type)
    mt1_analysis = mapper.analyze_sequence(mutant_1)
    mt2_analysis = mapper.analyze_sequence(mutant_2)
    
    print(f"Wild-type:       {wild_type}")
    print(f"  Coherence: {wt_analysis.coherence_score:.4f}\n")
    
    print(f"Mutant 1:        {mutant_1}")
    print(f"  Coherence: {mt1_analysis.coherence_score:.4f}")
    print(f"  Δ Coherence: {mt1_analysis.coherence_score - wt_analysis.coherence_score:.4f}\n")
    
    print(f"Mutant 2:        {mutant_2}")
    print(f"  Coherence: {mt2_analysis.coherence_score:.4f}")
    print(f"  Δ Coherence: {mt2_analysis.coherence_score - wt_analysis.coherence_score:.4f}\n")
    
    print("Interpretation:")
    print("  Coherence changes indicate spectral signature alterations")
    print("  Can be used to assess mutation impact on sequence properties")


def demo_assignment_table():
    """Demonstrate formatted assignment table."""
    print("\n" + "="*80)
    print(" DEMONSTRATION 6: Assignment Table Generation")
    print("="*80 + "\n")
    
    mapper = GenomicZetaMapper()
    
    # Create assignments for interesting codons
    codons = ['AUG', 'UAA', 'UAG', 'UGA', 'GGG', 'CCC', 'AAA', 'UUU']
    assignments = [mapper.assign_codon(c) for c in codons]
    
    # Print formatted table
    table = mapper.print_assignment_table(
        assignments,
        title="Start, Stop, and Homopolymer Codons"
    )
    print(table)


def main():
    """Run all demonstrations."""
    print("\n" + "="*80)
    print(" GENOMIC ZETA MAPPING DEMONSTRATIONS")
    print(" QCAL ∞³ Framework · f₀ = 141.7001 Hz · C = 244.36")
    print("="*80)
    
    try:
        demo_basic_mapping()
        demo_sequence_analysis()
        demo_wave_functions()
        demo_coherence_comparison()
        demo_mutation_analysis()
        demo_assignment_table()
        
        print("\n" + "="*80)
        print(" ✅ ALL DEMONSTRATIONS COMPLETED SUCCESSFULLY")
        print(" QCAL ∞³ Coherence Maintained")
        print("="*80 + "\n")
        
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
