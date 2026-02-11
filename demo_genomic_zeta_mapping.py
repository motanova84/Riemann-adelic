#!/usr/bin/env python3
"""
Demo script for Genomic Zeta Mapping (Gen→Zeta Framework)

Demonstrates the revolutionary mapping between DNA sequences and
Riemann zeta zeros, bridging biology and spectral mathematics.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

from utils.genomic_zeta_mapping import (
    analyze_genomic_field,
    export_analysis,
    find_orfs,
    predict_mutation_stability,
    F0_FREQUENCY,
    SOVEREIGNTY_THRESHOLD
)


def demo_simple_sequence():
    """Demo 1: Analyze a simple DNA sequence."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║          DEMO 1: Simple DNA Sequence Analysis                ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    # Simple sequence with clear codons
    sequence = "ATGCGATAGCTAGCT"
    
    print(f"Analyzing sequence: {sequence}")
    print(f"Length: {len(sequence)} bp\n")
    
    field = analyze_genomic_field(sequence, use_orfs=False)
    
    print("Analysis Results:")
    print("-" * 80)
    print(f"Codons analyzed: {field.num_codons}")
    print(f"Resonant codons: {field.resonant_count} ({100*field.resonant_count/field.num_codons:.1f}%)")
    print(f"Dissonant codons: {field.dissonant_count} ({100*field.dissonant_count/field.num_codons:.1f}%)")
    print(f"\nCoherence Ψ: {field.total_coherence:.6f}")
    print(f"Sovereignty Score: {field.sovereignty_score:.6f}")
    print(f"Status: {'SOVEREIGN ✓' if field.is_sovereign else 'UNSTABLE ✗'}")
    
    print("\nCodon Details:")
    for codon in field.codons:
        print(f"  {codon}")
    
    print("\n" + "="*80 + "\n")


def demo_orf_detection():
    """Demo 2: ORF detection and analysis."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║          DEMO 2: Open Reading Frame Detection                ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    # Sequence with multiple ORFs
    sequence = "AAATGCGATCGATCGTAAGGGATGCCCCCTAG"
    
    print(f"Searching for ORFs in: {sequence}")
    print(f"Length: {len(sequence)} bp\n")
    
    orfs = find_orfs(sequence, min_length=9)
    
    print(f"Found {len(orfs)} ORF(s):")
    for i, (start, end, frame) in enumerate(orfs, 1):
        orf_seq = sequence[start:end]
        print(f"\n  ORF {i}:")
        print(f"    Position: {start}-{end} (frame {frame})")
        print(f"    Sequence: {orf_seq}")
        print(f"    Length: {len(orf_seq)} bp")
    
    # Analyze with ORF mode
    field = analyze_genomic_field(sequence, use_orfs=True, min_orf_length=9)
    print(f"\n  Total codons in ORFs: {field.num_codons}")
    print(f"  Sovereignty: {field.sovereignty_score:.6f}")
    
    print("\n" + "="*80 + "\n")


def demo_biological_sequence():
    """Demo 3: Real biological sequence (Human HBB gene)."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║     DEMO 3: Real Biological Sequence (Human β-globin)        ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    # Human HBB gene start (β-globin)
    hbb_sequence = """
    ATGGTGCATCTGACTCCTGAGGAGAAGTCTGCCGTTACTGCCCTGTGGGGCAAGGTGAACGTGGATGAAGTTGGTGGTGAGGCCCTGGGCAGG
    TTGGTATCAAGGTTACAAGACAGGTTTAAGGAGACCAATAGAAACTGGGCATGTGGAGACAGAGAAGACTCTTGGGTTTCTGATAGGCACTGAC
    CTTTCTGCCCTGAGCCAGGGAGCTGTGGTGAACCAGGCCAGGCCAGGGCTGGGCATAAAAGTCAGGGCAGAGCCATCTATTGCTTACATTTGCT
    """.replace('\n', '').replace(' ', '').upper()
    
    print("Human β-globin (HBB) gene fragment")
    print(f"Length: {len(hbb_sequence)} bp")
    print(f"First 60 bp: {hbb_sequence[:60]}...\n")
    
    print("Analyzing with ORF detection...\n")
    field = analyze_genomic_field(hbb_sequence, use_orfs=True)
    
    # Display summary
    print(field.summary())
    
    # Mutation analysis
    print("\nMutation Stability Analysis:")
    print("-" * 80)
    mutation_pred = predict_mutation_stability(field)
    print(f"Chirality: {mutation_pred['chirality']:.6f}")
    print(f"Mutation Probability: {mutation_pred['mutation_probability']*100:.2f}%")
    print(f"Stability: {'STABLE ✓' if mutation_pred['is_stable'] else 'UNSTABLE ✗'}")
    print(f"Mutation Hotspots: {mutation_pred['hotspot_count']} zones")
    
    # Show some interesting codons
    print("\nSample Codons:")
    print("-" * 80)
    for i, codon in enumerate(field.codons[:5]):
        print(codon)
    
    if len(field.codons) > 10:
        print(f"... ({len(field.codons) - 5} more codons)")
    
    print("\n" + "="*80 + "\n")


def demo_resonance_classification():
    """Demo 4: Resonance vs Dissonance classification."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║        DEMO 4: Resonance vs Dissonance Classification         ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    print(f"Fundamental frequency f₀ = {F0_FREQUENCY} Hz")
    print(f"Sovereignty threshold = {SOVEREIGNTY_THRESHOLD}\n")
    
    # Test various codon patterns
    sequences = {
        "Homopolymer A": "AAA" * 10,
        "Homopolymer G": "GGG" * 10,
        "Alternating AT": "ATATATAT" * 3,
        "Alternating CG": "CGCGCGCG" * 3,
        "Mixed random": "ATGCGATAGCTAGCTAGCTACGA"
    }
    
    results = []
    for name, seq in sequences.items():
        field = analyze_genomic_field(seq, use_orfs=False)
        results.append({
            'name': name,
            'field': field
        })
    
    print("Sequence Type Comparison:")
    print("-" * 80)
    print(f"{'Type':<20} {'Codons':<8} {'Resonant%':<12} {'Coherence':<12} {'Sovereignty':<12}")
    print("-" * 80)
    
    for r in results:
        name = r['name']
        f = r['field']
        resonant_pct = 100 * f.resonant_count / max(1, f.num_codons)
        print(f"{name:<20} {f.num_codons:<8} {resonant_pct:<12.1f} {f.total_coherence:<12.6f} {f.sovereignty_score:<12.6f}")
    
    print("\n" + "="*80 + "\n")


def demo_mutation_prediction():
    """Demo 5: Mutation hotspot prediction."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║         DEMO 5: Mutation Hotspot Prediction (ΔP ≈ 0.2%)      ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    # Create sequences with expected different mutation profiles
    sequences = {
        "High coherence": "ATG" * 15,
        "Mixed stability": "ATGCGATAGCTAGCTAGCT" * 2,
        "Potential unstable": "ATATATATATCGCGCGCGCG"
    }
    
    print("Mutation Prediction Analysis:")
    print("=" * 80)
    
    for name, seq in sequences.items():
        field = analyze_genomic_field(seq, use_orfs=False)
        mutation_pred = predict_mutation_stability(field)
        
        print(f"\n{name}:")
        print(f"  Length: {len(seq)} bp, Codons: {field.num_codons}")
        print(f"  Coherence: {field.total_coherence:.6f}")
        print(f"  Chirality: {mutation_pred['chirality']:.6f}")
        print(f"  Mutation probability: {mutation_pred['mutation_probability']*100:.2f}%")
        print(f"  Stability: {'STABLE ✓' if mutation_pred['is_stable'] else 'UNSTABLE ✗'}")
        print(f"  Hotspots: {mutation_pred['hotspot_count']}")
        
        if field.mutation_hotspots:
            print(f"  Hotspot positions: {field.mutation_hotspots[:5]}...")
    
    print("\n" + "="*80 + "\n")


def demo_export():
    """Demo 6: Export analysis to JSON."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║              DEMO 6: Export Analysis to JSON                  ║")
    print("╚═══════════════════════════════════════════════════════════════╝\n")
    
    sequence = "ATGCGATAGCTAGCTAGCTA"
    field = analyze_genomic_field(sequence, use_orfs=False)
    
    # Export to JSON
    result = export_analysis(field)
    
    print("Exported JSON structure:")
    print("-" * 80)
    import json
    print(json.dumps(result, indent=2)[:800] + "\n  ...\n}")
    
    # Save to file
    output_file = "/tmp/genomic_field_demo.json"
    export_analysis(field, output_file)
    print(f"\n✓ Full analysis saved to: {output_file}")
    
    print("\n" + "="*80 + "\n")


def main():
    """Run all demos."""
    print("\n")
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║         GENOMIC ZETA MAPPING DEMONSTRATION                    ║")
    print("║              Gen→Zeta Framework · QCAL ∞³                    ║")
    print("║                  141.7001 Hz · Ψ = I × A² × C^∞              ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    
    demos = [
        demo_simple_sequence,
        demo_orf_detection,
        demo_biological_sequence,
        demo_resonance_classification,
        demo_mutation_prediction,
        demo_export
    ]
    
    for demo in demos:
        try:
            demo()
        except Exception as e:
            print(f"❌ Error in {demo.__name__}: {e}")
            import traceback
            traceback.print_exc()
    
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║                    DEMONSTRATION COMPLETE                     ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    print('"La biología es el eco de la función Zeta en la materia."')
    print("José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Instituto de Conciencia Cuántica (ICQ)")
    print()


if __name__ == "__main__":
    main()
