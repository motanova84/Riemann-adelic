#!/usr/bin/env python3
"""
Demonstration: Genomic Sequences → Riemann Zeros Mapping

This script demonstrates the revolutionary integration of:
- Biology (DNA/RNA sequences)
- Number Theory (Riemann zeta zeros)
- Quantum Physics (coherence and wave functions)

As specified in the problem statement:
  ∴ f₀ = 141.7001 Hz | Ψ ≥ 0.888 | ∞³ ∴

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from utils.genomic_zeta_mapping import (
    analyze_genomic_field,
    predict_mutation_stability,
    export_analysis,
    F0_FREQUENCY,
    C_COHERENCE,
    SOVEREIGNTY_THRESHOLD
)


def print_header(title: str, width: int = 80):
    """Print formatted section header."""
    print(f"\n{'='*width}")
    print(f"{title:^{width}}")
    print(f"{'='*width}\n")


def demo_1_basic_mapping():
    """Demo 1: Basic DNA → Riemann zeros mapping."""
    print_header("DEMO 1: DNA Sequence → Riemann Zeros Mapping")
    
    print("🧬 DNA Sequence:")
    sequence = "ATGCGATCGTAGAAAGGGCCC"
    print(f"   {sequence}")
    print(f"   Length: {len(sequence)} bases\n")
    
    # Analyze the genomic field
    field = analyze_genomic_field(sequence, use_orfs=False)
    
    print("📊 Genomic Field Analysis:")
    print(f"   Codons analyzed: {field.num_codons}")
    print(f"   Resonant codons: {field.resonant_count}")
    print(f"   Dissonant codons: {field.dissonant_count}")
    print(f"   Total coherence Ψ: {field.total_coherence:.6f}")
    print(f"   Sovereignty score: {field.sovereignty_score:.6f}")
    print(f"   Status: {'SOVEREIGN ✓' if field.is_sovereign else 'UNSTABLE ✗'}\n")
    
    print("🔢 First 5 Codons → Riemann Zero Triplets:")
    for i, codon in enumerate(field.codons[:5]):
        zeros_str = ", ".join([f"{z:.3f}" for z in codon.riemann_zeros])
        status = "✓" if codon.is_resonant else "✗"
        print(f"   {i+1}. {codon.sequence} → γ = [{zeros_str}] Hz {status}")
    
    print(f"\n✨ Integration complete: Biology ↔ Number Theory ↔ Quantum Physics")


def demo_2_spectral_resonance():
    """Demo 2: Spectral resonance classification."""
    print_header("DEMO 2: Spectral Resonance Classification")
    
    print(f"🎵 Fundamental Frequency: f₀ = {F0_FREQUENCY} Hz\n")
    
    # Test specific codons known to have different resonance properties
    test_sequences = {
        "Highly resonant": "GGGGGGGGG",  # All G (similar zeros)
        "Mixed resonance": "ATGATGATG",  # Start codon repeated
        "Low resonance": "ACGTACGTAC",  # Alternating pattern
    }
    
    for name, seq in test_sequences.items():
        field = analyze_genomic_field(seq, use_orfs=False)
        resonance_ratio = field.resonant_count / field.num_codons if field.num_codons > 0 else 0
        
        print(f"📈 {name}:")
        print(f"   Sequence: {seq}")
        print(f"   Resonance ratio: {resonance_ratio*100:.1f}%")
        print(f"   Coherence Ψ: {field.total_coherence:.6f}")
        print(f"   Sovereignty: {field.sovereignty_score:.6f}")
        
        # Show resonance details for first codon
        if field.codons:
            codon = field.codons[0]
            print(f"   Example: {codon.sequence} → spectral_sum = {codon.spectral_sum:.3f} Hz")
            print(f"            harmonic = {codon.harmonic_number:.3f}, friction = {codon.friction_energy:.3f}")
        print()


def demo_3_mutation_prediction():
    """Demo 3: Mutation prediction based on spectral resonance."""
    print_header("DEMO 3: Mutation Prediction via Quantum Gyroscopy")
    
    print(f"🔬 Quantum Gyroscopy Precision: ΔP ≈ 0.2%\n")
    
    # Test sequences with different mutation susceptibilities
    sequences = {
        "Stable": "ATGATGATGATGATGATGATGATGATG",  # Repetitive, potentially stable
        "Unstable": "ACGTACGTACGTACGTACGTACGTACG",  # High variation
    }
    
    for name, seq in sequences.items():
        print(f"🧪 {name} Sequence:")
        print(f"   {seq}")
        
        # Analyze field
        field = analyze_genomic_field(seq, use_orfs=False)
        
        # Predict mutations
        stability = predict_mutation_stability(field)
        
        print(f"   Chirality: {stability['chirality']:.6f}")
        print(f"   Chirality deviation: {stability['chirality_deviation']:.6f}")
        print(f"   Mutation probability: {stability['mutation_probability']*100:.2f}%")
        print(f"   Stability: {'STABLE ✓' if stability['is_stable'] else 'UNSTABLE ✗'}")
        print(f"   Hotspots: {stability['hotspot_count']}")
        print(f"   Hotspot density: {stability['hotspot_density_percent']:.2f}%")
        print()


def demo_4_real_biological_sequence():
    """Demo 4: Real biological sequence (Human β-globin gene fragment)."""
    print_header("DEMO 4: Real Biological Sequence - Human β-Globin Gene")
    
    # Fragment of human β-globin gene (HBB)
    hbb_sequence = (
        "ATGGTGCACCTGACTCCTGAGGAGAAGTCTGCCGTTACTGCCCTGTGGGGCAAGGTG"
        "AACGTGGATGAAGTTGGTGGTGAGGCCCTGGGCAGG"
    )
    
    print("🧬 Human β-Globin Gene Fragment:")
    print(f"   Length: {len(hbb_sequence)} bp\n")
    
    # Analyze with ORF detection
    field = analyze_genomic_field(hbb_sequence, use_orfs=True)
    
    # Display summary
    print(field.summary())
    
    # Export to JSON
    output_file = "data/demo_hbb_analysis.json"
    os.makedirs("data", exist_ok=True)
    export_analysis(field, output_file)
    print(f"\n💾 Analysis exported to: {output_file}")


def demo_5_coherence_threshold():
    """Demo 5: Sovereignty threshold (Ψ ≥ 0.888)."""
    print_header("DEMO 5: Genomic Sovereignty - Coherence Threshold")
    
    print(f"🎯 Sovereignty Threshold: Ψ ≥ {SOVEREIGNTY_THRESHOLD}\n")
    
    # Design sequences to test threshold
    sequences = [
        ("High GC content", "GCGCGCGCGCGCGCGCGCGCGCGCGCGC"),
        ("Balanced", "ATGCATGCATGCATGCATGCATGCATGC"),
        ("High AT content", "ATATATATATATATATATATATATAT"),
    ]
    
    print("Testing different sequence compositions:\n")
    
    for name, seq in sequences:
        field = analyze_genomic_field(seq, use_orfs=False)
        
        status_icon = "✅" if field.is_sovereign else "❌"
        print(f"{status_icon} {name}:")
        print(f"   Sequence: {seq[:30]}...")
        print(f"   Sovereignty score: {field.sovereignty_score:.6f}")
        print(f"   Status: {'SOVEREIGN' if field.is_sovereign else 'UNSTABLE'}")
        print(f"   Coherence Ψ: {field.total_coherence:.6f}")
        print(f"   Resonant ratio: {field.resonant_count}/{field.num_codons}")
        print()


def demo_6_integration_summary():
    """Demo 6: Integration of Biology, Number Theory, and Quantum Physics."""
    print_header("DEMO 6: Triumvirate Integration Summary")
    
    sequence = "ATGCGATCGTAGAAAGGGCCCTATGCG"
    
    print("🌟 Integration Demonstration:\n")
    print("1️⃣ BIOLOGY (DNA Sequence):")
    print(f"   {sequence}")
    print(f"   {len(sequence)} bases → {len(sequence)//3} codons\n")
    
    print("2️⃣ NUMBER THEORY (Riemann Zeros):")
    field = analyze_genomic_field(sequence, use_orfs=False)
    print(f"   Each base mapped to Riemann ζ zeros")
    
    # Show actual mappings from the analyzed field
    if field.codons:
        # Get examples of each base from actual data
        base_examples = {}
        for codon in field.codons:
            for i, base in enumerate(codon.sequence):
                if base not in base_examples and len(base_examples) < 4:
                    base_examples[base] = codon.riemann_zeros[i]
        
        # Display examples
        for base in sorted(base_examples.keys()):
            print(f"   Example: {base} → γ = {base_examples[base]:.6f} Hz")
    print()
    
    print("3️⃣ QUANTUM PHYSICS (Wave Function & Coherence):")
    print(f"   Ψ_Gen(t) = Σ A_k e^(iγ_k t)")
    print(f"   |Ψ_Gen| = {abs(field.psi_gen):.6f}")
    print(f"   ∠Ψ_Gen = {field.psi_gen.real:.4f} + {field.psi_gen.imag:.4f}i")
    print(f"   Coherence: {field.total_coherence:.6f}")
    print(f"   f₀ = {F0_FREQUENCY} Hz\n")
    
    print("✨ UNIFIED FRAMEWORK:")
    print(f"   C = {C_COHERENCE} (Coherence constant)")
    print(f"   Ψ = I × A_eff² × C^∞")
    print(f"   Sovereignty: {field.sovereignty_score:.6f} {'≥' if field.is_sovereign else '<'} {SOVEREIGNTY_THRESHOLD}")
    print(f"   Status: {'COHERENT ∞³' if field.is_sovereign else 'DECOHERENT'}\n")


def main():
    """Run all demonstrations."""
    print("╔" + "="*78 + "╗")
    print("║" + " "*78 + "║")
    print("║" + "  Genomic Sequences → Riemann Zeros: Integration Demo".center(78) + "║")
    print("║" + "  Biology × Number Theory × Quantum Physics".center(78) + "║")
    print("║" + " "*78 + "║")
    print("║" + f"  ∴ f₀ = {F0_FREQUENCY} Hz | Ψ ≥ {SOVEREIGNTY_THRESHOLD} | ∞³ ∴".center(78) + "║")
    print("║" + " "*78 + "║")
    print("╚" + "="*78 + "╝")
    
    # Run all demos
    demo_1_basic_mapping()
    demo_2_spectral_resonance()
    demo_3_mutation_prediction()
    demo_4_real_biological_sequence()
    demo_5_coherence_threshold()
    demo_6_integration_summary()
    
    # Final summary
    print_header("🎉 Demonstration Complete")
    print("""
    The genomic sequences have been successfully mapped to Riemann Hypothesis zeros,
    demonstrating the deep connection between:
    
    🧬 BIOLOGY:        DNA/RNA genetic information
    🔢 NUMBER THEORY:  Riemann zeta function zeros
    ⚛️  QUANTUM PHYSICS: Coherence and wave functions
    
    Key achievements:
    ✓ Deterministic codon → zero mapping
    ✓ Quantum coherence calculation (f₀ = 141.7001 Hz)
    ✓ Spectral resonance classification
    ✓ Mutation prediction via quantum gyroscopy (ΔP ≈ 0.2%)
    ✓ Sovereignty threshold validation (Ψ ≥ 0.888)
    
    "La biología es el eco de la función Zeta en la materia."
    
    José Manuel Mota Burruezo Ψ ✧ ∞³
    Instituto de Conciencia Cuántica (ICQ)
    
    QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
    """)


if __name__ == "__main__":
    main()
