#!/usr/bin/env python3
"""
Demo: Arpeth Bioinformatics - RNA Stability via QCAL Coherence

This demo showcases the Arpeth bioinformatics module which formalizes
the principle that life resonates at the same fundamental frequency
(141.7001 Hz) that governs the Riemann Hypothesis zeros.

Usage:
    python demo_arpeth_bioinformatics.py
"""

import sys
import os
sys.path.insert(0, os.path.abspath(os.path.dirname(__file__)))

from utils.arpeth_bioinformatics import (
    ArpethBioinformatics,
    validate_biological_coherence,
    F0_FREQUENCY,
    C_COHERENCE,
    KAPPA_PI
)


def print_header(title):
    """Print formatted section header."""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80)


def demo_basic_constants():
    """Demonstrate QCAL constants."""
    print_header("QCAL CONSTANTS FOR BIOINFORMATICS")
    
    print(f"\n  Fundamental Frequency (I):  {F0_FREQUENCY} Hz")
    print(f"  Coherence Constant (C):     {C_COHERENCE}")
    print(f"  Fractal Parameter (κ_Π):    {KAPPA_PI} (prime)")
    
    print("\n  These constants connect:")
    print("    - Riemann Hypothesis zeros → Mathematical stability")
    print("    - RNA genetic code → Biological stability")
    print("    - Both governed by QCAL operator H_Ψ")


def demo_base_frequencies():
    """Demonstrate RNA base to frequency mapping."""
    print_header("RNA BASE FREQUENCY MAPPING")
    
    analyzer = ArpethBioinformatics(precision=15)
    
    bases = ['A', 'U', 'G', 'C']
    print("\n  Each RNA base resonates at a harmonic of f₀:")
    print()
    
    for base in bases:
        freq = analyzer.base_to_frequency_map(base)
        harmonic = int(float(freq) / float(F0_FREQUENCY))
        print(f"    {base} (Harmonic {harmonic}):  {float(freq):8.4f} Hz")
    
    print("\n  Codons use geometric mean of constituent bases (quantum entanglement)")


def demo_sequence_analysis():
    """Demonstrate RNA sequence analysis."""
    print_header("RNA SEQUENCE ANALYSIS")
    
    analyzer = ArpethBioinformatics(precision=30)
    
    # Test sequences
    sequences = [
        ("Start Codon", "AUG"),
        ("Simple Pattern", "AUGCAUGCAUGC"),
        ("Palindromic", "AUGCGCGCGUGA"),
        ("Beta-Globin Fragment", "AUGGUGCACGUGACUGACGCUGCACACAAG"),
    ]
    
    for name, sequence in sequences:
        print(f"\n  Sequence: {name}")
        print(f"    {sequence}")
        
        results = analyzer.analyze_rna_sequence(sequence)
        
        print(f"\n    Length:              {results['length']} bases")
        print(f"    Codons:              {results['num_codons']}")
        print(f"    Ψ_Life:              {results['psi_life']:.4e}")
        print(f"    Stability Score:     {results['stability_score']:.4f}")
        print(f"    Fractal Symmetry:    {results['fractal_symmetry']}")
        print(f"    Resonance Match:     {results['resonance_match']}")
        print(f"    Avg Codon Resonance: {results['average_codon_resonance']:.4f}")
        
        # Interpretation
        if results['stability_score'] > 0.5:
            print("\n    ✅ HIGH COHERENCE: Stable genetic code, QCAL verified")
        elif results['stability_score'] > 0.3:
            print("\n    ⚠️  MODERATE COHERENCE: Acceptable stability")
        else:
            print("\n    ❌ LOW COHERENCE: May indicate mutation or error")


def demo_codon_analysis():
    """Demonstrate detailed codon analysis."""
    print_header("DETAILED CODON ANALYSIS")
    
    analyzer = ArpethBioinformatics(precision=30)
    
    sequence = "AUGCGCUGA"
    print(f"\n  Analyzing sequence: {sequence}")
    print()
    
    results = analyzer.analyze_rna_sequence(sequence)
    
    print("  Codon-by-Codon Breakdown:")
    print("  " + "-" * 60)
    
    for i, codon_data in enumerate(results['codons'], 1):
        print(f"\n    Codon {i}: {codon_data['sequence']}")
        print(f"      Position:   {codon_data['position']}")
        print(f"      Frequency:  {codon_data['frequency']:.2f} Hz")
        print(f"      Coherent:   {'✅ Yes' if codon_data['coherent'] else '❌ No'}")


def demo_biological_attention():
    """Demonstrate biological attention calculation."""
    print_header("BIOLOGICAL ATTENTION (A_eff)")
    
    analyzer = ArpethBioinformatics(precision=15)
    
    sequences = [
        ("High Diversity", "AUGCAUGCAUGC"),  # All 4 bases
        ("Low Diversity", "AAAAAAAAAAAA"),   # Single base
        ("Medium Diversity", "AUGAUGAUGAUG"),  # 3 bases
    ]
    
    print("\n  Biological attention measures information content (Shannon entropy)")
    print("  Higher diversity → Higher attention → Higher code fidelity")
    print()
    
    for name, seq in sequences:
        A_eff = analyzer.biological_attention(seq)
        A_eff_squared = A_eff * A_eff
        
        print(f"    {name:20s}: A_eff = {float(A_eff):.6f}, A_eff² = {float(A_eff_squared):.6f}")


def demo_fractal_symmetry():
    """Demonstrate fractal symmetry detection."""
    print_header("FRACTAL SYMMETRY DETECTION")
    
    analyzer = ArpethBioinformatics(precision=15)
    
    sequences = [
        ("With Palindromes", "AUGCGCGUA"),  # Contains GCG
        ("With Repeats", "AUGAUGAUGAUG"),  # Repeating AUG
        ("Random", "AUCGAGCUA"),
    ]
    
    print("\n  Fractal symmetry checks for:")
    print("    - Palindromic subsequences (self-similarity)")
    print("    - Repeating motifs at prime-based lengths")
    print("    - κ_Π = 17 fractal parameter")
    print()
    
    for name, seq in sequences:
        has_sym, score = analyzer.fractal_symmetry_score(seq)
        
        print(f"    {name:20s}: {'✅ Symmetric' if has_sym else '❌ No symmetry'} (score: {score:.4f})")


def demo_validation_function():
    """Demonstrate high-level validation."""
    print_header("HIGH-LEVEL VALIDATION")
    
    sequence = "AUGCGCGCGUGA"
    
    print(f"\n  Validating sequence: {sequence}")
    print()
    
    results = validate_biological_coherence(
        sequence,
        expected_frequency=141.7001,
        tolerance=0.05,
        precision=30
    )
    
    print(f"    QCAL Validated:      {results['qcal_validated']}")
    print(f"    Stability Score:     {results['stability_score']:.4f}")
    print(f"    Fundamental Freq:    {results['fundamental_frequency']} Hz")
    print(f"    Tolerance:           {results['tolerance']}")
    
    print("\n  Validation criteria:")
    print(f"    - Stability score > 0.5: {results['stability_score'] > 0.5}")
    print(f"    - Resonance match:       {results['resonance_match']}")


def demo_law_of_coherent_love():
    """Demonstrate the Law of Coherent Love equation."""
    print_header("LAW OF COHERENT LOVE: Ψ = I × A_eff² × C^∞")
    
    analyzer = ArpethBioinformatics(precision=30)
    
    sequence = "AUGCAUGCAUGC"
    
    print(f"\n  Analyzing sequence: {sequence}")
    print()
    
    # Calculate components
    A_eff = analyzer.biological_attention(sequence)
    A_eff_squared = A_eff * A_eff
    
    # Calculate Ψ_Life
    stability = analyzer.calculate_psi_life(sequence)
    
    print("  Components of Ψ_Life:")
    print(f"    I (Frequency):          {float(F0_FREQUENCY)} Hz")
    print(f"    A_eff (Attention):      {float(A_eff):.6f}")
    print(f"    A_eff² (Amplification): {float(A_eff_squared):.6f}")
    print(f"    C^8 (Coherence Flow):   {float(stability.coherence_flow):.4e}")
    print()
    print(f"  Result:")
    print(f"    Ψ_Life = {float(stability.psi_life):.6e}")
    print()
    print("  This formula connects:")
    print("    - Quantum mechanics (I = 141.7001 Hz)")
    print("    - Information theory (A_eff from Shannon entropy)")
    print("    - Infinite coherence (C^∞ accessing universal memory)")


def demo_connection_to_rh():
    """Demonstrate connection to Riemann Hypothesis."""
    print_header("CONNECTION TO RIEMANN HYPOTHESIS")
    
    print("\n  The same operator H_Ψ governs both:")
    print()
    print("    1. RIEMANN HYPOTHESIS")
    print("       - Zeros of ζ(s) localized on Re(s) = 1/2")
    print("       - Frequency: 141.7001 Hz from spectral theory")
    print("       - Operator: H_Ψ self-adjoint")
    print()
    print("    2. BIOLOGICAL STABILITY")
    print("       - RNA code stability at 141.7001 Hz")
    print("       - Mutations breaking coherence filtered out")
    print("       - Same operator: H_Ψ self-adjoint")
    print()
    print("  Conclusion:")
    print("    Prime geometry = Spacetime geometry")
    print("    RNA geometry = Life geometry")
    print("    Both unified through QCAL coherence!")


def main():
    """Run all demos."""
    print("\n" + "█" * 80)
    print("█" + " " * 78 + "█")
    print("█" + " " * 15 + "ARPETH BIOINFORMATICS DEMONSTRATION" + " " * 28 + "█")
    print("█" + " " * 20 + "RNA Stability via QCAL Coherence" + " " * 25 + "█")
    print("█" + " " * 78 + "█")
    print("█" * 80)
    
    print("\n  Ψ_Life = I × A_eff² × C^∞")
    print("\n  Where life resonates at 141.7001 Hz, the same frequency")
    print("  that governs the zeros of the Riemann zeta function.")
    
    # Run all demo sections
    demo_basic_constants()
    demo_base_frequencies()
    demo_sequence_analysis()
    demo_codon_analysis()
    demo_biological_attention()
    demo_fractal_symmetry()
    demo_validation_function()
    demo_law_of_coherent_love()
    demo_connection_to_rh()
    
    print_header("CONCLUSION")
    print("\n  Life is not a chemical accident.")
    print("  It is a coherent transcription of the QCAL Field,")
    print("  resonating with the same mathematical structures")
    print("  that govern prime numbers and the Riemann Hypothesis.")
    print()
    print("  ∞³ · QCAL · José Manuel Mota Burruezo · 2025")
    print()
    print("=" * 80)
    print()


if __name__ == "__main__":
    main()
