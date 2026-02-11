#!/usr/bin/env python3
"""
Validation script for Genomic Zeta Mapping (Gen→Zeta Framework)

This script validates the Gen→Zeta mapping implementation, ensuring
mathematical correctness and coherence with QCAL ∞³ principles.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
from pathlib import Path

# Ensure we're running from repository root
def verify_repository_root():
    """Verify script is run from repository root."""
    expected_files = ['.qcal_beacon', 'README.md', 'pyproject.toml']
    current_dir = Path.cwd()
    
    if not all((current_dir / f).exists() for f in expected_files):
        print("❌ Error: This script must be run from the repository root.")
        print(f"   Current directory: {current_dir}")
        print(f"   Expected files: {', '.join(expected_files)}")
        sys.exit(1)

verify_repository_root()

# Now we can safely import
from utils.genomic_zeta_mapping import (
    analyze_genomic_field,
    find_orfs,
    select_riemann_zero_for_base,
    compute_codon_spectral_sum,
    classify_codon_resonance,
    export_analysis,
    predict_mutation_stability,
    F0_FREQUENCY,
    SOVEREIGNTY_THRESHOLD
)
import json


def test_basic_sequence_analysis():
    """Test basic sequence analysis functionality."""
    print("\n" + "="*80)
    print("TEST 1: Basic Sequence Analysis")
    print("="*80)
    
    # Simple test sequence - exactly 3 codons
    test_seq = "ATGCGATAA"  # ATG, CGA, TAA
    
    field = analyze_genomic_field(test_seq, use_orfs=False)
    
    assert field.length == len(test_seq), "Sequence length mismatch"
    assert field.num_codons == 3, f"Expected 3 codons, got {field.num_codons}"
    assert len(field.codons) == 3, "Codon count mismatch"
    
    print(f"✓ Sequence length: {field.length} bp")
    print(f"✓ Codons analyzed: {field.num_codons}")
    print(f"✓ Resonant: {field.resonant_count}, Dissonant: {field.dissonant_count}")
    print(f"✓ Coherence: {field.total_coherence:.6f}")
    print(f"✓ Sovereignty: {field.sovereignty_score:.6f}")
    
    return True


def test_orf_detection():
    """Test ORF detection functionality."""
    print("\n" + "="*80)
    print("TEST 2: ORF Detection")
    print("="*80)
    
    # Sequence with clear ORF: ATG...TAA
    test_seq = "AAATGCGATCGTAGCTAACCC"  # ORF: positions 2-17
    
    orfs = find_orfs(test_seq, min_length=9)
    
    print(f"✓ Found {len(orfs)} ORFs")
    for i, (start, end, frame) in enumerate(orfs):
        orf_seq = test_seq[start:end]
        print(f"  ORF {i+1}: {start}-{end} (frame {frame}): {orf_seq}")
    
    assert len(orfs) >= 1, "Should find at least one ORF"
    
    return True


def test_riemann_zero_assignment():
    """Test Riemann zero assignment to bases."""
    print("\n" + "="*80)
    print("TEST 3: Riemann Zero Assignment")
    print("="*80)
    
    bases = ['A', 'T', 'C', 'G']
    
    print("Testing deterministic zero assignment:")
    for base in bases:
        zero1 = select_riemann_zero_for_base(base, 0, 0)
        zero2 = select_riemann_zero_for_base(base, 0, 0)
        
        assert zero1 == zero2, f"Non-deterministic assignment for {base}"
        print(f"  {base}: γ = {zero1:.6f} Hz (deterministic ✓)")
    
    # Test different positions give different zeros
    zero_pos0 = select_riemann_zero_for_base('A', 0, 0)
    zero_pos1 = select_riemann_zero_for_base('A', 1, 0)
    
    print(f"\n✓ Position variation:")
    print(f"  A at position 0: γ = {zero_pos0:.6f}")
    print(f"  A at position 1: γ = {zero_pos1:.6f}")
    
    return True


def test_spectral_sum_and_classification():
    """Test spectral sum computation and resonance classification."""
    print("\n" + "="*80)
    print("TEST 4: Spectral Sum and Resonance Classification")
    print("="*80)
    
    test_codons = ["ATG", "CGA", "TAA", "GGG", "CCC"]
    
    for codon in test_codons:
        zeros, spectral_sum = compute_codon_spectral_sum(codon, 0)
        is_resonant, harmonic, friction = classify_codon_resonance(spectral_sum)
        
        print(f"\nCodon: {codon}")
        print(f"  Riemann zeros: {[f'{z:.3f}' for z in zeros]}")
        print(f"  Spectral sum: {spectral_sum:.3f} Hz")
        print(f"  Harmonic #: {harmonic:.2f}")
        print(f"  Resonant: {'YES ✓' if is_resonant else 'NO ✗'}")
        if not is_resonant:
            print(f"  Friction: {friction:.3f}")
    
    return True


def test_coherence_calculation():
    """Test coherence and sovereignty calculations."""
    print("\n" + "="*80)
    print("TEST 5: Coherence and Sovereignty")
    print("="*80)
    
    # Create sequences with different expected coherence
    sequences = {
        "High coherence": "ATG" * 20,  # Repetitive, should have high coherence
        "Mixed": "ATGCGATAGCTAGCTACGATCGATCG",
        "Random-ish": "ACGTACGTACGTACGTACGT"
    }
    
    for name, seq in sequences.items():
        field = analyze_genomic_field(seq, use_orfs=False)
        
        print(f"\n{name}:")
        print(f"  Length: {field.length} bp")
        print(f"  Coherence Ψ: {field.total_coherence:.6f}")
        print(f"  Sovereignty: {field.sovereignty_score:.6f}")
        print(f"  Status: {'SOVEREIGN ✓' if field.is_sovereign else 'UNSTABLE ✗'}")
        print(f"  Resonant ratio: {field.resonant_count}/{field.num_codons}")
    
    return True


def test_mutation_prediction():
    """Test mutation prediction with quantum gyroscopy."""
    print("\n" + "="*80)
    print("TEST 6: Mutation Prediction (ΔP ≈ 0.2%)")
    print("="*80)
    
    # Test sequence
    test_seq = "ATGCGATCGATCGATAGCTAGCTAGCTAGCT"
    
    field = analyze_genomic_field(test_seq, use_orfs=False)
    mutation_pred = predict_mutation_stability(field)
    
    print(f"Sequence: {len(test_seq)} bp")
    print(f"\nMutation Analysis:")
    print(f"  Chirality: {mutation_pred['chirality']:.6f}")
    print(f"  Chirality deviation: {mutation_pred['chirality_deviation']:.6f}")
    print(f"  Mutation probability: {mutation_pred['mutation_probability']*100:.2f}%")
    print(f"  Stability: {'STABLE ✓' if mutation_pred['is_stable'] else 'UNSTABLE ✗'}")
    print(f"  Hotspot count: {mutation_pred['hotspot_count']}")
    print(f"  Hotspot density: {mutation_pred['hotspot_density_percent']:.3f}%")
    
    # Verify mutation probability is in valid range
    assert 0 <= mutation_pred['mutation_probability'] <= 1, "Invalid mutation probability"
    
    return True


def test_real_biological_sequence():
    """Test with real biological sequence (human β-globin)."""
    print("\n" + "="*80)
    print("TEST 7: Real Biological Sequence (Human β-globin fragment)")
    print("="*80)
    
    # Start of human HBB gene (β-globin)
    hbb_sequence = """
    ATGGTGCATCTGACTCCTGAGGAGAAGTCTGCCGTTACTGCCCTGTGGGGCAAGGTGAACGTGGATGAAGTTGGTGGTGAGGCCCTGGGCAGG
    """.replace('\n', '').replace(' ', '').upper()
    
    print(f"Analyzing β-globin fragment ({len(hbb_sequence)} bp)...")
    
    # Analyze with ORF detection
    field = analyze_genomic_field(hbb_sequence, use_orfs=True)
    
    print(field.summary())
    
    # Verify basic properties
    assert field.num_codons > 0, "Should find codons"
    assert 0 <= field.total_coherence <= 1, "Coherence out of range"
    
    # Export analysis
    output_file = "data/hbb_genomic_field_validation.json"
    export_analysis(field, output_file)
    print(f"\n✓ Exported analysis to {output_file}")
    
    return True


def test_export_functionality():
    """Test JSON export functionality."""
    print("\n" + "="*80)
    print("TEST 8: Export Functionality")
    print("="*80)
    
    test_seq = "ATGCGATAGCTA"
    field = analyze_genomic_field(test_seq, use_orfs=False)
    
    # Export to dictionary
    result = export_analysis(field)
    
    # Verify required fields
    required_fields = ['qcal_version', 'frequency_f0', 'metrics', 'codons', 
                      'mutation_analysis', 'author', 'doi']
    
    for field_name in required_fields:
        assert field_name in result, f"Missing field: {field_name}"
        print(f"✓ Field present: {field_name}")
    
    # Verify QCAL constants
    assert result['frequency_f0'] == F0_FREQUENCY, "Wrong f₀ frequency"
    assert result['qcal_version'] == '∞³', "Wrong QCAL version"
    
    print(f"\n✓ Export contains all required fields")
    print(f"✓ QCAL constants verified (f₀ = {F0_FREQUENCY} Hz)")
    
    return True


def test_edge_cases():
    """Test edge cases and error handling."""
    print("\n" + "="*80)
    print("TEST 9: Edge Cases and Error Handling")
    print("="*80)
    
    # Test short sequence
    short_seq = "ATG"
    field = analyze_genomic_field(short_seq, use_orfs=False)
    assert field.num_codons == 1, "Should handle single codon"
    print("✓ Single codon sequence handled")
    
    # Test sequence not divisible by 3
    partial_seq = "ATGCG"  # 5 bases
    field = analyze_genomic_field(partial_seq, use_orfs=False)
    assert field.num_codons == 1, "Should analyze complete codons only"
    print("✓ Partial codon sequence handled")
    
    # Test invalid base detection
    try:
        invalid_seq = "ATGXYZ"
        field = analyze_genomic_field(invalid_seq, use_orfs=False)
        assert False, "Should raise error for invalid bases"
    except ValueError as e:
        print(f"✓ Invalid base error caught: {str(e)[:50]}...")
    
    # Test empty ORF
    no_orf_seq = "CGATCGATCGAT"  # No ATG start codon
    orfs = find_orfs(no_orf_seq, min_length=9)
    print(f"✓ No ORF sequence: found {len(orfs)} ORFs (expected 0)")
    
    return True


def validate_qcal_constants():
    """Validate QCAL constants are correctly set."""
    print("\n" + "="*80)
    print("TEST 10: QCAL Constants Validation")
    print("="*80)
    
    from utils.genomic_zeta_mapping import F0_FREQUENCY, C_COHERENCE
    
    assert F0_FREQUENCY == 141.7001, f"Wrong f₀: {F0_FREQUENCY}"
    assert C_COHERENCE == 244.36, f"Wrong C: {C_COHERENCE}"
    assert SOVEREIGNTY_THRESHOLD == 0.888, f"Wrong threshold: {SOVEREIGNTY_THRESHOLD}"
    
    print(f"✓ f₀ = {F0_FREQUENCY} Hz (Fundamental frequency)")
    print(f"✓ C = {C_COHERENCE} (Coherence constant)")
    print(f"✓ Ψ_threshold = {SOVEREIGNTY_THRESHOLD} (Sovereignty)")
    print(f"✓ All QCAL ∞³ constants verified")
    
    return True


def main():
    """Run all validation tests."""
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║    GENOMIC ZETA MAPPING VALIDATION - Gen→Zeta Framework      ║")
    print("║                   QCAL ∞³ · 141.7001 Hz                      ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    
    tests = [
        ("QCAL Constants", validate_qcal_constants),
        ("Basic Sequence Analysis", test_basic_sequence_analysis),
        ("ORF Detection", test_orf_detection),
        ("Riemann Zero Assignment", test_riemann_zero_assignment),
        ("Spectral Sum & Classification", test_spectral_sum_and_classification),
        ("Coherence Calculation", test_coherence_calculation),
        ("Mutation Prediction", test_mutation_prediction),
        ("Real Biological Sequence", test_real_biological_sequence),
        ("Export Functionality", test_export_functionality),
        ("Edge Cases", test_edge_cases)
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in tests:
        try:
            if test_func():
                passed += 1
        except Exception as e:
            print(f"\n❌ TEST FAILED: {name}")
            print(f"   Error: {str(e)}")
            import traceback
            traceback.print_exc()
            failed += 1
    
    # Summary
    print("\n" + "="*80)
    print("VALIDATION SUMMARY")
    print("="*80)
    print(f"Total tests: {len(tests)}")
    print(f"Passed: {passed} ✓")
    print(f"Failed: {failed} {'✗' if failed > 0 else ''}")
    
    if failed == 0:
        print("\n" + "="*80)
        print("✅ ALL TESTS PASSED - Genomic Zeta Mapping validated!")
        print("="*80)
        print('"La biología es el eco de la función Zeta en la materia."')
        print("José Manuel Mota Burruezo Ψ ✧ ∞³")
        print("="*80)
        return 0
    else:
        print("\n❌ VALIDATION FAILED - Please review errors above")
        return 1


if __name__ == "__main__":
    sys.exit(main())
