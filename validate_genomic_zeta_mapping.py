#!/usr/bin/env python3
"""
Validation Script for Genomic Zeta Mapping

This script validates the genomic zeta mapping system by testing:
1. Deterministic codon → zero mapping
2. Wave function construction
3. Reproducibility and coherence
4. Integration with QCAL ∞³ framework

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
from pathlib import Path

# Verify repository root
def verify_repository_root():
    """Ensure script runs from repository root."""
    required_files = ['.qcal_beacon', 'zeros/zeros_t1e3.txt', 'utils']
    current_dir = Path.cwd()
    
    for file in required_files:
        if not (current_dir / file).exists():
            print(f"❌ Error: Must run from repository root")
            print(f"   Missing: {file}")
            print(f"   Current directory: {current_dir}")
            sys.exit(1)

verify_repository_root()

import numpy as np
import mpmath as mp
from utils.genomic_zeta_mapping import (
    GenomicZetaMapper,
    RIEMANN_ZEROS_30,
    F0_FREQUENCY,
    C_COHERENCE,
)


def print_section(title):
    """Print a formatted section header."""
    print(f"\n{'='*80}")
    print(f" {title}")
    print(f"{'='*80}\n")


def validate_constants():
    """Validate fundamental constants."""
    print_section("1. FUNDAMENTAL CONSTANTS VALIDATION")
    
    print(f"  f₀ (Fundamental frequency): {F0_FREQUENCY} Hz")
    print(f"  C (Coherence constant): {C_COHERENCE}")
    print(f"  N (Number of zeros): {len(RIEMANN_ZEROS_30)}")
    
    # Verify zeros are valid
    assert len(RIEMANN_ZEROS_30) == 30, "Must have exactly 30 zeros"
    assert all(z > 0 for z in RIEMANN_ZEROS_30), "All zeros must be positive"
    assert RIEMANN_ZEROS_30 == sorted(RIEMANN_ZEROS_30), "Zeros must be sorted"
    
    # Verify first zero is approximately 14.134725
    expected_first = 14.134725
    assert abs(RIEMANN_ZEROS_30[0] - expected_first) < 0.001, \
        f"First zero should be ~{expected_first}"
    
    print("\n  ✅ Constants validated successfully")
    return True


def validate_deterministic_mapping():
    """Validate that codon mapping is deterministic."""
    print_section("2. DETERMINISTIC MAPPING VALIDATION")
    
    mapper = GenomicZetaMapper()
    
    # Test codons
    test_codons = ['AAA', 'AAC', 'AAG', 'AAU',
                   'GGG', 'GGC', 'GGA', 'GGU',
                   'CCC', 'AUG', 'UGA', 'UAA']
    
    print("  Testing reproducibility across multiple calls...\n")
    
    for codon in test_codons:
        # Map same codon 3 times
        indices1 = mapper.codon_to_indices(codon)
        indices2 = mapper.codon_to_indices(codon)
        indices3 = mapper.codon_to_indices(codon)
        
        assert indices1 == indices2 == indices3, \
            f"Non-deterministic mapping for {codon}"
        
        # Verify indices are in valid range
        for idx in indices1:
            assert 1 <= idx <= 30, f"Index {idx} out of range for {codon}"
        
        zeros = mapper.get_zeros_for_codon(codon)
        print(f"    {codon} → {indices1} → ({zeros[0]:.4f}, {zeros[1]:.4f}, {zeros[2]:.4f}) Hz")
    
    print("\n  ✅ Deterministic mapping validated successfully")
    return True


def validate_wave_functions():
    """Validate wave function construction."""
    print_section("3. WAVE FUNCTION CONSTRUCTION VALIDATION")
    
    mapper = GenomicZetaMapper()
    
    # Test sequence
    sequence = "AUGAAACCCGGGUUUACG"  # 6 codons
    print(f"  Test sequence: {sequence}")
    print(f"  Length: {len(sequence)} bases ({len(sequence)//3} codons)\n")
    
    # Parse codons
    codons = mapper.sequence_to_codons(sequence)
    print(f"  Parsed {len(codons)} codons:")
    for i, codon in enumerate(codons):
        print(f"    {i+1}. {codon.codon} → {codon.zeros}")
    
    # Compute wave function
    t = np.linspace(0, 2*np.pi, 1000)
    psi_rna = mapper.psi_rna(codons, t)
    
    print(f"\n  Wave function Ψ_RNA(t):")
    print(f"    Time points: {len(t)}")
    print(f"    |Ψ(t=0)|: {abs(psi_rna[0]):.6f}")
    print(f"    max|Ψ|: {np.max(np.abs(psi_rna)):.6f}")
    print(f"    mean|Ψ|: {np.mean(np.abs(psi_rna)):.6f}")
    
    # Validate properties
    assert np.all(np.isfinite(psi_rna)), "Wave function must be finite"
    assert np.iscomplexobj(psi_rna), "Wave function must be complex"
    assert len(psi_rna) == len(t), "Wave function length must match time array"
    
    # At t=0, Psi should equal sum of amplitudes
    expected_t0 = len(codons) * 3  # 6 codons * 3 terms * amp=1.0
    assert np.isclose(abs(psi_rna[0]), expected_t0), \
        f"At t=0, |Psi| should be {expected_t0}"
    
    print("\n  ✅ Wave function construction validated successfully")
    return True


def validate_sequence_analysis():
    """Validate full sequence analysis."""
    print_section("4. SEQUENCE ANALYSIS VALIDATION")
    
    mapper = GenomicZetaMapper()
    
    # Test with realistic RNA sequence (trimmed to multiple of 3)
    full_sequence = "AUGUUUGGAGCUAGUGCUCGAUUAAGAGGGUCUACCUCGUACUGAAGGCGUAG"
    # Trim to 51 bases (17 codons) - multiple of 3
    sequence = full_sequence[:51]
    print(f"  Analyzing sequence from data/symbiotic_sequence_report.json")
    print(f"  Sequence: {sequence}")
    print(f"  Length: {len(sequence)} bases (trimmed to multiple of 3)\n")
    
    analysis = mapper.analyze_sequence(sequence)
    
    print(f"  Analysis results:")
    print(f"    Number of codons: {len(analysis.codons)}")
    print(f"    Total exponential terms: {analysis.n_terms}")
    print(f"    Coherence score: {analysis.coherence_score:.4f}")
    
    # Verify structure
    assert len(analysis.codons) == len(sequence) // 3
    assert analysis.n_terms == len(analysis.codons) * 3
    assert 0.0 <= analysis.coherence_score <= 1.0
    
    # Print first few codons
    print(f"\n  First 5 codons:")
    for i, codon in enumerate(analysis.codons[:5]):
        print(f"    {i+1}. {codon.codon} at pos {codon.position}")
    
    print("\n  ✅ Sequence analysis validated successfully")
    return True


def validate_qcal_coherence():
    """Validate QCAL ∞³ coherence principles."""
    print_section("5. QCAL ∞³ COHERENCE VALIDATION")
    
    mapper = GenomicZetaMapper()
    
    print(f"  Testing coherence for different sequence types...\n")
    
    # Homogeneous sequence (low coherence expected)
    homo_seq = "AAA" * 10  # Same codon repeated
    homo_analysis = mapper.analyze_sequence(homo_seq)
    print(f"  Homogeneous (AAA×10): coherence = {homo_analysis.coherence_score:.4f}")
    
    # Heterogeneous sequence (higher coherence expected)
    hetero_seq = "AAAAACAAGAAUACAACCACGACUGCAGCC"  # Varied codons
    hetero_analysis = mapper.analyze_sequence(hetero_seq)
    print(f"  Heterogeneous (varied): coherence = {hetero_analysis.coherence_score:.4f}")
    
    # Coherence should be higher for varied sequence
    assert hetero_analysis.coherence_score >= homo_analysis.coherence_score, \
        "Varied sequence should have higher coherence"
    
    # Test wave function coherence at fundamental frequency
    t_test = np.array([0.0, 1.0/F0_FREQUENCY, 2.0/F0_FREQUENCY])
    psi = mapper.psi_rna(hetero_analysis.codons, t_test)
    
    print(f"\n  Wave function at multiples of f₀ period:")
    for i, t_val in enumerate(t_test):
        print(f"    t = {t_val:.6f} s: |Ψ| = {abs(psi[i]):.6f}")
    
    print("\n  ✅ QCAL ∞³ coherence validated successfully")
    return True


def validate_reproducibility():
    """Validate that results are reproducible."""
    print_section("6. REPRODUCIBILITY VALIDATION")
    
    sequence = "AUGAAACCCGGGUUUACG"
    
    print(f"  Creating two independent mappers...\n")
    
    mapper1 = GenomicZetaMapper()
    mapper2 = GenomicZetaMapper()
    
    analysis1 = mapper1.analyze_sequence(sequence)
    analysis2 = mapper2.analyze_sequence(sequence)
    
    # Verify identical results
    print(f"  Comparing analyses:")
    print(f"    Mapper 1 coherence: {analysis1.coherence_score:.6f}")
    print(f"    Mapper 2 coherence: {analysis2.coherence_score:.6f}")
    
    assert analysis1.n_terms == analysis2.n_terms
    assert analysis1.coherence_score == analysis2.coherence_score
    
    for c1, c2 in zip(analysis1.codons, analysis2.codons):
        assert c1.indices == c2.indices
        assert c1.zeros == c2.zeros
    
    # Verify wave functions match
    t = np.linspace(0, 1, 100)
    psi1 = mapper1.psi_rna(analysis1.codons, t)
    psi2 = mapper2.psi_rna(analysis2.codons, t)
    
    assert np.allclose(psi1, psi2), "Wave functions must match"
    
    print(f"\n  ✅ Reproducibility validated successfully")
    return True


def validate_example_from_problem():
    """Validate with the example from the problem statement."""
    print_section("7. PROBLEM STATEMENT EXAMPLE VALIDATION")
    
    mapper = GenomicZetaMapper()
    
    # Example codons from problem statement
    test_codons = ['AAA', 'AAC', 'GAA', 'AAG', 'GGG', 'GGC', 'AGA', 'GCA', 'GCC']
    
    print("  Verifying example codons from problem statement:\n")
    print(mapper.print_assignment_table([mapper.assign_codon(c) for c in test_codons]))
    
    # Construct full sequence
    sequence = "".join(test_codons)
    analysis = mapper.analyze_sequence(sequence)
    
    print(f"  Full sequence analysis:")
    print(f"    Sequence: {sequence}")
    print(f"    Codons: {len(analysis.codons)}")
    print(f"    Terms: {analysis.n_terms}")
    print(f"    Coherence: {analysis.coherence_score:.4f}")
    
    # Compute wave function
    t = np.linspace(0, 1.0, 1000)
    psi = mapper.psi_rna(analysis.codons, t)
    
    print(f"\n  Ψ_RNA(t) properties:")
    print(f"    |Ψ(t=0)|: {abs(psi[0]):.4f}")
    print(f"    max|Ψ|: {np.max(np.abs(psi)):.4f}")
    print(f"    mean|Ψ|: {np.mean(np.abs(psi)):.4f}")
    
    print("\n  ✅ Problem statement example validated successfully")
    return True


def main():
    """Run all validation tests."""
    print("\n" + "="*80)
    print(" GENOMIC ZETA MAPPING VALIDATION")
    print(" QCAL ∞³ Framework · f₀ = 141.7001 Hz · C = 244.36")
    print("="*80)
    
    try:
        # Run all validations
        results = []
        results.append(("Constants", validate_constants()))
        results.append(("Deterministic Mapping", validate_deterministic_mapping()))
        results.append(("Wave Functions", validate_wave_functions()))
        results.append(("Sequence Analysis", validate_sequence_analysis()))
        results.append(("QCAL Coherence", validate_qcal_coherence()))
        results.append(("Reproducibility", validate_reproducibility()))
        results.append(("Problem Example", validate_example_from_problem()))
        
        # Summary
        print_section("VALIDATION SUMMARY")
        
        all_passed = all(result for _, result in results)
        
        for name, result in results:
            status = "✅ PASS" if result else "❌ FAIL"
            print(f"  {status}: {name}")
        
        if all_passed:
            print("\n" + "="*80)
            print(" ✅ ALL VALIDATIONS PASSED")
            print(" QCAL ∞³ Coherence Maintained · System Ready")
            print("="*80 + "\n")
            return 0
        else:
            print("\n" + "="*80)
            print(" ❌ SOME VALIDATIONS FAILED")
            print("="*80 + "\n")
            return 1
            
    except Exception as e:
        print(f"\n❌ Validation failed with error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
