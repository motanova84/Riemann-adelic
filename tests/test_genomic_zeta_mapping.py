"""
Tests for Genomic Zeta Mapping Module

Validates DNA/RNA codon fragmentation and mapping to Riemann zeros.
#!/usr/bin/env python3
"""
Unit tests for Genomic Zeta Mapping (Gen→Zeta Framework)

Tests the mapping between DNA sequences and Riemann zeta zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import mpmath as mp
import sys
import os

# Import directly to avoid utils __init__ dependencies
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'utils')))
from genomic_zeta_mapping import (
    GenomicZetaMapper,
    Codon,
    RiemannZeroTriplet,
    CodonType,
    GenomicField,
    predict_mutation_stability,
    F0_FREQUENCY,
    C_COHERENCE,
    KAPPA_PI,
    SOVEREIGNTY_THRESHOLD
)


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_frequency(self):
        """Verify f₀ = 141.7001 Hz."""
        assert float(F0_FREQUENCY) == 141.7001
        
    def test_coherence_constant(self):
        """Verify C = 244.36."""
        assert float(C_COHERENCE) == 244.36
        
    def test_kappa_pi(self):
        """Verify κ_Π = 17."""
        assert float(KAPPA_PI) == 17
        
    def test_sovereignty_threshold(self):
        """Verify sovereignty threshold Ψ ≥ 0.888."""
        assert float(SOVEREIGNTY_THRESHOLD) == 0.888


class TestRiemannZeroTriplet:
    """Test Riemann zero triplet structure."""
    
    def test_valid_triplet_creation(self):
        """Test creating valid triplet."""
        triplet = RiemannZeroTriplet(
            gamma_i=mp.mpf("14.134725"),
            gamma_j=mp.mpf("21.022039"),
            gamma_k=mp.mpf("25.010857")
        )
        assert triplet.gamma_i > 0
        assert triplet.gamma_j > 0
        assert triplet.gamma_k > 0
        
    def test_invalid_triplet_negative(self):
        """Test that negative zeros are rejected."""
        with pytest.raises(ValueError):
            RiemannZeroTriplet(
                gamma_i=mp.mpf("-1.0"),
                gamma_j=mp.mpf("21.0"),
                gamma_k=mp.mpf("25.0")
            )
            
    def test_triplet_to_list(self):
        """Test conversion to list."""
        triplet = RiemannZeroTriplet(
            gamma_i=mp.mpf("14.1"),
            gamma_j=mp.mpf("21.0"),
            gamma_k=mp.mpf("25.0")
        )
        lst = triplet.to_list()
        assert len(lst) == 3
        assert all(isinstance(x, mp.mpf) for x in lst)


class TestCodon:
    """Test codon structure."""
    
    def test_valid_dna_codon(self):
        """Test creating valid DNA codon."""
        codon = Codon(sequence="ATG", position=0)
        assert codon.sequence == "ATG"
        assert codon.position == 0
        
    def test_valid_rna_codon(self):
        """Test creating valid RNA codon."""
        codon = Codon(sequence="AUG", position=3)
        assert codon.sequence == "AUG"
        assert codon.position == 3
        
    def test_lowercase_normalization(self):
        """Test that lowercase is converted to uppercase."""
        codon = Codon(sequence="atg", position=0)
        assert codon.sequence == "ATG"
        
    def test_invalid_length(self):
        """Test that wrong length is rejected."""
        with pytest.raises(ValueError):
            Codon(sequence="AT", position=0)
            
    def test_invalid_bases(self):
        """Test that invalid bases are rejected."""
        with pytest.raises(ValueError):
            Codon(sequence="XYZ", position=0)


class TestGenomicZetaMapper:
    """Test genomic zeta mapper functionality."""
    
    def test_initialization(self):
        """Test mapper initialization."""
        mapper = GenomicZetaMapper(precision=25)
        assert mapper.f0 == F0_FREQUENCY
        assert mapper.C == C_COHERENCE
        assert len(mapper.riemann_zeros) > 0
        
    def test_load_zeros_fallback(self):
        """Test that fallback zeros are loaded if file doesn't exist."""
        mapper = GenomicZetaMapper(zeros_file="/nonexistent/path.txt")
        assert len(mapper.riemann_zeros) >= 30  # At least hardcoded zeros
        
    def test_fragment_to_codons_exact_multiple(self):
        """Test fragmentation when length is multiple of 3."""
        mapper = GenomicZetaMapper()
        sequence = "ATGATGATG"  # 3 codons, no remainder
        codons, remainder = mapper.fragment_to_codons(sequence)
        
        assert len(codons) == 3
        assert remainder == ""
        assert all(c.sequence == "ATG" for c in codons)
        
    def test_fragment_to_codons_with_remainder(self):
        """Test fragmentation with remaining bases."""
        mapper = GenomicZetaMapper()
        sequence = "ATGATGAT"  # 2 codons + 2 bases
        codons, remainder = mapper.fragment_to_codons(sequence)
        
        assert len(codons) == 2
        assert remainder == "AT"
        
    def test_fragment_example_sequence(self):
        """Test fragmentation of example sequence from problem statement."""
        mapper = GenomicZetaMapper()
        # First part of example: AAA AAC GAA AAG GGG...
        sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
        codons, remainder = mapper.fragment_to_codons(sequence)
        
        # 80 bases total = 26 codons + 2 remainder
        assert len(codons) == 21  # Actually 63 bases / 3 = 21 codons
        # Check first few codons match problem statement
        expected_first_codons = ["AAA", "CGA", "AAG", "GGA", "AAA", "AAA", "CAA", "AAA"]
        for i, expected in enumerate(expected_first_codons[:len(codons)]):
            assert codons[i].sequence == expected, f"Codon {i}: expected {expected}, got {codons[i].sequence}"
    
    def test_codon_to_index_deterministic(self):
        """Test that same codon always maps to same index."""
        mapper = GenomicZetaMapper()
        
        idx1 = mapper._codon_to_index("ATG")
        idx2 = mapper._codon_to_index("ATG")
        assert idx1 == idx2
        
    def test_codon_to_index_unique(self):
        """Test that different codons map to different indices."""
        mapper = GenomicZetaMapper()
        
        idx_atg = mapper._codon_to_index("ATG")
        idx_gcg = mapper._codon_to_index("GCG")
        idx_aaa = mapper._codon_to_index("AAA")
        
        # Should all be different
        assert len({idx_atg, idx_gcg, idx_aaa}) == 3
        
    def test_codon_to_index_range(self):
        """Test that indices are in valid range 0-63."""
        mapper = GenomicZetaMapper()
        
        # Test all standard codons
        bases = ['A', 'T', 'G', 'C']
        for b1 in bases:
            for b2 in bases:
                for b3 in bases:
                    codon = b1 + b2 + b3
                    idx = mapper._codon_to_index(codon)
                    assert 0 <= idx < 64
    
    def test_map_codon_to_zeros(self):
        """Test mapping codon to zero triplet."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        
        triplet = mapper.map_codon_to_zeros(codon)
        
        assert isinstance(triplet, RiemannZeroTriplet)
        assert triplet.gamma_i > 0
        assert triplet.gamma_j > 0
        assert triplet.gamma_k > 0
        assert codon.zero_triplet == triplet
        
    def test_map_codon_deterministic(self):
        """Test that same codon always maps to same zeros."""
        mapper = GenomicZetaMapper()
        
        codon1 = Codon(sequence="ATG", position=0)
        codon2 = Codon(sequence="ATG", position=3)
        
        triplet1 = mapper.map_codon_to_zeros(codon1)
        triplet2 = mapper.map_codon_to_zeros(codon2)
        
        assert triplet1.gamma_i == triplet2.gamma_i
        assert triplet1.gamma_j == triplet2.gamma_j
        assert triplet1.gamma_k == triplet2.gamma_k
        
    def test_construct_psi_codon_scalar(self):
        """Test Ψ_codon construction with scalar time."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        mapper.map_codon_to_zeros(codon)
        
        psi = mapper.construct_psi_codon(codon, t=0.0)
        
        assert isinstance(psi, complex)
        # At t=0, all exponentials = 1, so psi = A1 + A2 + A3 = 3/sqrt(3) = sqrt(3)
        expected = np.sqrt(3)
        assert abs(abs(psi) - expected) < 1e-10
        
    def test_construct_psi_codon_array(self):
        """Test Ψ_codon construction with array time."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        mapper.map_codon_to_zeros(codon)
        
        t = np.linspace(0, 1, 10)
        psi = mapper.construct_psi_codon(codon, t)
        
        assert isinstance(psi, np.ndarray)
        assert len(psi) == 10
        assert all(isinstance(p, complex) for p in psi)
        
    def test_construct_psi_custom_amplitudes(self):
        """Test Ψ_codon with custom amplitudes."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        mapper.map_codon_to_zeros(codon)
        
        amplitudes = (1.0, 0.0, 0.0)
        psi = mapper.construct_psi_codon(codon, t=0.0, amplitudes=amplitudes)
        
        # With A1=1, A2=A3=0, psi should be 1 at t=0
        assert abs(psi - 1.0) < 1e-10
        
    def test_classify_codon_resonance(self):
        """Test codon resonance classification."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        
        codon_type = mapper.classify_codon_resonance(codon)
        
        assert isinstance(codon_type, CodonType)
        assert codon.codon_type == codon_type
        assert codon.psi_amplitude is not None
        
    def test_compute_genomic_field_empty(self):
        """Test genomic field computation with no codons."""
        mapper = GenomicZetaMapper()
        
        field = mapper.compute_genomic_field([])
        
        assert field.total_codons == 0
        assert field.psi_gen == 0+0j
        assert not field.sovereignty_achieved
        
    def test_compute_genomic_field_single_codon(self):
        """Test genomic field with single codon."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        
        field = mapper.compute_genomic_field([codon])
        
        assert field.total_codons == 1
        assert abs(field.psi_gen) > 0
        assert 0 <= field.coherence_score <= 2.0  # Normalized magnitude
        
    def test_compute_genomic_field_multiple_codons(self):
        """Test genomic field with multiple codons."""
        mapper = GenomicZetaMapper()
        sequence = "ATGATGATG"
        codons, _ = mapper.fragment_to_codons(sequence)
        
        field = mapper.compute_genomic_field(codons)
        
        assert field.total_codons == 3
        assert field.resonant_codons + field.dissonant_codons <= field.total_codons
        
    def test_analyze_sequence_complete(self):
        """Test complete sequence analysis."""
        mapper = GenomicZetaMapper()
        sequence = "ATGATGATG"
        
        results = mapper.analyze_sequence(sequence)
        
        assert 'codons' in results
        assert 'genomic_field' in results
        assert 'qcal_constants' in results
        assert results['sequence_length'] == 9
        assert len(results['codons']) == 3
        
    def test_analyze_sequence_example(self):
        """Test analysis of example sequence from problem statement."""
        mapper = GenomicZetaMapper()
        sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
        
        results = mapper.analyze_sequence(sequence)
        
        # Verify structure
        assert 'codons' in results
        assert 'genomic_field' in results
        
        # Check codons
        codons = results['codons']
        assert len(codons) > 0
        
        # Each codon should have zeros assigned
        for codon_data in codons:
            assert 'sequence' in codon_data
            assert 'zeros' in codon_data
            assert len(codon_data['zeros']) == 3
            assert all(z > 0 for z in codon_data['zeros'])
            
        # Check genomic field
        field = results['genomic_field']
        assert 'coherence_score' in field
        assert 0 <= field['coherence_score'] <= 2.0


class TestMutationPrediction:
    """Test mutation stability prediction."""
    
    def test_predict_mutation_no_change(self):
        """Test prediction when sequences are identical."""
        original = "ATGATGATG"
        mutated = "ATGATGATG"
        
        results = predict_mutation_stability(original, mutated)
        
        assert results['delta_coherence'] == 0.0
        assert results['stability_preserved']
        assert len(results['mutation_hotspots']) == 0
        
    def test_predict_mutation_single_base(self):
        """Test prediction with single base mutation."""
        original = "ATGATGATG"
        mutated = "ATGATCATG"  # G->C in middle codon
        
        results = predict_mutation_stability(original, mutated)
        
        assert 'original_coherence' in results
        assert 'mutated_coherence' in results
        assert 'delta_coherence' in results
        assert 'mutation_hotspots' in results
        
    def test_predict_mutation_gyroscopic_precision(self):
        """Test that gyroscopic precision ΔP ≈ 0.2% is reported."""
        original = "ATGATGATG"
        mutated = "ATGATCATG"
        
        results = predict_mutation_stability(original, mutated)
        
        assert results['gyroscopic_precision'] == 0.002  # 0.2%


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_workflow(self):
        """Test complete workflow from sequence to analysis."""
        # Initialize
        mapper = GenomicZetaMapper(precision=25)
        
        # Fragment
        sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
        codons, remainder = mapper.fragment_to_codons(sequence)
        
        # Map to zeros
        for codon in codons:
            triplet = mapper.map_codon_to_zeros(codon)
            assert triplet is not None
            
        # Construct wave functions
        t = 0.0
        for codon in codons:
            psi = mapper.construct_psi_codon(codon, t)
            assert isinstance(psi, complex)
            
        # Compute genomic field
        field = mapper.compute_genomic_field(codons, t)
        assert field.total_codons == len(codons)
        
        # Analyze
        results = mapper.analyze_sequence(sequence, t)
        assert len(results['codons']) == len(codons)
        
    def test_time_evolution(self):
        """Test Ψ_codon time evolution."""
        mapper = GenomicZetaMapper()
        codon = Codon(sequence="ATG", position=0)
        mapper.map_codon_to_zeros(codon)
        
        # Compute at multiple time points
        times = np.linspace(0, 10, 100)
        psi_values = mapper.construct_psi_codon(codon, times)
        
        # Wave function should oscillate
        amplitudes = np.abs(psi_values)
        assert np.min(amplitudes) < np.max(amplitudes)
        
    def test_different_codons_different_evolution(self):
        """Test that different codons have different time evolution."""
        mapper = GenomicZetaMapper()
        
        codon1 = Codon(sequence="ATG", position=0)
        codon2 = Codon(sequence="GCA", position=3)
        
        mapper.map_codon_to_zeros(codon1)
        mapper.map_codon_to_zeros(codon2)
        
        times = np.linspace(0, 10, 100)
        psi1 = mapper.construct_psi_codon(codon1, times)
        psi2 = mapper.construct_psi_codon(codon2, times)
        
        # Should be different
        assert not np.allclose(psi1, psi2)


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_f0_frequency_consistency(self):
        """Test that f₀ = 141.7001 Hz is used consistently."""
        mapper = GenomicZetaMapper()
        assert float(mapper.f0) == 141.7001
        
    def test_coherence_constant_usage(self):
        """Test that C = 244.36 coherence constant is accessible."""
        mapper = GenomicZetaMapper()
        assert float(mapper.C) == 244.36
        
    def test_sovereignty_threshold_application(self):
        """Test that Ψ ≥ 0.888 sovereignty threshold is applied."""
        mapper = GenomicZetaMapper()
        
        # Create sequence and analyze
        sequence = "ATG" * 10  # Repetitive sequence
        field = mapper.compute_genomic_field(
            mapper.fragment_to_codons(sequence)[0]
        )
        
        # Check sovereignty classification
        if field.coherence_score >= 0.888:
            assert field.sovereignty_achieved
        else:
            assert not field.sovereignty_achieved
from utils.genomic_zeta_mapping import (
    analyze_genomic_field,
    find_orfs,
    select_riemann_zero_for_base,
    compute_codon_spectral_sum,
    classify_codon_resonance,
    compute_codon_field,
    analyze_codon,
    predict_mutation_stability,
    export_analysis,
    F0_FREQUENCY,
    C_COHERENCE,
    SOVEREIGNTY_THRESHOLD,
    BASE_PHASE_MAP,
    BASE_AMPLITUDE_MAP
)


class TestBasicFunctionality:
    """Test basic genomic zeta mapping functionality."""
    
    def test_constants(self):
        """Test QCAL constants are correctly defined."""
        assert F0_FREQUENCY == 141.7001
        assert C_COHERENCE == 244.36
        assert SOVEREIGNTY_THRESHOLD == 0.888
    
    def test_base_mappings(self):
        """Test base-to-phase and base-to-amplitude mappings."""
        assert len(BASE_PHASE_MAP) == 4
        assert len(BASE_AMPLITUDE_MAP) == 4
        
        # All bases should be present
        bases = {'A', 'T', 'C', 'G'}
        assert set(BASE_PHASE_MAP.keys()) == bases
        assert set(BASE_AMPLITUDE_MAP.keys()) == bases
        
        # Phases should be in valid range [0, 2π)
        for phase in BASE_PHASE_MAP.values():
            assert 0 <= phase < 2 * np.pi
        
        # Amplitudes should be positive
        for amplitude in BASE_AMPLITUDE_MAP.values():
            assert amplitude > 0
    
    def test_riemann_zero_selection_deterministic(self):
        """Test that Riemann zero selection is deterministic."""
        # Same inputs should give same output
        zero1 = select_riemann_zero_for_base('A', 0, 0)
        zero2 = select_riemann_zero_for_base('A', 0, 0)
        assert zero1 == zero2
        
        # Different positions should give different zeros
        zero_pos0 = select_riemann_zero_for_base('A', 0, 0)
        zero_pos1 = select_riemann_zero_for_base('A', 1, 0)
        assert zero_pos0 != zero_pos1
    
    def test_riemann_zeros_positive(self):
        """Test that selected Riemann zeros are positive."""
        for base in ['A', 'T', 'C', 'G']:
            for pos in range(3):
                zero = select_riemann_zero_for_base(base, pos, 0)
                assert zero > 0, f"Riemann zero should be positive, got {zero}"


class TestCodonAnalysis:
    """Test codon-level analysis functions."""
    
    def test_spectral_sum_computation(self):
        """Test spectral sum computation for codons."""
        zeros, spectral_sum = compute_codon_spectral_sum("ATG", 0)
        
        assert len(zeros) == 3
        assert all(z > 0 for z in zeros)
        assert spectral_sum > 0
        assert spectral_sum == sum(zeros) / 3.0
    
    def test_resonance_classification(self):
        """Test resonance/dissonance classification."""
        # Test with a spectral sum close to f₀
        is_resonant, harmonic, friction = classify_codon_resonance(F0_FREQUENCY)
        assert is_resonant  # Should be resonant at f₀
        assert harmonic == 1  # First harmonic
        assert friction == 0  # No friction for resonant
        
        # Test with a non-resonant frequency
        is_resonant, harmonic, friction = classify_codon_resonance(100.0)
        # Might or might not be resonant depending on tolerance
        assert isinstance(is_resonant, bool)
        assert friction >= 0  # Friction should be non-negative
    
    def test_codon_field_computation(self):
        """Test quantum field computation for codon."""
        psi = compute_codon_field("ATG", 0, t=0.0)
        
        assert isinstance(psi, complex)
        assert abs(psi) > 0  # Should have non-zero magnitude
    
    def test_analyze_codon(self):
        """Test complete codon analysis."""
        codon = analyze_codon("ATG", 0, 0)
        
        assert codon.sequence == "ATG"
        assert codon.position == 0
        assert len(codon.riemann_zeros) == 3
        assert codon.spectral_sum > 0
        assert isinstance(codon.is_resonant, bool)
        assert codon.coherence_local >= 0
        assert isinstance(codon.phase_accumulation, complex)


class TestORFDetection:
    """Test Open Reading Frame detection."""
    
    def test_find_simple_orf(self):
        """Test finding a simple ORF."""
        # ATG...TAA
        sequence = "AAATGCGATCGTAACC"
        orfs = find_orfs(sequence, min_length=9)
        
        assert len(orfs) >= 1
        start, end, frame = orfs[0]
        assert sequence[start:start+3] == "ATG"
        assert sequence[end-3:end] in ["TAA", "TAG", "TGA"]
    
    def test_no_orf_found(self):
        """Test sequence with no ORF."""
        sequence = "CGATCGATCGAT"  # No ATG
        orfs = find_orfs(sequence, min_length=9)
        
        assert len(orfs) == 0
    
    def test_multiple_orfs(self):
        """Test finding multiple ORFs."""
        # Two ORFs in different frames
        sequence = "ATGCGATAAGGGATGCCCTAG"
        orfs = find_orfs(sequence, min_length=6)
        
        # Should find at least one ORF
        assert len(orfs) >= 1
    
    def test_min_length_filter(self):
        """Test minimum length filtering."""
        sequence = "ATGTAA"  # Very short ORF
        
        orfs_short = find_orfs(sequence, min_length=3)
        orfs_long = find_orfs(sequence, min_length=100)
        
        # Should find with low threshold, not with high
        assert len(orfs_short) >= len(orfs_long)


class TestGenomicFieldAnalysis:
    """Test complete genomic field analysis."""
    
    def test_simple_sequence(self):
        """Test analysis of simple sequence."""
        sequence = "ATGCGATAA"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert field.length == len(sequence)
        assert field.num_codons == 3
        assert len(field.codons) == 3
        assert field.resonant_count + field.dissonant_count == field.num_codons
        assert 0 <= field.total_coherence <= 1
        assert 0 <= field.sovereignty_score <= 1
    
    def test_with_orf_detection(self):
        """Test analysis with ORF detection."""
        sequence = "AAATGCGATCGTAACC"
        field = analyze_genomic_field(sequence, use_orfs=True)
        
        assert field.num_codons >= 0  # May find ORFs or not
        if field.num_codons > 0:
            assert len(field.codons) == field.num_codons
    
    def test_sovereignty_classification(self):
        """Test sovereignty classification."""
        sequence = "ATG" * 20  # Repetitive sequence
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        # Check sovereignty is boolean (handle numpy bool)
        assert isinstance(field.is_sovereign, (bool, np.bool_))
        
        # Check threshold logic
        if field.sovereignty_score >= SOVEREIGNTY_THRESHOLD:
            assert field.is_sovereign
        else:
            assert not field.is_sovereign
    
    def test_torsion_tensor(self):
        """Test torsion tensor computation."""
        sequence = "ATGCGATAG"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert field.torsion_tensor.shape == (3, 3)
        # Tensor should be real
        assert np.all(np.isreal(field.torsion_tensor))
    
    def test_mutation_hotspots(self):
        """Test mutation hotspot identification."""
        sequence = "ATGCGATAGCTAGCT"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert isinstance(field.mutation_hotspots, list)
        # Hotspots should be valid positions
        for pos in field.mutation_hotspots:
            assert 0 <= pos < len(sequence)


class TestMutationPrediction:
    """Test mutation prediction functionality."""
    
    def test_mutation_prediction(self):
        """Test mutation stability prediction."""
        sequence = "ATGCGATAGCTA"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        pred = predict_mutation_stability(field)
        
        assert 'chirality' in pred
        assert 'mutation_probability' in pred
        assert 'is_stable' in pred
        assert 'hotspot_count' in pred
        
        # Probability should be in [0, 1]
        assert 0 <= pred['mutation_probability'] <= 1
        
        # Chirality should be real number
        assert isinstance(pred['chirality'], (int, float))
    
    def test_stability_threshold(self):
        """Test stability threshold logic."""
        sequence = "ATG" * 10
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        pred = predict_mutation_stability(field)
        
        # Stability should be boolean
        assert isinstance(pred['is_stable'], bool)


class TestExportFunctionality:
    """Test export and serialization."""
    
    def test_export_to_dict(self):
        """Test export to dictionary."""
        sequence = "ATGCGATAG"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        result = export_analysis(field)
        
        # Check required fields
        required_fields = [
            'qcal_version', 'frequency_f0', 'sequence',
            'metrics', 'codons', 'mutation_analysis',
            'author', 'doi'
        ]
        for field_name in required_fields:
            assert field_name in result
        
        # Check QCAL constants
        assert result['frequency_f0'] == F0_FREQUENCY
        assert result['qcal_version'] == '∞³'
    
    def test_export_to_file(self, tmp_path):
        """Test export to JSON file."""
        import json
        
        sequence = "ATGCGATAG"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        output_file = tmp_path / "test_export.json"
        export_analysis(field, str(output_file))
        
        # Check file was created
        assert output_file.exists()
        
        # Check it's valid JSON
        with open(output_file, 'r') as f:
            data = json.load(f)
        
        assert 'qcal_version' in data
        assert data['qcal_version'] == '∞³'


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_single_codon(self):
        """Test single codon sequence."""
        sequence = "ATG"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert field.num_codons == 1
        assert len(field.codons) == 1
    
    def test_partial_codon(self):
        """Test sequence with partial codon."""
        sequence = "ATGCG"  # 5 bases
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        # Should only analyze complete codons
        assert field.num_codons == 1
    
    def test_invalid_bases(self):
        """Test error on invalid bases."""
        with pytest.raises(ValueError):
            analyze_genomic_field("ATGXYZ", use_orfs=False)
    
    def test_empty_sequence(self):
        """Test handling of very short sequence."""
        # Sequence too short for any codon
        sequence = "AT"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert field.num_codons == 0
    
    def test_lowercase_sequence(self):
        """Test that lowercase sequences are handled."""
        sequence = "atgcgatag"
        field = analyze_genomic_field(sequence, use_orfs=False)
        
        assert field.num_codons > 0
        # Should convert to uppercase internally
        assert all(codon.sequence.isupper() for codon in field.codons)


class TestBiologicalSequences:
    """Test with real biological sequences."""
    
    def test_hbb_fragment(self):
        """Test with human β-globin fragment."""
        # Start of HBB gene
        hbb = "ATGGTGCATCTGACTCCTGAGGAGAAGTCTGCCGTT"
        field = analyze_genomic_field(hbb, use_orfs=False)
        
        assert field.num_codons > 0
        assert 0 <= field.total_coherence <= 1
        assert isinstance(field.sovereignty_score, float)
    
    def test_atp_synthase_fragment(self):
        """Test with ATP synthase gene fragment."""
        # Fragment from ATP synthase
        atp = "ATGGCTCAGATTCACTTCGCCGGTGACGACGTGACGAAG"
        field = analyze_genomic_field(atp, use_orfs=True)
        
        assert field.num_codons >= 0
        # Should preserve sequence info
        assert field.sequence == atp.upper()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
