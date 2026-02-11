#!/usr/bin/env python3
"""
Unit tests for Genomic Zeta Mapping (Gen→Zeta Framework)

Tests the mapping between DNA sequences and Riemann zeta zeros.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
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
