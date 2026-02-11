#!/usr/bin/env python3
"""
Tests for Genomic Zeta Mapping Module

Tests the deterministic mapping of RNA/DNA codons to Riemann zeros
and the construction of coherent wave functions.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
from utils.genomic_zeta_mapping import (
    GenomicZetaMapper,
    CodonZetaAssignment,
    RNAZetaWaveFunction,
    RIEMANN_ZEROS_30,
    F0_FREQUENCY,
)


class TestGenomicZetaMapper:
    """Test suite for GenomicZetaMapper class."""
    
    def test_initialization(self):
        """Test mapper initialization."""
        mapper = GenomicZetaMapper()
        assert mapper.f0 == F0_FREQUENCY
        assert len(mapper.zeros) == 30
        assert mapper.n_zeros >= 30
    
    def test_custom_zeros(self):
        """Test initialization with custom zeros."""
        custom_zeros = list(range(10, 40))  # 30 zeros
        mapper = GenomicZetaMapper(zeros=custom_zeros)
        assert mapper.zeros == custom_zeros
        assert mapper.n_zeros == 30
    
    def test_insufficient_zeros(self):
        """Test that insufficient zeros raises error."""
        with pytest.raises(ValueError, match="At least 30 Riemann zeros required"):
            GenomicZetaMapper(zeros=list(range(20)))
    
    def test_codon_to_indices_deterministic(self):
        """Test that codon mapping is deterministic."""
        mapper = GenomicZetaMapper()
        
        # Same codon should always give same indices
        indices1 = mapper.codon_to_indices("AAA")
        indices2 = mapper.codon_to_indices("AAA")
        assert indices1 == indices2
        
        # Different codons should (usually) give different indices
        indices_aaa = mapper.codon_to_indices("AAA")
        indices_ggg = mapper.codon_to_indices("GGG")
        # Not strictly required, but likely for these specific codons
        assert indices_aaa != indices_ggg
    
    def test_codon_to_indices_valid_range(self):
        """Test that indices are in valid range [1, 30]."""
        mapper = GenomicZetaMapper()
        
        test_codons = ["AAA", "AAC", "AAG", "AAU",
                       "ACA", "ACC", "ACG", "ACU",
                       "GGG", "GGC", "CCC", "UUU"]
        
        for codon in test_codons:
            indices = mapper.codon_to_indices(codon)
            assert len(indices) == 3
            for idx in indices:
                assert 1 <= idx <= 30, f"Index {idx} out of range for codon {codon}"
    
    def test_codon_validation(self):
        """Test that invalid codons are rejected."""
        mapper = GenomicZetaMapper()
        
        # Wrong length
        with pytest.raises(ValueError, match="must be 3 bases"):
            mapper.codon_to_indices("AA")
        
        with pytest.raises(ValueError, match="must be 3 bases"):
            mapper.codon_to_indices("AAAA")
        
        # Invalid bases
        with pytest.raises(ValueError):
            mapper.assign_codon("AXC")
    
    def test_get_zeros_for_codon(self):
        """Test retrieving zeros for a codon."""
        mapper = GenomicZetaMapper()
        
        zeros = mapper.get_zeros_for_codon("AAA")
        assert len(zeros) == 3
        assert all(isinstance(z, float) for z in zeros)
        # All zeros should be from the first 30
        for z in zeros:
            assert z in RIEMANN_ZEROS_30
    
    def test_assign_codon(self):
        """Test creating a codon assignment."""
        mapper = GenomicZetaMapper()
        
        assignment = mapper.assign_codon("AAA", position=0)
        
        assert isinstance(assignment, CodonZetaAssignment)
        assert assignment.codon == "AAA"
        assert assignment.position == 0
        assert len(assignment.indices) == 3
        assert len(assignment.zeros) == 3
        assert len(assignment.amplitudes) == 3
        assert all(a == 1.0 for a in assignment.amplitudes)
    
    def test_assign_codon_custom_amplitudes(self):
        """Test codon assignment with custom amplitudes."""
        mapper = GenomicZetaMapper()
        
        custom_amps = (0.5, 1.0, 1.5)
        assignment = mapper.assign_codon("GGG", amplitudes=custom_amps)
        
        assert assignment.amplitudes == custom_amps
    
    def test_sequence_to_codons(self):
        """Test parsing a sequence into codons."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAACGAA"  # 3 codons
        codons = mapper.sequence_to_codons(sequence)
        
        assert len(codons) == 3
        assert codons[0].codon == "AAA"
        assert codons[1].codon == "AAC"
        assert codons[2].codon == "GAA"
        assert codons[0].position == 0
        assert codons[1].position == 1
        assert codons[2].position == 2
    
    def test_sequence_invalid_length(self):
        """Test that sequences with invalid length are rejected."""
        mapper = GenomicZetaMapper()
        
        with pytest.raises(ValueError, match="multiple of 3"):
            mapper.sequence_to_codons("AAAA")  # 4 bases
        
        with pytest.raises(ValueError, match="multiple of 3"):
            mapper.sequence_to_codons("AAAAA")  # 5 bases
    
    def test_psi_codon_shape(self):
        """Test codon wave function computation."""
        mapper = GenomicZetaMapper()
        
        assignment = mapper.assign_codon("AAA")
        
        # Single time point
        t_single = np.array([0.0])
        psi = mapper.psi_codon(assignment, t_single)
        assert psi.shape == t_single.shape
        assert np.iscomplexobj(psi)
        
        # Multiple time points
        t_array = np.linspace(0, 1, 100)
        psi = mapper.psi_codon(assignment, t_array)
        assert psi.shape == t_array.shape
        assert np.iscomplexobj(psi)
    
    def test_psi_codon_at_zero(self):
        """Test codon wave function at t=0."""
        mapper = GenomicZetaMapper()
        
        assignment = mapper.assign_codon("AAA")
        t = np.array([0.0])
        psi = mapper.psi_codon(assignment, t)
        
        # At t=0, exp(i*gamma*0) = 1 for all gamma
        # So Psi(0) = sum of amplitudes = 3.0 (with default amps of 1.0 each)
        expected = sum(assignment.amplitudes)
        assert np.isclose(psi[0], expected)
    
    def test_psi_rna_shape(self):
        """Test RNA wave function computation."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAACGAA"
        codons = mapper.sequence_to_codons(sequence)
        
        t = np.linspace(0, 1, 100)
        psi = mapper.psi_rna(codons, t)
        
        assert psi.shape == t.shape
        assert np.iscomplexobj(psi)
    
    def test_psi_rna_at_zero(self):
        """Test RNA wave function at t=0."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAACGAA"  # 3 codons
        codons = mapper.sequence_to_codons(sequence)
        
        t = np.array([0.0])
        psi = mapper.psi_rna(codons, t)
        
        # At t=0, all exponentials = 1, so Psi_RNA(0) = sum of all amplitudes
        # 3 codons * 3 terms each * 1.0 amplitude = 9.0
        expected = 3 * 3 * 1.0
        assert np.isclose(psi[0], expected)
    
    def test_analyze_sequence(self):
        """Test full sequence analysis."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAACGAA"
        analysis = mapper.analyze_sequence(sequence)
        
        assert isinstance(analysis, RNAZetaWaveFunction)
        assert analysis.sequence == "AAAAACGAA"
        assert len(analysis.codons) == 3
        assert analysis.n_terms == 9  # 3 codons * 3 terms
        assert 0.0 <= analysis.coherence_score <= 1.0
    
    def test_analyze_sequence_coherence(self):
        """Test coherence score calculation."""
        mapper = GenomicZetaMapper()
        
        # Sequence with all same codon should have low coherence
        same_sequence = "AAAAAAAAA"  # AAA repeated 3 times
        analysis_same = mapper.analyze_sequence(same_sequence)
        
        # Sequence with different codons should have higher coherence
        varied_sequence = "AAAAACGAA"  # AAA, AAC, GAA
        analysis_varied = mapper.analyze_sequence(varied_sequence)
        
        # Varied sequence should generally have higher coherence
        # (more unique zeros used)
        assert analysis_varied.coherence_score >= analysis_same.coherence_score
    
    def test_print_assignment_table(self):
        """Test table generation."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAAC"
        codons = mapper.sequence_to_codons(sequence)
        
        table = mapper.print_assignment_table(codons)
        
        assert isinstance(table, str)
        assert "Codon" in table
        assert "Indices" in table
        assert "Zeros" in table
        assert "AAA" in table
        assert "AAC" in table
    
    def test_case_insensitivity(self):
        """Test that codon mapping is case-insensitive."""
        mapper = GenomicZetaMapper()
        
        indices_upper = mapper.codon_to_indices("AAA")
        indices_lower = mapper.codon_to_indices("aaa")
        indices_mixed = mapper.codon_to_indices("AaA")
        
        assert indices_upper == indices_lower == indices_mixed
    
    def test_reproducibility(self):
        """Test that results are reproducible across instances."""
        mapper1 = GenomicZetaMapper()
        mapper2 = GenomicZetaMapper()
        
        sequence = "AAAAACGAAGGGGCC"
        
        analysis1 = mapper1.analyze_sequence(sequence)
        analysis2 = mapper2.analyze_sequence(sequence)
        
        # Same sequence should give same indices
        for c1, c2 in zip(analysis1.codons, analysis2.codons):
            assert c1.indices == c2.indices
            assert c1.zeros == c2.zeros
        
        assert analysis1.n_terms == analysis2.n_terms


class TestCodonZetaAssignment:
    """Test suite for CodonZetaAssignment dataclass."""
    
    def test_creation(self):
        """Test creating a codon assignment."""
        assignment = CodonZetaAssignment(
            codon="AAA",
            position=0,
            indices=(1, 2, 3),
            zeros=(14.13, 21.02, 25.01),
            amplitudes=(1.0, 1.0, 1.0)
        )
        
        assert assignment.codon == "AAA"
        assert assignment.position == 0
        assert len(assignment.indices) == 3
        assert len(assignment.zeros) == 3
        assert len(assignment.amplitudes) == 3
    
    def test_invalid_codon_length(self):
        """Test validation of codon length."""
        with pytest.raises(ValueError, match="must be 3 bases"):
            CodonZetaAssignment(
                codon="AA",
                position=0,
                indices=(1, 2, 3),
                zeros=(14.13, 21.02, 25.01)
            )
    
    def test_invalid_bases(self):
        """Test validation of base characters."""
        with pytest.raises(ValueError, match="Invalid RNA bases"):
            CodonZetaAssignment(
                codon="AXC",
                position=0,
                indices=(1, 2, 3),
                zeros=(14.13, 21.02, 25.01)
            )


class TestRNAZetaWaveFunction:
    """Test suite for RNAZetaWaveFunction dataclass."""
    
    def test_creation(self):
        """Test creating an RNA wave function."""
        codons = [
            CodonZetaAssignment("AAA", 0, (1, 2, 3), (14.13, 21.02, 25.01)),
            CodonZetaAssignment("GGG", 1, (4, 5, 6), (30.42, 32.93, 37.58))
        ]
        
        wave_func = RNAZetaWaveFunction(
            sequence="AAAGGG",
            codons=codons,
            n_terms=6,
            coherence_score=0.5
        )
        
        assert wave_func.sequence == "AAAGGG"
        assert len(wave_func.codons) == 2
        assert wave_func.n_terms == 6
        assert wave_func.coherence_score == 0.5


class TestIntegration:
    """Integration tests for the complete workflow."""
    
    def test_complete_workflow(self):
        """Test a complete codon-to-wave-function workflow."""
        mapper = GenomicZetaMapper()
        
        # Use a realistic RNA sequence
        sequence = "AUGAAACCCGGGUUUACG"  # 6 codons
        
        # Parse and analyze
        analysis = mapper.analyze_sequence(sequence)
        
        # Verify structure
        assert len(analysis.codons) == 6
        assert analysis.n_terms == 18
        assert analysis.sequence == "AUGAAACCCGGGUUUACG"
        
        # Compute wave function
        t = np.linspace(0, 2*np.pi, 1000)
        psi = mapper.psi_rna(analysis.codons, t)
        
        # Verify properties
        assert len(psi) == len(t)
        assert np.iscomplexobj(psi)
        assert np.all(np.isfinite(psi))
        
        # Magnitude should be positive
        assert np.all(np.abs(psi) >= 0)
    
    def test_symmetry_properties(self):
        """Test that wave function has expected symmetry."""
        mapper = GenomicZetaMapper()
        
        sequence = "AAAAAAAAA"  # 3 identical codons
        codons = mapper.sequence_to_codons(sequence)
        
        # Compute at symmetric time points
        t = np.array([0.5, -0.5])
        psi = mapper.psi_rna(codons, t)
        
        # Should be complex conjugates (approximately, depends on zeros)
        # At minimum, magnitudes should be equal
        assert np.isclose(np.abs(psi[0]), np.abs(psi[1]))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
