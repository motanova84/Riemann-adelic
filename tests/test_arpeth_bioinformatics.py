"""
Tests for Arpeth Bioinformatics Module

Validates RNA stability analysis via QCAL coherence at 141.7001 Hz.
"""

import pytest
import mpmath as mp
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.arpeth_bioinformatics import (
    ArpethBioinformatics,
    RNACodon,
    BiologicalStability,
    validate_biological_coherence,
    F0_FREQUENCY,
    C_COHERENCE,
    KAPPA_PI
)


class TestArpethConstants:
    """Test QCAL constants used in bioinformatics."""
    
    def test_fundamental_frequency(self):
        """Verify f0 = 141.7001 Hz."""
        assert float(F0_FREQUENCY) == 141.7001
        
    def test_coherence_constant(self):
        """Verify C = 244.36."""
        assert float(C_COHERENCE) == 244.36
        
    def test_fractal_parameter(self):
        """Verify κ_Π = 17 (prime)."""
        assert KAPPA_PI == 17
        # Verify it's prime
        assert all(KAPPA_PI % i != 0 for i in range(2, int(KAPPA_PI**0.5) + 1))


class TestRNACodon:
    """Test RNA codon structure."""
    
    def test_valid_codon_creation(self):
        """Test creating valid RNA codons."""
        codon = RNACodon(sequence="AUG", position=0)
        assert codon.sequence == "AUG"
        assert codon.position == 0
        
    def test_invalid_length(self):
        """Test that codons must be exactly 3 bases."""
        with pytest.raises(ValueError, match="must be 3 bases"):
            RNACodon(sequence="AU", position=0)
            
        with pytest.raises(ValueError, match="must be 3 bases"):
            RNACodon(sequence="AUGC", position=0)
    
    def test_invalid_bases(self):
        """Test that only valid RNA bases are accepted."""
        with pytest.raises(ValueError, match="Invalid RNA bases"):
            RNACodon(sequence="ATG", position=0)  # T instead of U
            
        with pytest.raises(ValueError, match="Invalid RNA bases"):
            RNACodon(sequence="AXG", position=0)  # Invalid base X


class TestArpethBioinformatics:
    """Test Arpeth bioinformatics analyzer."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup analyzer for each test."""
        self.analyzer = ArpethBioinformatics(precision=30)
        
    def test_initialization(self):
        """Test analyzer initialization."""
        assert self.analyzer.f0 == F0_FREQUENCY
        assert self.analyzer.C == C_COHERENCE
        assert self.analyzer.kappa_pi == KAPPA_PI
        
    def test_base_to_frequency_map(self):
        """Test RNA base to frequency mapping."""
        # Each base should map to harmonic of f0
        freq_A = self.analyzer.base_to_frequency_map('A')
        freq_U = self.analyzer.base_to_frequency_map('U')
        freq_G = self.analyzer.base_to_frequency_map('G')
        freq_C = self.analyzer.base_to_frequency_map('C')
        
        # Check they're harmonics of f0
        assert freq_A == F0_FREQUENCY * 1
        assert freq_U == F0_FREQUENCY * 2
        assert freq_G == F0_FREQUENCY * 3
        assert freq_C == F0_FREQUENCY * 4
        
    def test_base_to_frequency_case_insensitive(self):
        """Test that base mapping is case-insensitive."""
        assert (self.analyzer.base_to_frequency_map('a') == 
                self.analyzer.base_to_frequency_map('A'))
        assert (self.analyzer.base_to_frequency_map('u') == 
                self.analyzer.base_to_frequency_map('U'))
                
    def test_invalid_base_frequency(self):
        """Test that invalid bases raise errors."""
        with pytest.raises(ValueError, match="Invalid RNA base"):
            self.analyzer.base_to_frequency_map('X')
            
    def test_codon_resonance_frequency(self):
        """Test codon resonance frequency calculation."""
        # AUG (start codon) should have geometric mean frequency
        freq = self.analyzer.codon_resonance_frequency("AUG")
        
        # Calculate expected: geometric mean of harmonics 1, 2, 3
        expected = F0_FREQUENCY * mp.power(mp.mpf("6"), mp.mpf("1")/mp.mpf("3"))
        
        # Should be close (geometric mean of 1*2*3 = 6^(1/3) ≈ 1.817)
        assert abs(freq - expected) < 1e-10
        
    def test_codon_frequency_invalid_length(self):
        """Test that codons must be 3 bases for frequency calc."""
        with pytest.raises(ValueError, match="must be 3 bases"):
            self.analyzer.codon_resonance_frequency("AU")
            
    def test_fractal_symmetry_palindromes(self):
        """Test fractal symmetry detection via palindromes."""
        # Sequence with clear palindromes
        seq_with_palindrome = "AUGCGCGUA"  # Contains GCG palindrome
        has_sym, score = self.analyzer.fractal_symmetry_score(seq_with_palindrome)
        
        assert score > 0, "Should detect palindromic structure"
        
    def test_fractal_symmetry_short_sequence(self):
        """Test fractal symmetry on very short sequences."""
        short_seq = "AU"
        has_sym, score = self.analyzer.fractal_symmetry_score(short_seq)
        
        assert not has_sym, "Very short sequences shouldn't have symmetry"
        assert score == 0.0
        
    def test_biological_attention_entropy(self):
        """Test biological attention based on sequence entropy."""
        # High entropy sequence (all bases present equally)
        high_entropy_seq = "AUGCAUGCAUGC"
        A_eff_high = self.analyzer.biological_attention(high_entropy_seq)
        
        # Low entropy sequence (single base repeated)
        low_entropy_seq = "AAAAAAAAAAAA"
        A_eff_low = self.analyzer.biological_attention(low_entropy_seq)
        
        # High entropy should give higher attention
        assert A_eff_high > A_eff_low
        
    def test_biological_attention_empty(self):
        """Test biological attention on empty sequence."""
        A_eff = self.analyzer.biological_attention("")
        assert A_eff == 0
        
    def test_validate_resonance_with_f0(self):
        """Test resonance validation with f0."""
        # f0 itself should resonate
        assert self.analyzer.validate_resonance_with_f0(F0_FREQUENCY)
        
        # Harmonics should resonate
        assert self.analyzer.validate_resonance_with_f0(F0_FREQUENCY * 2)
        assert self.analyzer.validate_resonance_with_f0(F0_FREQUENCY * 3)
        
        # Subharmonics should resonate
        assert self.analyzer.validate_resonance_with_f0(F0_FREQUENCY / 2)
        
        # Random frequency should not resonate
        assert not self.analyzer.validate_resonance_with_f0(mp.mpf("99.9"))
        
    def test_calculate_psi_life(self):
        """Test Ψ_Life calculation."""
        # Use a real RNA sequence (start of human beta-globin)
        sequence = "AUGGUGCACGUGACUGACGCUGCACACAAGUCAGCAUCAUUGCAGUGCACCUGCACGUGACCGAGGUGGAG"
        
        stability = self.analyzer.calculate_psi_life(sequence)
        
        # Verify result structure
        assert isinstance(stability, BiologicalStability)
        assert stability.psi_life > 0
        assert stability.attention_eff_squared > 0
        assert stability.coherence_flow > 0
        assert 0 <= stability.stability_score <= 1
        
    def test_psi_life_components(self):
        """Test that Ψ_Life = I × A_eff² × C^∞."""
        sequence = "AUGCAUGCAUGC"
        stability = self.analyzer.calculate_psi_life(sequence)
        
        # Manually calculate
        A_eff = self.analyzer.biological_attention(sequence)
        A_eff_squared = A_eff * A_eff
        C_infinity = mp.power(C_COHERENCE, mp.mpf("8"))
        expected_psi = F0_FREQUENCY * A_eff_squared * C_infinity
        
        # Should match within numerical precision
        assert abs(stability.psi_life - expected_psi) < 1e-10
        
    def test_analyze_rna_sequence(self):
        """Test complete RNA sequence analysis."""
        sequence = "AUGCGCGCGUGA"  # 4 codons with palindromes
        
        results = self.analyzer.analyze_rna_sequence(sequence)
        
        # Check result structure
        assert 'sequence' in results
        assert 'psi_life' in results
        assert 'stability_score' in results
        assert 'codons' in results
        
        # Verify values
        assert results['sequence'] == sequence
        assert results['length'] == len(sequence)
        assert results['num_codons'] == 4
        assert len(results['codons']) == 4
        
        # Each codon should have analysis
        for codon_data in results['codons']:
            assert 'sequence' in codon_data
            assert 'frequency' in codon_data
            assert 'coherent' in codon_data
            
    def test_analyze_rna_with_invalid_bases(self):
        """Test analysis handles invalid bases gracefully."""
        # Sequence with some invalid codons
        sequence = "AUGXYZAUC"  # Middle codon invalid
        
        results = self.analyzer.analyze_rna_sequence(sequence)
        
        # Should still complete but skip invalid codons
        assert 'codons' in results
        # Only valid codons should be analyzed


class TestValidateBiologicalCoherence:
    """Test high-level validation function."""
    
    def test_validate_coherent_sequence(self):
        """Test validation of coherent RNA sequence."""
        # Well-structured RNA sequence
        sequence = "AUGCAUGCAUGCAUGC"
        
        results = validate_biological_coherence(sequence)
        
        assert 'qcal_validated' in results
        assert 'fundamental_frequency' in results
        assert results['fundamental_frequency'] == 141.7001
        
    def test_validate_custom_tolerance(self):
        """Test validation with custom tolerance."""
        sequence = "AUGCCC"
        
        results = validate_biological_coherence(
            sequence,
            tolerance=0.1
        )
        
        assert results['tolerance'] == 0.1
        
    def test_validate_custom_precision(self):
        """Test validation with custom precision."""
        sequence = "AUGCCC"
        
        results = validate_biological_coherence(
            sequence,
            precision=50
        )
        
        # Should complete without errors
        assert 'psi_life' in results


class TestBiologicalStabilityEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_minimum_sequence_length(self):
        """Test analysis of minimum viable RNA sequence."""
        analyzer = ArpethBioinformatics(precision=15)
        
        # Single codon
        min_seq = "AUG"
        results = analyzer.analyze_rna_sequence(min_seq)
        
        assert results['num_codons'] == 1
        assert results['psi_life'] > 0
        
    def test_long_sequence_performance(self):
        """Test that long sequences can be analyzed."""
        analyzer = ArpethBioinformatics(precision=15)
        
        # Moderately long sequence (100 codons = 300 bases)
        long_seq = "AUG" * 100
        
        results = analyzer.analyze_rna_sequence(long_seq)
        
        assert results['num_codons'] == 100
        assert results['psi_life'] > 0
        
    def test_all_same_base(self):
        """Test sequence with all same base."""
        analyzer = ArpethBioinformatics(precision=15)
        
        # All adenine (low entropy, low attention)
        same_base = "AAA" * 10
        
        results = analyzer.analyze_rna_sequence(same_base)
        
        # Should have very low attention due to no diversity
        assert results['attention_eff_squared'] < 0.1


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_frequency_consistency(self):
        """Verify f0 consistency with QCAL framework."""
        from utils.arpeth_bioinformatics import F0_FREQUENCY
        
        # Should match the QCAL fundamental frequency
        assert float(F0_FREQUENCY) == 141.7001
        
    def test_coherence_constant_match(self):
        """Verify C constant matches QCAL."""
        from utils.arpeth_bioinformatics import C_COHERENCE
        
        # From .qcal_beacon: coherence = "C = 244.36"
        assert float(C_COHERENCE) == 244.36
        
    def test_prime_17_connection(self):
        """Verify κ_Π = 17 prime connection."""
        from utils.arpeth_bioinformatics import KAPPA_PI
        
        # κ_Π should be the prime 17
        assert KAPPA_PI == 17
        # Used in fractal symmetry analysis


class TestRealWorldSequences:
    """Test with real biological RNA sequences."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup analyzer."""
        self.analyzer = ArpethBioinformatics(precision=30)
        
    def test_start_codon_aug(self):
        """Test AUG start codon analysis."""
        # AUG is the universal start codon
        results = self.analyzer.analyze_rna_sequence("AUG")
        
        assert results['num_codons'] == 1
        assert results['codons'][0]['sequence'] == "AUG"
        
    def test_stop_codon_uag(self):
        """Test UAG stop codon analysis."""
        # UAG is a stop codon
        results = self.analyzer.analyze_rna_sequence("UAG")
        
        assert results['num_codons'] == 1
        assert results['psi_life'] > 0
        
    def test_human_beta_globin_fragment(self):
        """Test fragment of human beta-globin mRNA."""
        # Fragment of human HBB mRNA (71 bases = 23 complete codons)
        hbb_fragment = (
            "AUGGUGCACGUGACUGACGCUGCACACAAGUCAGCAUCAUUGCAGUGCACCUGCACGUGACCGAGGUGGAG"
        )
        
        results = self.analyzer.analyze_rna_sequence(hbb_fragment)
        
        assert results['num_codons'] == 23  # 71 bases / 3 = 23 complete codons
        assert results['stability_score'] > 0
        assert results['psi_life'] > 0
        
        # Beta-globin is highly conserved, should show some coherence
        assert results['average_codon_resonance'] >= 0


class TestMathematicalProperties:
    """Test mathematical properties of the formulas."""
    
    def test_psi_life_monotonic_in_attention(self):
        """Test that Ψ_Life increases with biological attention."""
        analyzer = ArpethBioinformatics(precision=15)
        
        # High diversity sequence
        high_diversity = "AUGCAUGCAUGC"
        # Low diversity sequence
        low_diversity = "AAAAAAAAAAAA"
        
        result_high = analyzer.calculate_psi_life(high_diversity)
        result_low = analyzer.calculate_psi_life(low_diversity)
        
        # Higher attention should give higher Ψ_Life
        assert result_high.psi_life > result_low.psi_life
        
    def test_stability_score_bounded(self):
        """Test that stability score is in [0, 1]."""
        analyzer = ArpethBioinformatics(precision=15)
        
        sequences = [
            "AUG",
            "AUGCCC",
            "AUGCAUGCAUGC",
            "A" * 30,
            "AUGCGCGCGUGA"
        ]
        
        for seq in sequences:
            results = analyzer.analyze_rna_sequence(seq)
            assert 0 <= results['stability_score'] <= 1, \
                f"Stability score {results['stability_score']} out of bounds for {seq}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
