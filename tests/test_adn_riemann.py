#!/usr/bin/env python3
"""
Tests for DNA Mutation Resonance System
========================================

Tests the adn_riemann module for DNA sequence resonance analysis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import sys
from pathlib import Path

# Add repo root to path
repo_root = Path(__file__).parent.parent
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

import adn_riemann as adn
import numpy as np


class TestDNAResonance:
    """Test DNA resonance calculations."""
    
    def test_validate_sequence(self):
        """Test sequence validation."""
        assert adn.validate_sequence("ATGC")
        assert adn.validate_sequence("atgc")
        assert adn.validate_sequence("AAATTTGGGCCC")
        assert not adn.validate_sequence("ATGCN")
        assert not adn.validate_sequence("ATGCU")  # U is RNA, not DNA
    
    def test_calculate_resonance_basic(self):
        """Test basic resonance calculation."""
        # Empty sequence
        assert adn.calculate_resonance("") == 0.0
        
        # Single base
        r_a = adn.calculate_resonance("A")
        assert 0.0 <= r_a <= 1.0
        
        # Simple sequences
        r_atgc = adn.calculate_resonance("ATGC")
        assert 0.0 <= r_atgc <= 1.0
        
        r_tata = adn.calculate_resonance("TATA")
        assert 0.0 <= r_tata <= 1.0
    
    def test_resonance_case_insensitive(self):
        """Test that resonance is case-insensitive."""
        r_upper = adn.calculate_resonance("ATGC")
        r_lower = adn.calculate_resonance("atgc")
        r_mixed = adn.calculate_resonance("AtGc")
        
        assert r_upper == r_lower
        assert r_upper == r_mixed
    
    def test_generate_mutations(self):
        """Test mutation generation."""
        sequence = "ATGC"
        mutations = adn.generate_mutations(sequence)
        
        # Should have substitutions, insertions, and deletions
        assert len(mutations) > 0
        
        # Check that all mutation types are present
        types = set(m.mutation_type for m in mutations)
        assert adn.MutationType.SUBSTITUTION in types
        assert adn.MutationType.INSERTION in types
        assert adn.MutationType.DELETION in types
        
        # Check mutations are sorted by score
        scores = [m.score for m in mutations]
        assert scores == sorted(scores, reverse=True)
    
    def test_mutation_substitution(self):
        """Test substitution mutations."""
        sequence = "A"
        mutations = adn.generate_mutations(sequence)
        
        substitutions = [m for m in mutations if m.mutation_type == adn.MutationType.SUBSTITUTION]
        
        # Should have 3 substitutions (T, G, C)
        assert len(substitutions) == 3
        
        mutated_bases = set(m.mutated for m in substitutions)
        assert mutated_bases == {'T', 'G', 'C'}
    
    def test_mutation_insertion(self):
        """Test insertion mutations."""
        sequence = "AT"
        mutations = adn.generate_mutations(sequence)
        
        insertions = [m for m in mutations if m.mutation_type == adn.MutationType.INSERTION]
        
        # Should have insertions at positions 0, 1, 2 for each of 4 bases
        assert len(insertions) == 3 * 4  # 3 positions × 4 bases
        
        # All insertions should increase sequence length by 1
        for insertion in insertions:
            assert len(insertion.mutated) == len(sequence) + 1
    
    def test_mutation_deletion(self):
        """Test deletion mutations."""
        sequence = "ATGC"
        mutations = adn.generate_mutations(sequence)
        
        deletions = [m for m in mutations if m.mutation_type == adn.MutationType.DELETION]
        
        # Should have 4 deletions (one for each position)
        assert len(deletions) == 4
        
        # All deletions should decrease sequence length by 1
        for deletion in deletions:
            assert len(deletion.mutated) == len(sequence) - 1
    
    def test_greedy_optimize(self):
        """Test greedy optimization."""
        sequence = "ATCG"
        optimized, steps = adn.greedy_optimize(sequence, max_iterations=5)
        
        # Should return a sequence
        assert isinstance(optimized, str)
        assert len(optimized) > 0
        
        # Steps should be a list
        assert isinstance(steps, list)
        
        # Final resonance should be >= initial resonance
        initial_resonance = adn.calculate_resonance(sequence)
        final_resonance = adn.calculate_resonance(optimized)
        assert final_resonance >= initial_resonance
        
        # Number of steps should not exceed max_iterations
        assert len(steps) <= 5
    
    def test_greedy_optimize_no_improvement(self):
        """Test greedy optimization when no improvement possible."""
        # A sequence that's already optimal or near-optimal
        sequence = "TTTTTT"
        optimized, steps = adn.greedy_optimize(sequence, max_iterations=3)
        
        # May not change much
        assert isinstance(optimized, str)
        assert len(steps) >= 0
    
    def test_find_hotspots(self):
        """Test hotspot detection."""
        sequence = "ATGCATGCATGC"
        hotspots = adn.find_hotspots(sequence, window_size=3, threshold=0.3)
        
        # Should return a list of positions
        assert isinstance(hotspots, list)
        
        # All positions should be valid
        for pos in hotspots:
            assert 0 <= pos < len(sequence) - 2
    
    def test_analyze_mutation_types(self):
        """Test mutation type analysis."""
        sequence = "ATGC"
        analysis = adn.analyze_mutation_types(sequence)
        
        # Should have all three mutation types
        assert "sustitución" in analysis
        assert "inserción" in analysis
        assert "deleción" in analysis
        
        # Each should be a Mutation object
        for mutation in analysis.values():
            assert isinstance(mutation, adn.Mutation)
            assert hasattr(mutation, 'score')
            assert hasattr(mutation, 'delta_resonance')


class TestMutationDataStructures:
    """Test mutation data structures."""
    
    def test_mutation_type_enum(self):
        """Test MutationType enum."""
        assert adn.MutationType.SUBSTITUTION.value == "sustitución"
        assert adn.MutationType.INSERTION.value == "inserción"
        assert adn.MutationType.DELETION.value == "deleción"
    
    def test_mutation_dataclass(self):
        """Test Mutation dataclass."""
        mutation = adn.Mutation(
            original="ATGC",
            mutated="TTGC",
            position=0,
            mutation_type=adn.MutationType.SUBSTITUTION,
            score=0.5,
            delta_resonance=0.1,
            is_beneficial=True
        )
        
        assert mutation.original == "ATGC"
        assert mutation.mutated == "TTGC"
        assert mutation.position == 0
        assert mutation.score == 0.5
        assert mutation.is_beneficial


class TestQCALConstants:
    """Test QCAL constants."""
    
    def test_f0_frequency(self):
        """Test fundamental frequency."""
        assert adn.F0_QCAL == 141.7001
    
    def test_riemann_zeros(self):
        """Test Riemann zeros list."""
        assert len(adn.RIEMANN_ZEROS) == 30
        assert adn.RIEMANN_ZEROS[0] == pytest.approx(14.134725141735, rel=1e-6)
        
        # All zeros should be positive
        assert all(z > 0 for z in adn.RIEMANN_ZEROS)
        
        # Zeros should be in ascending order
        for i in range(len(adn.RIEMANN_ZEROS) - 1):
            assert adn.RIEMANN_ZEROS[i] < adn.RIEMANN_ZEROS[i+1]
    
    def test_base_phase_map(self):
        """Test base-to-phase mapping."""
        assert 'A' in adn.BASE_PHASE
        assert 'T' in adn.BASE_PHASE
        assert 'G' in adn.BASE_PHASE
        assert 'C' in adn.BASE_PHASE
        
        # Phases should be in [0, 2π)
        for phase in adn.BASE_PHASE.values():
            assert 0 <= phase < 2 * np.pi


class TestIntegration:
    """Integration tests."""
    
    def test_full_pipeline(self):
        """Test full analysis pipeline."""
        sequence = "ATGC"
        
        # 1. Calculate initial resonance
        initial_res = adn.calculate_resonance(sequence)
        assert 0.0 <= initial_res <= 1.0
        
        # 2. Generate mutations
        mutations = adn.generate_mutations(sequence)
        assert len(mutations) > 0
        
        # 3. Get best mutation
        best = mutations[0]
        assert best.score >= initial_res or best.score < adn.RESONANCE_THRESHOLD
        
        # 4. Optimize
        optimized, steps = adn.greedy_optimize(sequence)
        final_res = adn.calculate_resonance(optimized)
        assert final_res >= initial_res
        
        # 5. Find hotspots
        hotspots = adn.find_hotspots(sequence * 3)  # Longer sequence
        assert isinstance(hotspots, list)
        
        # 6. Analyze mutation types
        type_analysis = adn.analyze_mutation_types(sequence)
        assert len(type_analysis) == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
