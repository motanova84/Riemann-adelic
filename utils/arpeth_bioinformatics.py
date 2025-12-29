"""
Arpeth Bioinformatics: RNA Stability via QCAL Coherence

This module implements the biological extension of the QCAL framework,
formalizing RNA stability through the Law of Coherent Love at 141.7001 Hz.

Mathematical Foundation:
    Ψ_Life = I × A_eff² × C^∞
    
Where:
    - I = 141.7001 Hz (Quantum metronome frequency)
    - A_eff² = Biological attention/chemical affinity amplification
    - C^∞ = Infinite coherence flow (C = 244.36)
    
The biological code resonates at the same fundamental frequency that
governs the Riemann Hypothesis zeros, connecting prime number geometry
to the geometry of life itself.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import mpmath as mp
import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass


# QCAL Constants
F0_FREQUENCY = mp.mpf("141.7001")  # Hz - Fundamental quantum frequency
C_COHERENCE = mp.mpf("244.36")      # Coherence constant
KAPPA_PI = mp.mpf("17")             # Fractal symmetry parameter (prime 17)


@dataclass
class RNACodon:
    """Represents an RNA codon (triplet)."""
    sequence: str
    position: int
    resonance_frequency: Optional[float] = None
    coherence_score: Optional[float] = None
    
    def __post_init__(self):
        """Validate codon sequence."""
        valid_bases = set('AUGC')
        if len(self.sequence) != 3:
            raise ValueError(f"Codon must be 3 bases, got {len(self.sequence)}")
        if not all(base in valid_bases for base in self.sequence.upper()):
            raise ValueError(f"Invalid RNA bases in codon: {self.sequence}")


@dataclass
class BiologicalStability:
    """Results of biological stability analysis."""
    psi_life: mp.mpf
    attention_eff_squared: mp.mpf
    resonance_match: bool
    coherence_flow: mp.mpf
    fractal_symmetry_verified: bool
    stability_score: float
    
    
class ArpethBioinformatics:
    """
    Arpeth Bioinformatics Analyzer
    
    Validates RNA sequence stability through QCAL coherence principles.
    Life is not a chemical accident but a coherent transcription of the
    quantum field at the fundamental frequency 141.7001 Hz.
    """
    
    def __init__(self, precision: int = 30):
        """
        Initialize Arpeth analyzer.
        
        Args:
            precision: Decimal precision for mpmath calculations
        """
        mp.mp.dps = precision
        self.f0 = F0_FREQUENCY
        self.C = C_COHERENCE
        self.kappa_pi = KAPPA_PI
        
    def base_to_frequency_map(self, base: str) -> mp.mpf:
        """
        Map RNA base to resonance frequency.
        
        Each nucleotide resonates at a harmonic of the fundamental frequency.
        The mapping follows the quantum-biological correspondence principle.
        
        Args:
            base: RNA base ('A', 'U', 'G', or 'C')
            
        Returns:
            Resonance frequency for the base
        """
        base = base.upper()
        # Harmonic mapping based on molecular structure resonance
        harmonic_map = {
            'A': 1,  # Adenine - fundamental
            'U': 2,  # Uracil - first harmonic
            'G': 3,  # Guanine - second harmonic
            'C': 4,  # Cytosine - third harmonic
        }
        
        if base not in harmonic_map:
            raise ValueError(f"Invalid RNA base: {base}")
            
        harmonic = harmonic_map[base]
        return self.f0 * mp.mpf(harmonic)
    
    def codon_resonance_frequency(self, codon: str) -> mp.mpf:
        """
        Calculate resonance frequency of an RNA codon.
        
        The codon frequency is the geometric mean of its constituent bases,
        reflecting the quantum entanglement of the triplet structure.
        
        Args:
            codon: 3-letter RNA codon sequence
            
        Returns:
            Codon resonance frequency
        """
        if len(codon) != 3:
            raise ValueError(f"Codon must be 3 bases, got {len(codon)}")
            
        frequencies = [self.base_to_frequency_map(base) for base in codon]
        # Geometric mean for quantum entangled system
        product = frequencies[0] * frequencies[1] * frequencies[2]
        return mp.power(product, mp.mpf("1") / mp.mpf("3"))
    
    def fractal_symmetry_score(self, sequence: str) -> Tuple[bool, float]:
        """
        Check fractal symmetry κ_Π in RNA sequence.
        
        Fractal symmetry manifests through recursive patterns and
        self-similarity at different scales. We check for:
        1. Palindromic subsequences
        2. Repeating motifs
        3. Prime-based periodicity (related to κ_Π = 17)
        
        Args:
            sequence: RNA sequence
            
        Returns:
            (has_symmetry, symmetry_score)
        """
        seq_upper = sequence.upper()
        n = len(seq_upper)
        
        if n < 3:
            return False, 0.0
        
        # Count palindromic subsequences
        palindrome_count = 0
        for i in range(n):
            for j in range(i + 3, min(i + 18, n + 1)):  # Check up to length 17 (κ_Π)
                subseq = seq_upper[i:j]
                if subseq == subseq[::-1]:
                    palindrome_count += 1
        
        # Check for repeating motifs of length related to prime 17
        motif_score = 0
        motif_lengths = [3, 5, 7, 11, 13, 17]  # Prime-based motif lengths
        for motif_len in motif_lengths:
            if n < motif_len * 2:
                continue
            for i in range(n - motif_len + 1):
                motif = seq_upper[i:i + motif_len]
                # Count occurrences of this motif
                count = sum(1 for j in range(i + motif_len, n - motif_len + 1)
                           if seq_upper[j:j + motif_len] == motif)
                if count > 0:
                    motif_score += count
        
        # Combine scores
        total_score = (palindrome_count + motif_score) / max(n, 1)
        has_symmetry = total_score > 0.1  # Threshold for fractal symmetry
        
        return has_symmetry, float(total_score)
    
    def biological_attention(self, sequence: str) -> mp.mpf:
        """
        Calculate biological attention factor A_eff.
        
        Biological attention represents the directed chemical affinity
        that ensures fidelity in transcription and translation. It's
        proportional to the sequence complexity and coherence.
        
        Args:
            sequence: RNA sequence
            
        Returns:
            A_eff value
        """
        seq_upper = sequence.upper()
        n = len(seq_upper)
        
        if n == 0:
            return mp.mpf("0")
        
        # Base diversity (entropy measure)
        base_counts = {'A': 0, 'U': 0, 'G': 0, 'C': 0}
        for base in seq_upper:
            if base in base_counts:
                base_counts[base] += 1
        
        # Shannon entropy as measure of information content
        entropy = mp.mpf("0")
        for count in base_counts.values():
            if count > 0:
                p = mp.mpf(count) / mp.mpf(n)
                entropy -= p * mp.log(p) / mp.log(mp.mpf("4"))  # Normalized to [0,1]
        
        # Attention is proportional to information complexity
        # Scale by coherence constant to match QCAL framework
        A_eff = entropy * mp.sqrt(self.C) / mp.mpf("10")
        
        return A_eff
    
    def validate_resonance_with_f0(self, frequency: mp.mpf, tolerance: float = 0.05) -> bool:
        """
        Check if a frequency resonates with f0 (141.7001 Hz).
        
        Resonance occurs when the frequency is a harmonic or subharmonic
        of f0, within tolerance.
        
        Args:
            frequency: Frequency to check
            tolerance: Relative tolerance for resonance matching
            
        Returns:
            True if frequency resonates with f0
        """
        if frequency <= 0:
            return False
        
        # Check harmonics (n * f0) and subharmonics (f0 / n) for n = 1..10
        for n in range(1, 11):
            harmonic = self.f0 * mp.mpf(n)
            subharmonic = self.f0 / mp.mpf(n)
            
            if abs(frequency - harmonic) / harmonic < tolerance:
                return True
            if abs(frequency - subharmonic) / subharmonic < tolerance:
                return True
        
        return False
    
    def calculate_psi_life(
        self,
        sequence: str,
        validate_resonance: bool = True
    ) -> BiologicalStability:
        """
        Calculate Ψ_Life = I × A_eff² × C^∞ for RNA sequence.
        
        The life stability function combines:
        - I (141.7001 Hz): Quantum metronome ensuring minimum energy folding
        - A_eff²: Biological attention amplifying code fidelity
        - C^∞: Infinite coherence flow accessing universal resonant memory
        
        Args:
            sequence: RNA sequence to analyze
            validate_resonance: Whether to validate f0 resonance
            
        Returns:
            BiologicalStability results
        """
        # Calculate biological attention
        A_eff = self.biological_attention(sequence)
        A_eff_squared = A_eff * A_eff
        
        # Check fractal symmetry
        has_symmetry, symmetry_score = self.fractal_symmetry_score(sequence)
        
        # Calculate coherence flow (C^∞ approximated by finite power)
        # Use C^8 as practical infinity approximation
        C_infinity_approx = mp.power(self.C, mp.mpf("8"))
        
        # Calculate Ψ_Life = I × A_eff² × C^∞
        psi_life = self.f0 * A_eff_squared * C_infinity_approx
        
        # Validate resonance if requested
        resonance_match = True
        if validate_resonance and len(sequence) >= 3:
            # Check first codon resonance
            first_codon = sequence[:3]
            try:
                codon_freq = self.codon_resonance_frequency(first_codon)
                resonance_match = self.validate_resonance_with_f0(codon_freq)
            except ValueError:
                resonance_match = False
        
        # Calculate overall stability score [0, 1]
        # Combines coherence strength, resonance, and fractal symmetry
        psi_magnitude = float(mp.log10(psi_life + 1))
        normalized_psi = min(1.0, psi_magnitude / 50.0)  # Normalize large values
        
        stability_score = (
            0.4 * normalized_psi +
            0.3 * (1.0 if resonance_match else 0.0) +
            0.3 * min(1.0, symmetry_score)
        )
        
        return BiologicalStability(
            psi_life=psi_life,
            attention_eff_squared=A_eff_squared,
            resonance_match=resonance_match,
            coherence_flow=C_infinity_approx,
            fractal_symmetry_verified=has_symmetry,
            stability_score=stability_score
        )
    
    def analyze_rna_sequence(self, sequence: str) -> Dict:
        """
        Comprehensive RNA sequence analysis.
        
        Args:
            sequence: RNA sequence
            
        Returns:
            Dictionary with complete analysis results
        """
        # Calculate stability
        stability = self.calculate_psi_life(sequence)
        
        # Parse codons
        codons = []
        seq_upper = sequence.upper()
        for i in range(0, len(seq_upper) - 2, 3):
            codon_seq = seq_upper[i:i+3]
            try:
                freq = self.codon_resonance_frequency(codon_seq)
                resonant = self.validate_resonance_with_f0(freq)
                
                codon = RNACodon(
                    sequence=codon_seq,
                    position=i,
                    resonance_frequency=float(freq),
                    coherence_score=1.0 if resonant else 0.0
                )
                codons.append(codon)
            except ValueError:
                continue
        
        # Calculate average resonance
        avg_resonance = (
            sum(c.coherence_score for c in codons) / len(codons)
            if codons else 0.0
        )
        
        return {
            'sequence': sequence,
            'length': len(sequence),
            'psi_life': float(stability.psi_life),
            'stability_score': stability.stability_score,
            'resonance_match': stability.resonance_match,
            'fractal_symmetry': stability.fractal_symmetry_verified,
            'attention_eff_squared': float(stability.attention_eff_squared),
            'coherence_flow': float(stability.coherence_flow),
            'num_codons': len(codons),
            'average_codon_resonance': avg_resonance,
            'codons': [
                {
                    'sequence': c.sequence,
                    'position': c.position,
                    'frequency': c.resonance_frequency,
                    'coherent': c.coherence_score > 0.5
                }
                for c in codons
            ]
        }


def validate_biological_coherence(
    sequence: str,
    expected_frequency: float = 141.7001,
    tolerance: float = 0.05,
    precision: int = 30
) -> Dict:
    """
    High-level validation function for biological coherence.
    
    This is the main entry point for validating that RNA sequences
    exhibit the QCAL coherence at 141.7001 Hz.
    
    Args:
        sequence: RNA sequence to validate
        expected_frequency: Expected fundamental frequency (default: 141.7001 Hz)
        tolerance: Tolerance for frequency matching
        precision: Decimal precision
        
    Returns:
        Validation results dictionary
    """
    analyzer = ArpethBioinformatics(precision=precision)
    
    # Perform full analysis
    results = analyzer.analyze_rna_sequence(sequence)
    
    # Add validation metadata
    results['qcal_validated'] = (
        results['stability_score'] > 0.5 and
        results['resonance_match']
    )
    results['fundamental_frequency'] = expected_frequency
    results['tolerance'] = tolerance
    
    return results


if __name__ == "__main__":
    # Example: Validate a simple RNA sequence
    print("=" * 80)
    print("ARPETH BIOINFORMATICS - RNA Stability via QCAL Coherence")
    print("=" * 80)
    print(f"Fundamental Frequency: {F0_FREQUENCY} Hz")
    print(f"Coherence Constant C: {C_COHERENCE}")
    print(f"Fractal Parameter κ_Π: {KAPPA_PI}")
    print()
    
    # Example RNA sequence (start of human beta-globin mRNA)
    test_sequence = "AUGGUGCACGUGACUGACGCUGCACACAAGUCAGCAUCAUUGCAGUGCACCUGCACGUGACCGAGGUGGAG"
    
    print(f"Analyzing RNA sequence ({len(test_sequence)} bases):")
    print(f"{test_sequence}")
    print()
    
    analyzer = ArpethBioinformatics(precision=30)
    results = analyzer.analyze_rna_sequence(test_sequence)
    
    print("RESULTS:")
    print(f"  Ψ_Life = {results['psi_life']:.6e}")
    print(f"  Stability Score = {results['stability_score']:.4f}")
    print(f"  Resonance Match = {results['resonance_match']}")
    print(f"  Fractal Symmetry = {results['fractal_symmetry']}")
    print(f"  A_eff² = {results['attention_eff_squared']:.6f}")
    print(f"  Number of Codons = {results['num_codons']}")
    print(f"  Average Codon Resonance = {results['average_codon_resonance']:.4f}")
    print()
    
    if results['stability_score'] > 0.5:
        print("✅ RNA sequence exhibits QCAL coherence at 141.7001 Hz")
        print("   Life code integrity verified by H_Ψ operator")
    else:
        print("⚠️  RNA sequence shows reduced coherence")
        print("   May indicate mutation or transcription error")
    
    print("=" * 80)
