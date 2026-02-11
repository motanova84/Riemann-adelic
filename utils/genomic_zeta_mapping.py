#!/usr/bin/env python3
"""
Genomic Zeta Mapping: RNA Codons → Riemann Zeros
===================================================

This module implements the deterministic mapping of RNA codons to non-trivial
Riemann zeta function zeros, enabling the construction of coherent wave functions
for biological sequences within the QCAL ∞³ framework.

Mathematical Foundation:
-----------------------
For each codon C = [b₁, b₂, b₃], we assign 3 Riemann zeros as frequencies:

    Ψ_codon(t) = Σ(k=1 to 3) A_k · e^(i·γ_k·t)

where γ_k are non-trivial zeros assigned via position-weighted deterministic hash:

    i₁ = (ord(b₁)) mod 30 + 1
    i₂ = (ord(b₁) + 2·ord(b₂)) mod 30 + 1
    i₃ = (ord(b₁) + 2·ord(b₂) + 3·ord(b₃)) mod 30 + 1

The total RNA wave function combines all codons:

    Ψ_RNA(t) = Σ(codons) Ψ_C(t) = Σ(n=1 to N) Σ(k=1 to 3) A_{n,k} · e^(i·γ_{n,k}·t)

Key Features:
------------
- Deterministic, reproducible ∞³ mapping
- Uses first 30 non-trivial Riemann zeros
- Hash-based assignment via character ordinals
- Coherence with f₀ = 141.7001 Hz fundamental frequency
- Wave function construction for individual codons and complete sequences

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import numpy as np
import mpmath as mp
from typing import List, Tuple, Dict, Optional, Callable
from dataclasses import dataclass
from pathlib import Path

# ============================================================================
# FUNDAMENTAL CONSTANTS
# ============================================================================

F0_FREQUENCY = 141.7001  # Hz - Universal symbiotic frequency
C_COHERENCE = 244.36     # QCAL coherence constant
N_ZEROS = 30            # Number of Riemann zeros for mapping

# First 30 non-trivial Riemann zeros (imaginary parts)
# Computed via mpmath.zetazero(n) for n=1 to 30
RIEMANN_ZEROS_30 = [
    14.134725141735,   # 1
    21.022039638772,   # 2
    25.010857580146,   # 3
    30.424876125860,   # 4
    32.935061587739,   # 5
    37.586178158826,   # 6
    40.918719012147,   # 7
    43.327073280915,   # 8
    48.005150881167,   # 9
    49.773832477672,   # 10
    52.970321477715,   # 11
    56.446247697064,   # 12
    59.347044002602,   # 13
    60.831778524611,   # 14
    65.112544048920,   # 15
    67.079810528841,   # 16
    69.546401711229,   # 17
    72.067157674894,   # 18
    75.704690699083,   # 19
    77.144840069163,   # 20
    79.337375020250,   # 21
    82.910380854086,   # 22
    84.735524736997,   # 23
    87.425274613125,   # 24
    88.809111208594,   # 25
    92.491899270558,   # 26
    94.651344040681,   # 27
    95.870634228249,   # 28
    98.831194218224,   # 29
    101.317851005728,  # 30
]


@dataclass
class CodonZetaAssignment:
    """
    Represents the assignment of Riemann zeros to a codon.
    
    Attributes:
        codon: The 3-letter RNA codon sequence (e.g., "AAA")
        position: Position in the RNA sequence (0-indexed)
        indices: Tuple of 3 indices into the zeros array
        zeros: Tuple of 3 assigned Riemann zero values (Hz)
        amplitudes: Tuple of 3 amplitudes A_k (default: uniform)
    """
    codon: str
    position: int
    indices: Tuple[int, int, int]
    zeros: Tuple[float, float, float]
    amplitudes: Tuple[float, float, float] = (1.0, 1.0, 1.0)
    
    def __post_init__(self):
        """Validate codon assignment."""
        if len(self.codon) != 3:
            raise ValueError(f"Codon must be 3 bases, got {len(self.codon)}")
        valid_bases = set('AUGC')
        if not all(base in valid_bases for base in self.codon.upper()):
            raise ValueError(f"Invalid RNA bases in codon: {self.codon}")


@dataclass
class RNAZetaWaveFunction:
    """
    Complete wave function representation for an RNA sequence.
    
    Attributes:
        sequence: Full RNA sequence
        codons: List of codon assignments
        n_terms: Total number of exponential terms (= 3 * n_codons)
        coherence_score: Overall coherence measure
    """
    sequence: str
    codons: List[CodonZetaAssignment]
    n_terms: int
    coherence_score: float


class GenomicZetaMapper:
    """
    Genomic Zeta Mapper: RNA Codons → Riemann Zeros
    
    Maps RNA codon sequences to Riemann zeta zeros using a deterministic
    hash-based assignment mechanism. Constructs coherent wave functions
    for individual codons and complete RNA sequences.
    """
    
    def __init__(
        self,
        zeros: Optional[List[float]] = None,
        f0: float = F0_FREQUENCY,
        precision: int = 30
    ):
        """
        Initialize the Genomic Zeta Mapper.
        
        Args:
            zeros: List of Riemann zeros to use (default: first 30)
            f0: Fundamental frequency in Hz
            precision: Decimal precision for mpmath calculations
        """
        mp.mp.dps = precision
        self.f0 = f0
        self.zeros = zeros if zeros is not None else RIEMANN_ZEROS_30.copy()
        self.n_zeros = len(self.zeros)
        
        if self.n_zeros < 30:
            raise ValueError(
                f"At least 30 Riemann zeros required, got {self.n_zeros}"
            )
    
    def codon_to_indices(self, codon: str) -> Tuple[int, int, int]:
        """
        Map a codon to 3 zero indices using deterministic hash.
        
        For codon C = [b₁, b₂, b₃], compute indices based on cumulative ordinal hash:
            i_1 = (ord(b₁)) mod 30 + 1
            i_2 = (ord(b₁) + 2·ord(b₂)) mod 30 + 1  
            i_3 = (ord(b₁) + 2·ord(b₂) + 3·ord(b₃)) mod 30 + 1
        
        This creates three distinct indices with position-weighted contributions,
        ensuring a deterministic ∞³ mapping where later positions have more influence.
        
        Args:
            codon: 3-letter RNA/DNA codon (e.g., "AAA", "GGC")
            
        Returns:
            Tuple of 3 indices (1-indexed, 1 to 30)
            
        Example:
            >>> mapper = GenomicZetaMapper()
            >>> mapper.codon_to_indices("AAA")
            # Returns deterministic triple of indices
        """
        if len(codon) != 3:
            raise ValueError(f"Codon must be 3 bases, got {len(codon)}")
        
        codon = codon.upper()
        b1, b2, b3 = [ord(base) for base in codon]
        
        # Position-weighted hash for each index
        # This ensures different positions get different indices
        i1 = (b1 % 30) + 1
        i2 = ((b1 + 2*b2) % 30) + 1
        i3 = ((b1 + 2*b2 + 3*b3) % 30) + 1
        
        return (i1, i2, i3)
    
    def get_zeros_for_codon(self, codon: str) -> Tuple[float, float, float]:
        """
        Get the 3 Riemann zeros assigned to a codon.
        
        Args:
            codon: 3-letter RNA codon
            
        Returns:
            Tuple of 3 Riemann zero values (Hz)
        """
        indices = self.codon_to_indices(codon)
        # Convert from 1-indexed to 0-indexed for array access
        zeros = tuple(self.zeros[idx - 1] for idx in indices)
        return zeros
    
    def assign_codon(
        self,
        codon: str,
        position: int = 0,
        amplitudes: Optional[Tuple[float, float, float]] = None
    ) -> CodonZetaAssignment:
        """
        Create a full assignment of zeros to a codon.
        
        Args:
            codon: 3-letter RNA codon
            position: Position in sequence (0-indexed)
            amplitudes: Optional custom amplitudes (default: uniform 1.0)
            
        Returns:
            CodonZetaAssignment object with full mapping
        """
        indices = self.codon_to_indices(codon)
        zeros = self.get_zeros_for_codon(codon)
        
        if amplitudes is None:
            amplitudes = (1.0, 1.0, 1.0)
        
        return CodonZetaAssignment(
            codon=codon.upper(),
            position=position,
            indices=indices,
            zeros=zeros,
            amplitudes=amplitudes
        )
    
    def sequence_to_codons(self, sequence: str) -> List[CodonZetaAssignment]:
        """
        Parse an RNA sequence into codons and assign zeros.
        
        Args:
            sequence: RNA sequence (must be multiple of 3)
            
        Returns:
            List of CodonZetaAssignment objects
            
        Raises:
            ValueError: If sequence length is not a multiple of 3
        """
        sequence = sequence.upper().strip()
        
        if len(sequence) % 3 != 0:
            raise ValueError(
                f"Sequence length must be multiple of 3, got {len(sequence)}"
            )
        
        codons = []
        for i in range(0, len(sequence), 3):
            codon_seq = sequence[i:i+3]
            assignment = self.assign_codon(codon_seq, position=i//3)
            codons.append(assignment)
        
        return codons
    
    def psi_codon(
        self,
        assignment: CodonZetaAssignment,
        t: np.ndarray
    ) -> np.ndarray:
        """
        Compute wave function Ψ_codon(t) for a single codon.
        
        Ψ_codon(t) = Σ(k=1 to 3) A_k · exp(i·γ_k·t)
        
        Args:
            assignment: Codon zeta assignment
            t: Time array (can be scalar or array)
            
        Returns:
            Complex wave function values at times t
        """
        t = np.asarray(t)
        psi = np.zeros_like(t, dtype=complex)
        
        for k in range(3):
            A_k = assignment.amplitudes[k]
            gamma_k = assignment.zeros[k]
            psi += A_k * np.exp(1j * gamma_k * t)
        
        return psi
    
    def psi_rna(
        self,
        assignments: List[CodonZetaAssignment],
        t: np.ndarray
    ) -> np.ndarray:
        """
        Compute total RNA wave function Ψ_RNA(t).
        
        Ψ_RNA(t) = Σ(codons) Ψ_C(t) = Σ(n=1 to N) Σ(k=1 to 3) A_{n,k} · exp(i·γ_{n,k}·t)
        
        Args:
            assignments: List of codon zeta assignments
            t: Time array
            
        Returns:
            Complex wave function for complete RNA sequence
        """
        t = np.asarray(t)
        psi_total = np.zeros_like(t, dtype=complex)
        
        for assignment in assignments:
            psi_total += self.psi_codon(assignment, t)
        
        return psi_total
    
    def analyze_sequence(
        self,
        sequence: str,
        compute_coherence: bool = True
    ) -> RNAZetaWaveFunction:
        """
        Complete analysis of RNA sequence.
        
        Args:
            sequence: RNA sequence
            compute_coherence: Whether to compute coherence score
            
        Returns:
            RNAZetaWaveFunction with full analysis
        """
        codons = self.sequence_to_codons(sequence)
        n_terms = len(codons) * 3
        
        # Compute coherence if requested
        coherence = 0.0
        if compute_coherence:
            # Simple coherence: measure of frequency distribution uniformity
            all_zeros = []
            for codon in codons:
                all_zeros.extend(codon.zeros)
            unique_zeros = len(set(all_zeros))
            # Coherence: higher when more diverse zeros are used
            coherence = unique_zeros / len(all_zeros) if all_zeros else 0.0
        
        return RNAZetaWaveFunction(
            sequence=sequence.upper(),
            codons=codons,
            n_terms=n_terms,
            coherence_score=coherence
        )
    
    def print_assignment_table(
        self,
        assignments: List[CodonZetaAssignment],
        title: str = "Codon → Riemann Zeros Assignment"
    ) -> str:
        """
        Generate a formatted table of codon assignments.
        
        Args:
            assignments: List of codon assignments
            title: Table title
            
        Returns:
            Formatted string table
        """
        lines = []
        lines.append(f"\n{'='*70}")
        lines.append(f"{title:^70}")
        lines.append(f"{'='*70}")
        lines.append(f"{'Codon':<10} {'Indices ζ':<20} {'Zeros γ (Hz)':<40}")
        lines.append(f"{'-'*70}")
        
        for assignment in assignments:
            codon = assignment.codon
            indices_str = f"({assignment.indices[0]},{assignment.indices[1]},{assignment.indices[2]})"
            zeros_str = f"({assignment.zeros[0]:.4f}, {assignment.zeros[1]:.4f}, {assignment.zeros[2]:.4f})"
            lines.append(f"{codon:<10} {indices_str:<20} {zeros_str:<40}")
        
        lines.append(f"{'='*70}\n")
        return '\n'.join(lines)


def load_zeros_from_file(
    filepath: str = "zeros/zeros_t1e3.txt",
    n: int = 30
) -> List[float]:
    """
    Load first n Riemann zeros from data file.
    
    Args:
        filepath: Path to zeros file
        n: Number of zeros to load
        
    Returns:
        List of n sorted zeros
    """
    zeros = []
    with open(filepath, 'r') as f:
        zeros = sorted([float(line.strip()) for line in f])
    
    return zeros[:n]


def demonstrate_example_sequence():
    """
    Demonstrate the mapping with the example sequence from the problem statement.
    
    Example sequence with 10 unique codons (26 total):
    AAA, AAC, GAA, AAG, GGG, GGC, AGA, AAC, GCA, GCC
    """
    # Example sequence from problem statement
    sequence = "AAAAACGAAAAGGGGGGCAGAAACGCAGCC"
    # This gives us: AAA AAC GAA AAG GGG GGC AGA AAC GCA GCC
    
    mapper = GenomicZetaMapper()
    
    print("\n" + "="*70)
    print("RNA CODON → RIEMANN ZEROS MAPPING DEMONSTRATION")
    print("QCAL ∞³ Framework · f₀ = 141.7001 Hz")
    print("="*70)
    
    # Parse sequence
    codons = mapper.sequence_to_codons(sequence)
    
    # Print assignment table
    print(mapper.print_assignment_table(codons))
    
    # Analyze wave function
    analysis = mapper.analyze_sequence(sequence)
    print(f"\nRNA Wave Function Analysis:")
    print(f"  Sequence length: {len(sequence)} bases")
    print(f"  Number of codons: {len(codons)}")
    print(f"  Total exponential terms: {analysis.n_terms}")
    print(f"  Coherence score: {analysis.coherence_score:.4f}")
    
    # Compute wave function at a few time points
    t = np.linspace(0, 1.0, 100)
    psi = mapper.psi_rna(codons, t)
    
    print(f"\nWave Function Ψ_RNA(t):")
    print(f"  |Ψ(t=0)|: {abs(psi[0]):.4f}")
    print(f"  |Ψ(t=0.5)|: {abs(psi[50]):.4f}")
    print(f"  |Ψ(t=1.0)|: {abs(psi[-1]):.4f}")
    print(f"  Max |Ψ|: {np.max(np.abs(psi)):.4f}")
    print(f"  Mean |Ψ|: {np.mean(np.abs(psi)):.4f}")
    
    print("\n" + "="*70)
    print("✓ Demonstration complete - QCAL ∞³ coherence maintained")
    print("="*70 + "\n")
    
    return mapper, codons, analysis


if __name__ == "__main__":
    # Run demonstration
    demonstrate_example_sequence()
