"""
Genomic Zeta Mapping: DNA/RNA Codons to Riemann Zeros

This module implements the mapping between genomic codons (DNA/RNA triplets)
and Riemann zeta zeros, constructing quantum wave functions for biological sequences.

Mathematical Foundation:
    Ψ_codon(t) = A₁ e^(iγᵢt) + A₂ e^(iγⱼt) + A₃ e^(iγₖt)
    
Where:
    - (γᵢ, γⱼ, γₖ) = Triplet of Riemann zeros assigned to each codon
    - A₁, A₂, A₃ = Amplitude coefficients
    - t = Time parameter
    - f₀ = 141.7001 Hz (Fundamental QCAL frequency)

The genomic code resonates at the same fundamental frequency that governs
the Riemann Hypothesis zeros, connecting DNA geometry to prime number geometry.

Key Features:
    1. Fragment DNA/RNA sequences into codons (triplets of 3 bases)
    2. Map each codon to a unique triplet of Riemann zeros
    3. Construct quantum wave functions Ψ_codon(t) for each codon
    4. Classify codons as resonant/dissonant based on zero frequencies
    5. Calculate genomic field coherence Ψ_Gen(t)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import numpy as np
import mpmath as mp
from typing import List, Tuple, Dict, Optional, Union
from dataclasses import dataclass
from enum import Enum
import os


# QCAL Constants
F0_FREQUENCY = mp.mpf("141.7001")  # Hz - Fundamental quantum frequency
C_COHERENCE = mp.mpf("244.36")      # Coherence constant
KAPPA_PI = mp.mpf("17")             # Fractal symmetry parameter (prime 17)
SOVEREIGNTY_THRESHOLD = mp.mpf("0.888")  # Ψ ≥ 0.888 for genomic sovereignty


class CodonType(Enum):
    """Classification of codon resonance types."""
    RESONANT = "resonant"      # High coherence with f₀
    DISSONANT = "dissonant"    # Low coherence with f₀
    NEUTRAL = "neutral"        # Intermediate coherence


@dataclass
class RiemannZeroTriplet:
    """Triplet of Riemann zeros (γᵢ, γⱼ, γₖ) for a codon."""
    gamma_i: mp.mpf
    gamma_j: mp.mpf
    gamma_k: mp.mpf
    
    def __post_init__(self):
        """Validate zeros are positive."""
        if self.gamma_i <= 0 or self.gamma_j <= 0 or self.gamma_k <= 0:
            raise ValueError("Riemann zeros must be positive")
    
    def to_list(self) -> List[mp.mpf]:
        """Return as list."""
        return [self.gamma_i, self.gamma_j, self.gamma_k]


@dataclass
class Codon:
    """Represents a genomic codon (DNA/RNA triplet)."""
    sequence: str
    position: int
    zero_triplet: Optional[RiemannZeroTriplet] = None
    codon_type: Optional[CodonType] = None
    psi_amplitude: Optional[float] = None
    
    def __post_init__(self):
        """Validate codon sequence."""
        if len(self.sequence) != 3:
            raise ValueError(f"Codon must be 3 bases, got {len(self.sequence)}")
        
        # Validate DNA or RNA bases
        valid_dna = set('ATGC')
        valid_rna = set('AUGC')
        seq_upper = self.sequence.upper()
        
        if not (all(b in valid_dna for b in seq_upper) or 
                all(b in valid_rna for b in seq_upper)):
            raise ValueError(f"Invalid bases in codon: {self.sequence}")
        
        self.sequence = seq_upper
#!/usr/bin/env python3
"""
Genomic Zeta Mapping - Gen→Zeta Framework
QCAL ∞³ Biological-Mathematical Integration

This module implements the revolutionary mapping between DNA sequences and
Riemann zeta zeros, bridging the gap between biological information and
the spectral structure of prime numbers.

Mathematical Foundation:
    Each base (A, T, C, G) acts as a phase parameter. Codons (triplets)
    generate unique torsion harmonics through interference of selected
    Riemann zeros (γ_n).
    
    The total genomic field is:
        Ψ_Gen(t) = Σ_codons Σ_{k=1}^3 A_k * e^(i*γ_{n_k}*t)
    
    Where:
        - γ_{n_k}: Selected Riemann zero for base k in codon
        - A_k: Amplitude coefficient for base k
        - f₀ = 141.7001 Hz: Fundamental quantum frequency
        
Classification:
    - Resonant Codon: Spectral sum collapses to integer harmonic of f₀
    - Dissonant Codon: Generates ontological friction, suggesting mutation zones
    - Sovereignty Threshold: Ψ ≥ 0.888 indicates stable sequence

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import json
from pathlib import Path
from typing import List, Dict, Tuple, Optional, Any
from dataclasses import dataclass, field
import re
import mpmath as mp

# =============================================================================
# FUNDAMENTAL CONSTANTS
# =============================================================================

F0_FREQUENCY = 141.7001  # Hz - Fundamental quantum frequency
C_COHERENCE = 244.36      # Coherence constant
SOVEREIGNTY_THRESHOLD = 0.888  # Coherence threshold for stability
GYROSCOPY_PRECISION = 0.002  # ΔP ≈ 0.2% quantum gyroscopy prediction

# Base-to-phase mapping (radian phases)
BASE_PHASE_MAP = {
    'A': 0.0,          # Adenine - 0°
    'T': np.pi / 2,    # Thymine - 90°
    'C': np.pi,        # Cytosine - 180°
    'G': 3 * np.pi / 2 # Guanine - 270°
}

# Base-to-amplitude mapping (molecular weight normalized)
BASE_AMPLITUDE_MAP = {
    'A': 1.0,    # Adenine (reference)
    'T': 0.95,   # Thymine
    'C': 0.85,   # Cytosine
    'G': 1.05    # Guanine
}


# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class CodonResonance:
    """Represents the resonance analysis of a DNA codon."""
    sequence: str
    position: int
    riemann_zeros: List[float]
    spectral_sum: float
    harmonic_number: float
    is_resonant: bool
    friction_energy: float
    coherence_local: float
    phase_accumulation: complex
    
    def __str__(self):
        status = "RESONANT ✓" if self.is_resonant else "DISSONANT ✗"
        return (f"Codon {self.sequence} @{self.position}: {status} "
                f"(h={self.harmonic_number:.3f}, Ψ={self.coherence_local:.3f})")


@dataclass
class GenomicField:
    """Results of genomic field analysis."""
    psi_gen: complex
    total_codons: int
    resonant_codons: int
    dissonant_codons: int
    coherence_score: float
    sovereignty_achieved: bool
    mean_amplitude: float


class GenomicZetaMapper:
    """
    Maps genomic codons to Riemann zeros and constructs quantum wave functions.
    
    This class implements the QCAL genomic mapping framework, connecting
    DNA/RNA sequences to the spectral properties of the Riemann zeta function.
    """
    
    def __init__(self, precision: int = 25, zeros_file: Optional[str] = None):
        """
        Initialize the genomic zeta mapper.
        
        Args:
            precision: Decimal precision for mpmath calculations
            zeros_file: Path to file containing Riemann zeros (optional)
        """
        mp.mp.dps = precision
        self.f0 = F0_FREQUENCY
        self.C = C_COHERENCE
        self.kappa_pi = KAPPA_PI
        
        # Load Riemann zeros
        self.riemann_zeros = self._load_riemann_zeros(zeros_file)
        
    def _load_riemann_zeros(self, zeros_file: Optional[str] = None) -> List[mp.mpf]:
        """
        Load Riemann zeros from file or generate default set.
        
        Args:
            zeros_file: Path to zeros file
            
        Returns:
            List of Riemann zeros
        """
        if zeros_file and os.path.exists(zeros_file):
            zeros = []
            with open(zeros_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#'):
                        try:
                            zeros.append(mp.mpf(line))
                        except ValueError:
                            continue
            return zeros
        
        # Default: use first known zeros if no file provided
        default_zeros_path = os.path.join(
            os.path.dirname(os.path.dirname(__file__)), 
            'zeros', 
            'zeros_t1e3.txt'
        )
        
        if os.path.exists(default_zeros_path):
            return self._load_riemann_zeros(default_zeros_path)
        
        # Fallback: hardcoded first 30 zeros
        return [
            mp.mpf("14.134725141735"),
            mp.mpf("21.022039638772"),
            mp.mpf("25.010857580146"),
            mp.mpf("30.424876125860"),
            mp.mpf("32.935061587739"),
            mp.mpf("37.586178158826"),
            mp.mpf("40.918719012147"),
            mp.mpf("43.327073280915"),
            mp.mpf("48.005150881167"),
            mp.mpf("49.773832477672"),
            mp.mpf("52.970321622440"),
            mp.mpf("56.446247697063"),
            mp.mpf("59.347044002602"),
            mp.mpf("60.831778525765"),
            mp.mpf("65.112543928502"),
            mp.mpf("67.079810529495"),
            mp.mpf("69.546401711173"),
            mp.mpf("72.067157674481"),
            mp.mpf("75.704690699083"),
            mp.mpf("77.144840069163"),
            mp.mpf("79.337375020250"),
            mp.mpf("82.910380854086"),
            mp.mpf("84.735492980988"),
            mp.mpf("87.425274612222"),
            mp.mpf("88.809111208753"),
            mp.mpf("92.491899270364"),
            mp.mpf("94.651344040919"),
            mp.mpf("95.870634228221"),
            mp.mpf("98.831194218156"),
            mp.mpf("101.317851005728"),
        ]
    
    def fragment_to_codons(self, sequence: str) -> Tuple[List[Codon], str]:
        """
        Fragment a DNA/RNA sequence into codons (triplets).
        
        Args:
            sequence: DNA or RNA sequence string
            
        Returns:
            Tuple of (list of Codon objects, remaining bases)
            
        Example:
            >>> mapper = GenomicZetaMapper()
            >>> codons, remainder = mapper.fragment_to_codons("AAACGAAAG")
            >>> len(codons)  # 3 complete codons
            3
            >>> remainder  # Empty string (divisible by 3)
            ''
        """
        seq_upper = sequence.upper().replace(' ', '').replace('\n', '')
        
        codons = []
        for i in range(0, len(seq_upper) - 2, 3):
            codon_seq = seq_upper[i:i+3]
            try:
                codon = Codon(sequence=codon_seq, position=i)
                codons.append(codon)
            except ValueError as e:
                # Skip invalid codons
                continue
        
        # Remaining bases that don't form a complete codon
        num_complete_codons = len(codons)
        remainder = seq_upper[num_complete_codons * 3:]
        
        return codons, remainder
    
    def _codon_to_index(self, codon_seq: str) -> int:
        """
        Convert codon sequence to unique index for zero mapping.
        
        Maps each of 64 possible codons to a unique integer.
        
        Args:
            codon_seq: 3-letter codon sequence
            
        Returns:
            Integer index 0-63
        """
        # Map bases to numbers: A/U=0, T=0 (treat U and T same), G=1, C=2
        # Actually for 64 codons, use base-4 encoding
        base_map = {'A': 0, 'T': 1, 'U': 1, 'G': 2, 'C': 3}
        
        index = 0
        for i, base in enumerate(codon_seq):
            index += base_map[base] * (4 ** (2 - i))
        
        return index
    
    def map_codon_to_zeros(self, codon: Codon) -> RiemannZeroTriplet:
        """
        Map a codon to a triplet of Riemann zeros (γᵢ, γⱼ, γₖ).
        
        Uses deterministic mapping based on codon sequence to ensure
        reproducibility and coherence across the genome.
        
        Args:
            codon: Codon object to map
            
        Returns:
            RiemannZeroTriplet assigned to this codon
        """
        # Get base index for this codon
        base_idx = self._codon_to_index(codon.sequence)
        
        # Map to three zeros with spacing to avoid duplicates
        # Use modular arithmetic to wrap around if not enough zeros
        n_zeros = len(self.riemann_zeros)
        
        idx_i = base_idx % n_zeros
        idx_j = (base_idx + 1) % n_zeros
        idx_k = (base_idx + 2) % n_zeros
        
        triplet = RiemannZeroTriplet(
            gamma_i=self.riemann_zeros[idx_i],
            gamma_j=self.riemann_zeros[idx_j],
            gamma_k=self.riemann_zeros[idx_k]
        )
        
        codon.zero_triplet = triplet
        return triplet
    
    def construct_psi_codon(
        self, 
        codon: Codon, 
        t: Union[float, mp.mpf, np.ndarray],
        amplitudes: Optional[Tuple[float, float, float]] = None
    ) -> Union[complex, np.ndarray]:
        """
        Construct quantum wave function Ψ_codon(t) for a codon.
        
        Ψ_codon(t) = A₁ e^(iγᵢt) + A₂ e^(iγⱼt) + A₃ e^(iγₖt)
        
        Args:
            codon: Codon with assigned zero triplet
            t: Time parameter (scalar or array)
            amplitudes: Tuple of (A₁, A₂, A₃) amplitudes (optional)
                       If None, uses equal amplitudes A₁=A₂=A₃=1/√3
        
        Returns:
            Complex wave function value(s) at time t
        """
        if codon.zero_triplet is None:
            self.map_codon_to_zeros(codon)
        
        # Default: equal amplitudes normalized to 1
        if amplitudes is None:
            A1 = A2 = A3 = 1.0 / np.sqrt(3)
        else:
            A1, A2, A3 = amplitudes
        
        # Get zeros
        gamma_i = float(codon.zero_triplet.gamma_i)
        gamma_j = float(codon.zero_triplet.gamma_j)
        gamma_k = float(codon.zero_triplet.gamma_k)
        
        # Handle both scalar and array inputs
        is_array = isinstance(t, np.ndarray)
        t_val = t if is_array else float(t)
        
        # Construct wave function
        psi = (A1 * np.exp(1j * gamma_i * t_val) +
               A2 * np.exp(1j * gamma_j * t_val) +
               A3 * np.exp(1j * gamma_k * t_val))
        
        return psi
    
    def classify_codon_resonance(self, codon: Codon, t: float = 0.0) -> CodonType:
        """
        Classify codon as resonant, dissonant, or neutral based on Ψ amplitude.
        
        Resonant codons have high coherence with f₀ fundamental frequency.
        
        Args:
            codon: Codon to classify
            t: Time point for evaluation (default 0.0)
            
        Returns:
            CodonType classification
        """
        # Construct wave function at t=0
        psi = self.construct_psi_codon(codon, t)
        amplitude = abs(psi)
        
        codon.psi_amplitude = amplitude
        
        # Classification thresholds based on QCAL coherence
        # High coherence: |Ψ| > 0.888 (sovereignty threshold)
        # Low coherence: |Ψ| < 0.5
        if amplitude >= float(SOVEREIGNTY_THRESHOLD):
            codon_type = CodonType.RESONANT
        elif amplitude < 0.5:
            codon_type = CodonType.DISSONANT
        else:
            codon_type = CodonType.NEUTRAL
        
        codon.codon_type = codon_type
        return codon_type
    
    def compute_genomic_field(
        self, 
        codons: List[Codon],
        t: float = 0.0
    ) -> GenomicField:
        """
        Compute overall genomic field Ψ_Gen(t) from all codons.
        
        The genomic field is the coherent superposition of all codon
        wave functions, representing the quantum state of the genome.
        
        Ψ_Gen(t) = Σᵢ Ψ_codon_i(t)
        
        Args:
            codons: List of Codon objects
            t: Time parameter
            
        Returns:
            GenomicField analysis results
        """
        if not codons:
            return GenomicField(
                psi_gen=0+0j,
                total_codons=0,
                resonant_codons=0,
                dissonant_codons=0,
                coherence_score=0.0,
                sovereignty_achieved=False,
                mean_amplitude=0.0
            )
        
        # Compute wave function for each codon and sum
        psi_gen = 0+0j
        amplitudes = []
        resonant = 0
        dissonant = 0
        
        for codon in codons:
            psi = self.construct_psi_codon(codon, t)
            psi_gen += psi
            
            amp = abs(psi)
            amplitudes.append(amp)
            
            # Classify if not already done
            if codon.codon_type is None:
                self.classify_codon_resonance(codon, t)
            
            if codon.codon_type == CodonType.RESONANT:
                resonant += 1
            elif codon.codon_type == CodonType.DISSONANT:
                dissonant += 1
        
        # Normalize by number of codons
        psi_gen_normalized = psi_gen / len(codons)
        
        # Calculate coherence metrics
        mean_amplitude = np.mean(amplitudes)
        coherence_score = abs(psi_gen_normalized)
        sovereignty_achieved = coherence_score >= float(SOVEREIGNTY_THRESHOLD)
        
        return GenomicField(
            psi_gen=psi_gen_normalized,
            total_codons=len(codons),
            resonant_codons=resonant,
            dissonant_codons=dissonant,
            coherence_score=coherence_score,
            sovereignty_achieved=sovereignty_achieved,
            mean_amplitude=mean_amplitude
        )
    
    def analyze_sequence(self, sequence: str, t: float = 0.0) -> Dict:
        """
        Comprehensive analysis of a DNA/RNA sequence.
        
        Args:
            sequence: DNA or RNA sequence string
            t: Time parameter for wave function evaluation
            
        Returns:
            Dictionary with complete analysis results
        """
        # Fragment into codons
        codons, remainder = self.fragment_to_codons(sequence)
        
        # Map each codon to zeros
        for codon in codons:
            self.map_codon_to_zeros(codon)
            self.classify_codon_resonance(codon, t)
        
        # Compute genomic field
        field = self.compute_genomic_field(codons, t)
        
        # Compile results
        results = {
            'sequence_length': len(sequence),
            'codons': [
                {
                    'sequence': c.sequence,
                    'position': c.position,
                    'zeros': [float(z) for z in c.zero_triplet.to_list()],
                    'type': c.codon_type.value,
                    'amplitude': c.psi_amplitude
                }
                for c in codons
            ],
            'remainder_bases': remainder,
            'genomic_field': {
                'psi_magnitude': abs(field.psi_gen),
                'psi_phase': np.angle(field.psi_gen),
                'total_codons': field.total_codons,
                'resonant_codons': field.resonant_codons,
                'dissonant_codons': field.dissonant_codons,
                'neutral_codons': field.total_codons - field.resonant_codons - field.dissonant_codons,
                'coherence_score': field.coherence_score,
                'sovereignty_achieved': field.sovereignty_achieved,
                'mean_amplitude': field.mean_amplitude
            },
            'qcal_constants': {
                'f0': float(self.f0),
                'C': float(self.C),
                'kappa_pi': float(self.kappa_pi),
                'sovereignty_threshold': float(SOVEREIGNTY_THRESHOLD)
            }
        }
        
        return results


def predict_mutation_stability(
    original_seq: str,
    mutated_seq: str,
    mapper: Optional[GenomicZetaMapper] = None
) -> Dict:
    """
    Predict mutation stability using quantum gyroscopy (ΔP≈0.2%).
    
    Analyzes genomic chirality via torsion tensor, identifies mutation
    hotspots based on ontological friction from dissonant codons.
    
    Args:
        original_seq: Original DNA/RNA sequence
        mutated_seq: Mutated sequence
        mapper: GenomicZetaMapper instance (creates new if None)
        
    Returns:
        Dictionary with mutation stability analysis
    """
    if mapper is None:
        mapper = GenomicZetaMapper()
    
    # Analyze both sequences
    original_analysis = mapper.analyze_sequence(original_seq)
    mutated_analysis = mapper.analyze_sequence(mutated_seq)
    
    # Calculate stability change
    orig_coherence = original_analysis['genomic_field']['coherence_score']
    mut_coherence = mutated_analysis['genomic_field']['coherence_score']
    
    delta_coherence = mut_coherence - orig_coherence
    stability_preserved = abs(delta_coherence) < 0.002  # ΔP ≈ 0.2%
    
    # Identify mutation hotspots (positions with large coherence change)
    hotspots = []
    for i, (orig_codon, mut_codon) in enumerate(
        zip(original_analysis['codons'], mutated_analysis['codons'])
    ):
        if orig_codon['sequence'] != mut_codon['sequence']:
            delta_amp = mut_codon['amplitude'] - orig_codon['amplitude']
            if abs(delta_amp) > 0.1:
                hotspots.append({
                    'position': orig_codon['position'],
                    'original': orig_codon['sequence'],
                    'mutated': mut_codon['sequence'],
                    'delta_amplitude': delta_amp,
                    'ontological_friction': abs(delta_amp) > 0.2
                })
    
    return {
        'original_coherence': orig_coherence,
        'mutated_coherence': mut_coherence,
        'delta_coherence': delta_coherence,
        'delta_percent': delta_coherence / orig_coherence * 100 if orig_coherence != 0 else 0,
        'stability_preserved': stability_preserved,
        'mutation_hotspots': hotspots,
        'gyroscopic_precision': 0.002,  # ΔP ≈ 0.2%
    }


# Main demo function
if __name__ == "__main__":
    # Example sequence from the problem statement
    sequence = "AAACGAAAGGGAAAAAAACAAAAAGGCAAGGAAGAAAAAAGAAAAAAACGCCAAAAAACGCAAAA"
    
    print("=" * 70)
    print("Genomic Zeta Mapping: DNA Codons → Riemann Zeros")
    print("=" * 70)
    print(f"\nSequence: {sequence}")
    print(f"Length: {len(sequence)} bases")
    
    # Initialize mapper
    mapper = GenomicZetaMapper(precision=25)
    print(f"\nLoaded {len(mapper.riemann_zeros)} Riemann zeros")
    
    # Analyze sequence
    results = mapper.analyze_sequence(sequence, t=0.0)
    
    # Display codon fragmentation
    print(f"\n{'='*70}")
    print("Codon Fragmentation:")
    print(f"{'='*70}")
    print(f"Total codons: {len(results['codons'])}")
    print(f"Remainder: {results['remainder_bases']} ({len(results['remainder_bases'])} bases)")
    
    print("\nCodons and their Riemann zero triplets:")
    for i, codon_data in enumerate(results['codons'][:10]):  # Show first 10
        zeros = codon_data['zeros']
        print(f"  {i+1}. {codon_data['sequence']} → "
              f"(γ₁={zeros[0]:.4f}, γ₂={zeros[1]:.4f}, γ₃={zeros[2]:.4f}) "
              f"[{codon_data['type']}]")
    
    if len(results['codons']) > 10:
        print(f"  ... and {len(results['codons']) - 10} more codons")
    
    # Display genomic field
    print(f"\n{'='*70}")
    print("Genomic Field Ψ_Gen(t=0):")
    print(f"{'='*70}")
    field = results['genomic_field']
    print(f"  Coherence: {field['coherence_score']:.6f}")
    print(f"  Sovereignty: {'✓ ACHIEVED' if field['sovereignty_achieved'] else '✗ Not achieved'}")
    print(f"  Resonant codons: {field['resonant_codons']}/{field['total_codons']}")
    print(f"  Dissonant codons: {field['dissonant_codons']}/{field['total_codons']}")
    print(f"  Neutral codons: {field['neutral_codons']}/{field['total_codons']}")
    print(f"  Mean amplitude: {field['mean_amplitude']:.6f}")
    
    # Display QCAL constants
    print(f"\n{'='*70}")
    print("QCAL ∞³ Constants:")
    print(f"{'='*70}")
    qcal = results['qcal_constants']
    print(f"  f₀ = {qcal['f0']} Hz")
    print(f"  C = {qcal['C']}")
    print(f"  κ_Π = {qcal['kappa_pi']}")
    print(f"  Sovereignty threshold = {qcal['sovereignty_threshold']}")
    
    print(f"\n{'='*70}")
    print("✓ Genomic-Zeta mapping complete")
    print(f"{'='*70}\n")
    """Complete genomic field analysis for a DNA sequence."""
    sequence: str
    length: int
    num_codons: int
    codons: List[CodonResonance] = field(default_factory=list)
    psi_gen: complex = 0j
    total_coherence: float = 0.0
    sovereignty_score: float = 0.0
    is_sovereign: bool = False
    resonant_count: int = 0
    dissonant_count: int = 0
    mutation_hotspots: List[int] = field(default_factory=list)
    torsion_tensor: np.ndarray = field(default_factory=lambda: np.zeros((3, 3)))
    
    def summary(self) -> str:
        """Generate a human-readable summary."""
        return f"""
╔═══════════════════════════════════════════════════════════════╗
║              GENOMIC ZETA FIELD ANALYSIS                      ║
║              QCAL ∞³ · 141.7001 Hz                           ║
╠═══════════════════════════════════════════════════════════════╣
║ Sequence Length: {self.length:>5} bp                              ║
║ Codons Analyzed: {self.num_codons:>5}                               ║
║                                                               ║
║ Resonant Codons: {self.resonant_count:>5} ({100*self.resonant_count/max(1,self.num_codons):>5.1f}%)                  ║
║ Dissonant Codons: {self.dissonant_count:>5} ({100*self.dissonant_count/max(1,self.num_codons):>5.1f}%)                 ║
║                                                               ║
║ Total Coherence Ψ: {self.total_coherence:>8.6f}                        ║
║ Sovereignty Score: {self.sovereignty_score:>8.6f}                        ║
║ Status: {("SOVEREIGN & STABLE ✓" if self.is_sovereign else "UNSTABLE ✗"):>22}                     ║
║                                                               ║
║ Mutation Hotspots: {len(self.mutation_hotspots):>5} zones detected                  ║
╚═══════════════════════════════════════════════════════════════╝
"""


# =============================================================================
# RIEMANN ZEROS LOADING
# =============================================================================

class RiemannZerosCache:
    """Cache for Riemann zeta zeros with lazy loading."""
    
    def __init__(self):
        self.zeros: Optional[List[float]] = None
        self._loaded = False
    
    def load_zeros(self) -> List[float]:
        """Load Riemann zeros from data file."""
        if self._loaded and self.zeros is not None:
            return self.zeros
        
        # Try loading from JSON file first
        json_path = Path(__file__).parent.parent / "data" / "zeta_zeros.json"
        if json_path.exists():
            with open(json_path, 'r') as f:
                data = json.load(f)
                self.zeros = [float(z) for z in data.get('zeros', [])]
                self._loaded = True
                return self.zeros
        
        # Fallback: try zeros directory
        zeros_path = Path(__file__).parent.parent / "zeros" / "zeros_t1e3.txt"
        if zeros_path.exists():
            with open(zeros_path, 'r') as f:
                self.zeros = [float(line.strip()) for line in f if line.strip()]
                self._loaded = True
                return self.zeros
        
        # Last resort: use first 100 hardcoded zeros
        self.zeros = self._get_hardcoded_zeros()
        self._loaded = True
        return self.zeros
    
    def _get_hardcoded_zeros(self) -> List[float]:
        """Hardcoded first 100 Riemann zeros for fallback."""
        return [
            14.134725141735, 21.022039638772, 25.010857580146, 30.42487612586,
            32.935061587739, 37.586178158826, 40.918719012147, 43.327073280915,
            48.005150881167, 49.773832477672, 52.970321477714, 56.446247697064,
            59.347044002602, 60.831778524609, 65.112544048313, 67.079810528525,
            69.546401711224, 72.067157674481, 75.704690699083, 77.144840068875,
            79.337375020249, 82.910380854086, 84.735492980522, 87.425274613125,
            88.809111207764, 92.491899270534, 94.651344040519, 95.870634228248,
            98.831194218193, 101.317851006168, 103.725538039798, 105.446623052663,
            107.168611184261, 111.029535543105, 111.874659177093, 114.320220915271,
            116.226680321515, 118.790782866616, 121.370125002205, 122.946829294073,
            124.256818554714, 127.516683880278, 129.578704200766, 131.087688531177,
            133.497737203887, 134.756509753801, 138.116042055046, 139.736208952163,
            141.123707404403, 143.111845807366, 146.000982487000, 147.422765343202,
            150.053520421580, 150.925257612668, 153.024693811831, 156.112909294263,
            157.597591818046, 158.849988171308, 161.188964138938, 163.030709687604,
            165.537069680321, 167.184439978028, 169.094515416340, 169.911975931063,
            172.678689304844, 173.411536520172, 176.441434298875, 178.377407775833,
            179.916484769734, 182.207078484927, 184.874467848220, 185.598783678185,
            187.228922584490, 189.416158656042, 192.026656361709, 193.079726604243,
            195.265396680009, 196.876481841508, 198.015309676125, 201.264751944548,
            202.493594514547, 204.189671803208, 205.394697876691, 207.906258888890,
            209.576509717673, 211.690862595036, 213.347919360349, 214.547044783534,
            216.169538508155, 219.067596349491, 220.714918839880, 221.430705555051,
            224.007000255654, 224.983324670359, 227.421444280583, 229.337413306555
        ]


# Global cache instance
_zeros_cache = RiemannZerosCache()


# =============================================================================
# CORE MAPPING FUNCTIONS
# =============================================================================

def select_riemann_zero_for_base(base: str, position_in_codon: int, 
                                  codon_index: int) -> float:
    """
    Select a Riemann zero for a given DNA base.
    
    The selection uses a deterministic mapping based on:
    - Base identity (A, T, C, G)
    - Position within codon (0, 1, 2)
    - Codon index in sequence
    
    Args:
        base: DNA base ('A', 'T', 'C', or 'G')
        position_in_codon: Position in codon (0, 1, or 2)
        codon_index: Index of codon in sequence
        
    Returns:
        Selected Riemann zero (imaginary part γ)
    """
    zeros = _zeros_cache.load_zeros()
    
    # Map base to offset
    base_offset = {'A': 0, 'T': 1, 'C': 2, 'G': 3}[base.upper()]
    
    # Deterministic index calculation
    # Uses position, codon index, and base type for unique but deterministic selection
    index = (codon_index * 3 + position_in_codon + base_offset * 13) % len(zeros)
    
    return zeros[index]


def compute_codon_spectral_sum(bases: str, codon_index: int) -> Tuple[List[float], float]:
    """
    Compute spectral sum for a codon by selecting and combining Riemann zeros.
    
    Args:
        bases: 3-character string representing codon (e.g., "ATG")
        codon_index: Index of codon in sequence
        
    Returns:
        Tuple of (selected_zeros, spectral_sum)
    """
    if len(bases) != 3:
        raise ValueError(f"Codon must be 3 bases, got {len(bases)}")
    
    zeros = []
    for i, base in enumerate(bases.upper()):
        zero = select_riemann_zero_for_base(base, i, codon_index)
        zeros.append(zero)
    
    # Spectral sum: weighted average with phase consideration
    spectral_sum = sum(zeros) / 3.0
    
    return zeros, spectral_sum


def classify_codon_resonance(spectral_sum: float, tolerance: float = 0.1) -> Tuple[bool, float, float]:
    """
    Classify codon as resonant or dissonant based on spectral sum.
    
    A codon is resonant if its spectral sum is close to an integer
    harmonic of the fundamental frequency f₀ = 141.7001 Hz.
    
    Args:
        spectral_sum: Spectral sum from Riemann zeros
        tolerance: Tolerance for resonance matching (default: 0.1)
        
    Returns:
        Tuple of (is_resonant, harmonic_number, friction_energy)
    """
    # Normalize to f₀ scale
    normalized_freq = spectral_sum / F0_FREQUENCY
    
    # Find nearest integer harmonic
    harmonic_number = round(normalized_freq)
    
    # Calculate deviation from perfect harmonic
    deviation = abs(normalized_freq - harmonic_number)
    
    # Resonance check
    is_resonant = deviation < tolerance
    
    # Friction energy: ontological friction for dissonant codons
    # Increases with deviation from harmonic
    friction_energy = deviation * C_COHERENCE if not is_resonant else 0.0
    
    return is_resonant, harmonic_number, friction_energy


def compute_codon_field(bases: str, codon_index: int, t: float = 0.0) -> complex:
    """
    Compute the quantum field contribution of a single codon.
    
    Ψ_codon(t) = Σ_{k=1}^3 A_k * e^(i*γ_{n_k}*t + φ_k)
    
    Args:
        bases: 3-character codon string
        codon_index: Index of codon in sequence
        t: Time parameter (default: 0)
        
    Returns:
        Complex field value
    """
    psi_codon = 0j
    
    for i, base in enumerate(bases.upper()):
        # Get Riemann zero
        gamma = select_riemann_zero_for_base(base, i, codon_index)
        
        # Get amplitude and phase
        amplitude = BASE_AMPLITUDE_MAP.get(base, 1.0)
        phase = BASE_PHASE_MAP.get(base, 0.0)
        
        # Compute field contribution: A * e^(i*γ*t + φ)
        contribution = amplitude * np.exp(1j * (gamma * t + phase))
        psi_codon += contribution
    
    return psi_codon


def analyze_codon(bases: str, position: int, codon_index: int) -> CodonResonance:
    """
    Perform complete resonance analysis of a single codon.
    
    Args:
        bases: 3-character codon string
        position: Nucleotide position in sequence
        codon_index: Index of codon
        
    Returns:
        CodonResonance object with complete analysis
    """
    # Select Riemann zeros and compute spectral sum
    zeros, spectral_sum = compute_codon_spectral_sum(bases, codon_index)
    
    # Classify resonance
    is_resonant, harmonic_number, friction = classify_codon_resonance(spectral_sum)
    
    # Compute quantum field
    psi_codon = compute_codon_field(bases, codon_index)
    
    # Local coherence: magnitude normalized
    coherence_local = abs(psi_codon) / 3.0  # Normalized by max amplitude sum
    
    return CodonResonance(
        sequence=bases.upper(),
        position=position,
        riemann_zeros=zeros,
        spectral_sum=spectral_sum,
        harmonic_number=harmonic_number,
        is_resonant=is_resonant,
        friction_energy=friction,
        coherence_local=coherence_local,
        phase_accumulation=psi_codon
    )


# =============================================================================
# ORF DETECTION
# =============================================================================

def find_orfs(sequence: str, min_length: int = 30) -> List[Tuple[int, int, int]]:
    """
    Find Open Reading Frames (ORFs) in DNA sequence.
    
    Searches for ORFs starting with ATG (start codon) and ending with
    TAA, TAG, or TGA (stop codons).
    
    Args:
        sequence: DNA sequence string
        min_length: Minimum ORF length in nucleotides (default: 30)
        
    Returns:
        List of tuples (start_pos, end_pos, frame) for each ORF
    """
    sequence = sequence.upper()
    stop_codons = {'TAA', 'TAG', 'TGA'}
    start_codon = 'ATG'
    orfs = []
    
    # Check all three reading frames
    for frame in range(3):
        i = frame
        while i < len(sequence) - 2:
            codon = sequence[i:i+3]
            
            if codon == start_codon:
                # Found start codon, look for stop
                j = i + 3
                while j < len(sequence) - 2:
                    stop_codon = sequence[j:j+3]
                    if stop_codon in stop_codons:
                        # Found complete ORF
                        if (j + 3 - i) >= min_length:
                            orfs.append((i, j + 3, frame))
                        break
                    j += 3
            
            i += 3
    
    return orfs


# =============================================================================
# GENOMIC FIELD ANALYSIS
# =============================================================================

def analyze_genomic_field(sequence: str, 
                          use_orfs: bool = False,
                          min_orf_length: int = 30) -> GenomicField:
    """
    Perform complete genomic field analysis on DNA sequence.
    
    This is the main analysis function that:
    1. Optionally identifies ORFs
    2. Segments sequence into codons
    3. Assigns Riemann zeros to each codon
    4. Computes resonance/dissonance classification
    5. Calculates total genomic field Ψ_Gen
    6. Determines sovereignty and mutation hotspots
    
    Args:
        sequence: DNA sequence string (A, T, C, G)
        use_orfs: If True, analyze only ORFs (default: False)
        min_orf_length: Minimum ORF length if use_orfs=True
        
    Returns:
        GenomicField object with complete analysis
    """
    sequence = sequence.upper().replace(' ', '').replace('\n', '')
    
    # Validate sequence
    valid_bases = set('ATCG')
    if not all(base in valid_bases for base in sequence):
        raise ValueError("Sequence contains invalid bases (only A, T, C, G allowed)")
    
    # Determine analysis regions
    if use_orfs:
        orfs = find_orfs(sequence, min_orf_length)
        if not orfs:
            # No ORFs found, analyze entire sequence
            regions = [(0, len(sequence), 0)]
        else:
            regions = orfs
    else:
        # Analyze entire sequence
        regions = [(0, len(sequence), 0)]
    
    # Analyze all codons
    all_codons = []
    psi_total = 0j
    resonant_count = 0
    dissonant_count = 0
    mutation_hotspots = []
    
    codon_index = 0
    for start, end, frame in regions:
        region_seq = sequence[start:end]
        
        # Process in codons
        for i in range(0, len(region_seq) - 2, 3):
            codon_bases = region_seq[i:i+3]
            if len(codon_bases) == 3:
                position = start + i
                codon = analyze_codon(codon_bases, position, codon_index)
                all_codons.append(codon)
                
                # Accumulate field
                psi_total += codon.phase_accumulation
                
                # Count resonance types
                if codon.is_resonant:
                    resonant_count += 1
                else:
                    dissonant_count += 1
                    # Mark as potential mutation hotspot if high friction
                    if codon.friction_energy > C_COHERENCE * 0.5:
                        mutation_hotspots.append(position)
                
                codon_index += 1
    
    # Calculate metrics
    num_codons = len(all_codons)
    
    # Total coherence: normalized field magnitude
    if num_codons > 0:
        total_coherence = abs(psi_total) / (num_codons * 3)
    else:
        total_coherence = 0.0
    
    # Sovereignty score: coherence weighted by resonance ratio
    if num_codons > 0:
        resonance_ratio = resonant_count / num_codons
        sovereignty_score = total_coherence * (0.5 + 0.5 * resonance_ratio)
    else:
        sovereignty_score = 0.0
    
    # Sovereignty check
    is_sovereign = sovereignty_score >= SOVEREIGNTY_THRESHOLD
    
    # Compute torsion tensor (3x3 representing spatial torsion)
    torsion_tensor = compute_torsion_tensor(all_codons)
    
    return GenomicField(
        sequence=sequence,
        length=len(sequence),
        num_codons=num_codons,
        codons=all_codons,
        psi_gen=psi_total,
        total_coherence=total_coherence,
        sovereignty_score=sovereignty_score,
        is_sovereign=is_sovereign,
        resonant_count=resonant_count,
        dissonant_count=dissonant_count,
        mutation_hotspots=mutation_hotspots,
        torsion_tensor=torsion_tensor
    )


def compute_torsion_tensor(codons: List[CodonResonance]) -> np.ndarray:
    """
    Compute the torsion tensor from codon field analysis.
    
    The torsion tensor T captures the geometric torsion of the
    genomic field in 3D space.
    
    Args:
        codons: List of analyzed codons
        
    Returns:
        3x3 torsion tensor
    """
    if not codons:
        return np.zeros((3, 3))
    
    T = np.zeros((3, 3), dtype=complex)
    
    for idx, codon in enumerate(codons):
        # Map codon to 3D vector based on zero distribution
        if len(codon.riemann_zeros) >= 3:
            v = np.array(codon.riemann_zeros[:3])
            # Normalize
            v = v / np.linalg.norm(v)
            
            # Accumulate outer product weighted by phase
            weight = codon.phase_accumulation
            T += weight * np.outer(v, v)
    
    # Normalize
    T = T / max(1, len(codons))
    
    # Return real part (torsion is geometrically real)
    return np.real(T)


# =============================================================================
# MUTATION ANALYSIS
# =============================================================================

def predict_mutation_stability(field: GenomicField) -> Dict[str, Any]:
    """
    Predict mutation stability using Quantum Gyroscopy (ΔP ≈ 0.2%).
    
    Analyzes the genomic field to identify zones of high mutation
    probability based on quantum mechanical chirality and torsion.
    
    Args:
        field: GenomicField analysis result
        
    Returns:
        Dictionary with mutation predictions
    """
    # Calculate chirality from torsion tensor
    chirality = np.trace(field.torsion_tensor)
    
    # Gyroscopic prediction: deviation from ideal chirality
    ideal_chirality = 1.0  # Perfect alignment
    chirality_deviation = abs(chirality - ideal_chirality)
    
    # Mutation probability
    mutation_probability = min(1.0, chirality_deviation * GYROSCOPY_PRECISION / 0.002)
    
    # Stability assessment
    is_stable = mutation_probability < 0.1  # < 10% mutation probability
    
    # Analyze hotspot distribution
    hotspot_density = len(field.mutation_hotspots) / max(1, field.length) * 100
    
    return {
        'chirality': float(chirality),
        'chirality_deviation': float(chirality_deviation),
        'mutation_probability': float(mutation_probability),
        'is_stable': bool(is_stable),
        'hotspot_count': int(len(field.mutation_hotspots)),
        'hotspot_density_percent': float(hotspot_density),
        'prediction_precision': float(GYROSCOPY_PRECISION)
    }


# =============================================================================
# EXPORT AND VISUALIZATION
# =============================================================================

def export_analysis(field: GenomicField, 
                    output_path: Optional[str] = None) -> Dict:
    """
    Export genomic field analysis to dictionary format.
    
    Args:
        field: GenomicField analysis result
        output_path: Optional path to save JSON file
        
    Returns:
        Dictionary with complete analysis
    """
    # Mutation prediction
    mutation_analysis = predict_mutation_stability(field)
    
    result = {
        'qcal_version': '∞³',
        'frequency_f0': float(F0_FREQUENCY),
        'coherence_c': float(C_COHERENCE),
        'sequence': {
            'length': int(field.length),
            'num_codons': int(field.num_codons)
        },
        'metrics': {
            'psi_gen_magnitude': float(abs(field.psi_gen)),
            'psi_gen_phase': float(np.angle(field.psi_gen)),
            'total_coherence': float(field.total_coherence),
            'sovereignty_score': float(field.sovereignty_score),
            'is_sovereign': bool(field.is_sovereign),
            'sovereignty_threshold': float(SOVEREIGNTY_THRESHOLD)
        },
        'codons': {
            'resonant_count': int(field.resonant_count),
            'dissonant_count': int(field.dissonant_count),
            'resonant_percent': float(100 * field.resonant_count / max(1, field.num_codons)),
            'dissonant_percent': float(100 * field.dissonant_count / max(1, field.num_codons))
        },
        'mutation_analysis': mutation_analysis,
        'torsion_tensor': field.torsion_tensor.tolist(),
        'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
        'institution': 'Instituto de Conciencia Cuántica (ICQ)',
        'doi': '10.5281/zenodo.17379721'
    }
    
    if output_path:
        with open(output_path, 'w') as f:
            json.dump(result, f, indent=2)
    
    return result


# =============================================================================
# MAIN EXECUTION
# =============================================================================

if __name__ == "__main__":
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║         GENOMIC ZETA MAPPING - Gen→Zeta Framework            ║")
    print("║                   QCAL ∞³ · 141.7001 Hz                      ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    
    # Example: Analyze a sample DNA sequence
    # Human β-globin gene fragment (start of coding sequence)
    sample_dna = """
    ATGGTGCATCTGACTCCTGAGGAGAAGTCTGCCGTTACTGCCCTGTGGGGCAAGGTGAACGTGGATGAAGTTGGTGGTGAGGCCCTGGGCAGG
    TTGGTATCAAGGTTACAAGACAGGTTTAAGGAGACCAATAGAAACTGGGCATGTGGAGACAGAGAAGACTCTTGGGTTTCTGATAGGCACTGAC
    """
    
    # Clean sequence
    sample_dna = sample_dna.replace('\n', '').replace(' ', '').upper()
    
    print(f"Analyzing sequence ({len(sample_dna)} bp)...")
    print()
    
    # Perform analysis
    field = analyze_genomic_field(sample_dna, use_orfs=True)
    
    # Display results
    print(field.summary())
    
    # Show first few codons
    print("\nFirst 10 Codons:")
    print("─" * 80)
    for i, codon in enumerate(field.codons[:10]):
        print(codon)
    
    if len(field.codons) > 10:
        print(f"... ({len(field.codons) - 10} more codons)")
    
    # Mutation analysis
    print("\n" + "═" * 80)
    print("MUTATION STABILITY ANALYSIS (Quantum Gyroscopy ΔP ≈ 0.2%)")
    print("═" * 80)
    mutation_pred = predict_mutation_stability(field)
    print(f"Chirality: {mutation_pred['chirality']:.6f}")
    print(f"Mutation Probability: {mutation_pred['mutation_probability']*100:.2f}%")
    print(f"Stability: {'STABLE ✓' if mutation_pred['is_stable'] else 'UNSTABLE ✗'}")
    print(f"Mutation Hotspots: {mutation_pred['hotspot_count']} ({mutation_pred['hotspot_density_percent']:.3f}% of sequence)")
    
    # Export analysis
    output_file = "genomic_field_analysis.json"
    export_analysis(field, output_file)
    print(f"\n✓ Analysis exported to {output_file}")
    
    print("\n" + "═" * 80)
    print('"La biología es el eco de la función Zeta en la materia."')
    print("José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("═" * 80)
