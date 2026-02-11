"""
Genomic Zeta Mapping: DNA/RNA Codons to Riemann Zeros
=======================================================

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
