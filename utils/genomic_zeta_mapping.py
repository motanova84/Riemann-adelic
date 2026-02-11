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
