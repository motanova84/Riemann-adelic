#!/usr/bin/env python3
"""
ADN-Riemann: DNA Resonance Mapping
===================================

Maps DNA sequences to Riemann zero resonances and analyzes mutations
in the QCAL ∞³ framework at f₀ = 141.7001 Hz.

Mathematical Foundation:
    Each DNA base encodes a phase:
        A → 0°, T → 90°, G → 180°, C → 270°
    
    Resonance for sequence S:
        R(S) = |Σ_i exp(i·θ_i·γ_i/f₀)| / N
    
    where γ_i are Riemann zeros and θ_i are base phases.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import warnings
import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from enum import Enum

# Try to import mpmath for high precision
try:
    import mpmath as mp
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    warnings.warn("mpmath no disponible. Usando aproximaciones limitadas.")

# =============================================================================
# QCAL CONSTANTS
# =============================================================================

F0_QCAL = 141.7001  # Hz - Fundamental quantum frequency
C_COHERENCE = 244.36  # Coherence constant
RESONANCE_THRESHOLD = 0.5  # Threshold for beneficial mutation

# First 30 Riemann zeros (imaginary parts)
RIEMANN_ZEROS = [
    14.134725141735, 21.022039638772, 25.010857580146, 30.424876125860,
    32.935061587739, 37.586178158826, 40.918719012147, 43.327073280915,
    48.005150881167, 49.773832477672, 52.970321477715, 56.446247697064,
    59.347044002602, 60.831778524611, 65.112544048920, 67.079810528841,
    69.546401711229, 72.067157674894, 75.704690699083, 77.144840069163,
    79.337375020250, 82.910380854086, 84.735524736997, 87.425274613125,
    88.809111208594, 92.491899270558, 94.651344040681, 95.870634228249,
    98.831194218224, 101.317851005728
]

# Base-to-phase mapping (radians)
BASE_PHASE = {
    'A': 0.0,              # Adenine - 0°
    'T': np.pi / 2,        # Thymine - 90°
    'G': np.pi,            # Guanine - 180°
    'C': 3 * np.pi / 2     # Cytosine - 270°
}

# Valid DNA bases
VALID_BASES = set('ATGC')


# =============================================================================
# MUTATION TYPES
# =============================================================================

class MutationType(Enum):
    """Types of DNA mutations."""
    SUBSTITUTION = "sustitución"
    INSERTION = "inserción"
    DELETION = "deleción"


# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class DNAResonance:
    """Resonance analysis of a DNA sequence."""
    sequence: str
    resonance: float
    phase_vector: np.ndarray
    coherence: float
    
    def __str__(self):
        return f"DNA({self.sequence}): R={self.resonance:.6f}, Ψ={self.coherence:.6f}"


@dataclass
class Mutation:
    """Represents a DNA mutation."""
    original: str
    mutated: str
    position: int
    mutation_type: MutationType
    score: float
    delta_resonance: float
    is_beneficial: bool
    
    def __str__(self):
        return (f"{self.original} → {self.mutated} (pos={self.position}, "
                f"tipo={self.mutation_type.value})")


# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def validate_sequence(sequence: str) -> bool:
    """
    Validate DNA sequence contains only ATGC bases.
    
    Args:
        sequence: DNA sequence string
        
    Returns:
        True if valid, False otherwise
    """
    return all(base in VALID_BASES for base in sequence.upper())


def calculate_resonance(sequence: str) -> float:
    """
    Calculate resonance score for DNA sequence.
    
    Uses Riemann zeros as frequency components modulated by base phases.
    The resonance measures how well the sequence aligns with f₀ = 141.7001 Hz
    through constructive interference of base-encoded phases.
    
    Args:
        sequence: DNA sequence (A, T, G, C)
        
    Returns:
        Resonance score in range [0, 1]
    """
    if not sequence:
        return 0.0
    
    sequence = sequence.upper()
    n = len(sequence)
    
    # Calculate phase accumulation with Riemann zero modulation
    # Each base contributes a phase rotated by its corresponding zero
    phase_sum = 0.0 + 0.0j
    
    for i, base in enumerate(sequence):
        if base not in BASE_PHASE:
            continue
        
        # Base phase (0, π/2, π, 3π/2)
        theta = BASE_PHASE[base]
        
        # Riemann zero for this position
        zero_idx = i % len(RIEMANN_ZEROS)
        gamma = RIEMANN_ZEROS[zero_idx]
        
        # Phase modulation: combine base phase with zero-derived frequency
        # The key is that certain combinations resonate with f₀
        omega = 2 * np.pi * gamma / F0_QCAL
        modulated_phase = theta + omega / (2 * np.pi)
        
        # Accumulate with exponential weights favoring beginning of sequence
        position_weight = np.exp(-0.1 * i)  # Decay factor
        phase_sum += position_weight * np.exp(1j * modulated_phase)
    
    # Resonance is the normalized magnitude
    # Normalize by theoretical maximum (all phases aligned)
    if n > 0:
        # Theoretical maximum when all phases align
        max_possible = sum(np.exp(-0.1 * i) for i in range(n))
        resonance = abs(phase_sum) / max_possible if max_possible > 0 else 0.0
    else:
        resonance = 0.0
    
    return float(resonance)


def generate_mutations(sequence: str) -> List[Mutation]:
    """
    Generate all single-base mutations for a sequence.
    
    Args:
        sequence: Original DNA sequence
        
    Returns:
        List of Mutation objects
    """
    mutations = []
    original_resonance = calculate_resonance(sequence)
    bases = list(VALID_BASES)
    
    # Substitutions: replace each base with each other base
    for i, original_base in enumerate(sequence):
        for new_base in bases:
            if new_base == original_base:
                continue
            
            mutated = sequence[:i] + new_base + sequence[i+1:]
            mutated_resonance = calculate_resonance(mutated)
            delta = mutated_resonance - original_resonance
            score = mutated_resonance
            
            mutation = Mutation(
                original=sequence,
                mutated=mutated,
                position=i,
                mutation_type=MutationType.SUBSTITUTION,
                score=score,
                delta_resonance=delta,
                is_beneficial=(delta > 0 and score > RESONANCE_THRESHOLD)
            )
            mutations.append(mutation)
    
    # Insertions: insert each base at each position
    for i in range(len(sequence) + 1):
        for new_base in bases:
            mutated = sequence[:i] + new_base + sequence[i:]
            mutated_resonance = calculate_resonance(mutated)
            delta = mutated_resonance - original_resonance
            score = mutated_resonance
            
            mutation = Mutation(
                original=sequence,
                mutated=mutated,
                position=i,
                mutation_type=MutationType.INSERTION,
                score=score,
                delta_resonance=delta,
                is_beneficial=(delta > 0 and score > RESONANCE_THRESHOLD)
            )
            mutations.append(mutation)
    
    # Deletions: remove each base
    for i in range(len(sequence)):
        mutated = sequence[:i] + sequence[i+1:]
        if mutated:  # Don't create empty sequence
            mutated_resonance = calculate_resonance(mutated)
            delta = mutated_resonance - original_resonance
            score = mutated_resonance
            
            mutation = Mutation(
                original=sequence,
                mutated=mutated,
                position=i,
                mutation_type=MutationType.DELETION,
                score=score,
                delta_resonance=delta,
                is_beneficial=(delta > 0 and score > RESONANCE_THRESHOLD)
            )
            mutations.append(mutation)
    
    # Sort by score (descending)
    mutations.sort(key=lambda m: m.score, reverse=True)
    
    return mutations


def greedy_optimize(sequence: str, max_iterations: int = 10) -> Tuple[str, List[Tuple[int, str, str, str]]]:
    """
    Optimize sequence using greedy algorithm.
    
    Iteratively applies the best mutation until no improvement or max iterations.
    
    Args:
        sequence: Initial DNA sequence
        max_iterations: Maximum optimization iterations
        
    Returns:
        Tuple of (optimized_sequence, optimization_steps)
        where steps is list of (iteration, mutated_seq, mutation_type, position)
    """
    current = sequence
    steps = []
    
    for iteration in range(max_iterations):
        # Generate all mutations
        mutations = generate_mutations(current)
        
        if not mutations:
            break
        
        # Get best mutation
        best = mutations[0]
        
        # Check if it improves
        current_resonance = calculate_resonance(current)
        if best.score <= current_resonance:
            # No improvement
            break
        
        # Apply mutation
        current = best.mutated
        
        # Record step
        step_type = best.mutation_type.value
        step = (iteration, current, step_type, best.position)
        steps.append(step)
    
    return current, steps


def find_hotspots(sequence: str, window_size: int = 3, threshold: float = 0.3) -> List[int]:
    """
    Find mutation hotspots in sequence.
    
    A hotspot is a region where mutations have particularly high impact.
    
    Args:
        sequence: DNA sequence
        window_size: Size of sliding window
        threshold: Threshold for hotspot detection
        
    Returns:
        List of hotspot positions
    """
    if len(sequence) < window_size:
        return []
    
    hotspots = []
    
    for i in range(len(sequence) - window_size + 1):
        window = sequence[i:i+window_size]
        
        # Generate mutations for window
        mutations = generate_mutations(window)
        
        if not mutations:
            continue
        
        # Check if best mutation exceeds threshold
        best_mutation = mutations[0]
        if best_mutation.delta_resonance > threshold:
            hotspots.append(i)
    
    return hotspots


def analyze_mutation_types(sequence: str) -> Dict[str, Mutation]:
    """
    Analyze best mutation of each type.
    
    Args:
        sequence: DNA sequence
        
    Returns:
        Dictionary mapping mutation type to best mutation
    """
    mutations = generate_mutations(sequence)
    
    result = {}
    for mut_type in MutationType:
        # Find best mutation of this type
        type_mutations = [m for m in mutations if m.mutation_type == mut_type]
        if type_mutations:
            result[mut_type.value] = type_mutations[0]
        else:
            # Create dummy mutation with score 0
            result[mut_type.value] = Mutation(
                original=sequence,
                mutated=sequence[:-1] if mut_type == MutationType.DELETION else sequence,
                position=0,
                mutation_type=mut_type,
                score=0.0,
                delta_resonance=0.0,
                is_beneficial=False
            )
    
    return result


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def format_mutation_display(mutation: Mutation, rank: int) -> str:
    """Format mutation for display."""
    return (f"   #{rank}: {mutation.original} → {mutation.mutated} "
            f"(pos={mutation.position}, tipo={mutation.mutation_type.value})\n"
            f"       Score: {mutation.score:.6f}, Δresonancia: {mutation.delta_resonance:.6f}, "
            f"Beneficiosa: {mutation.is_beneficial}")


def format_optimization_step(step: Tuple[int, str, str, int], original: str) -> str:
    """Format optimization step for display."""
    iteration, mutated, mut_type, position = step
    # Infer operation
    if len(mutated) > len(original):
        operation = "inserción"
    elif len(mutated) < len(original):
        operation = "deleción"
    else:
        operation = "sustitución"
    
    return f"      Iter {iteration}: {original} → {mutated} ({mut_type} pos={position})"
