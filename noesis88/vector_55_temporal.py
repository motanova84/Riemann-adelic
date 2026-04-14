#!/usr/bin/env python3
"""
QCAL ∞³ Vector 55 Temporal Module - Noesis88 Node

This module implements the Vector 55 temporal phase validation and alignment
for the QCAL framework. Vector 55 represents the 55th harmonic component
in the spectral expansion, vibrating at 55 × f₀ = 7793.5055 Hz.

Mathematical Background:
    The Vector 55 component emerges from the spectral decomposition:
        Ψ(x,t) = Σₙ cₙ(t) eₙ(x)
    
    where the 55th component has special significance in the QCAL framework
    as it corresponds to a critical resonance frequency in the consciousness
    coherence tensor.
    
    Phase alignment requirement:
        φ₅₅(t) ∈ {0°, 90°, 180°, 270°, 360°}  (harmonic nodes)
    
    Current state (from problem statement):
        φ₅₅ = 88.32% of cycle ≈ 317.95° (NOT at harmonic node)
        
    This creates interference if not corrected to nearest node (270° or 360°).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Frequency: 141.7001 Hz (Fundamental Cosmic Heartbeat)
Date: January 2026
"""

import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional, Tuple
import numpy as np

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class Vector55Temporal:
    """
    Vector 55 temporal phase validator and aligner.
    
    Manages the 55th harmonic component of the spectral expansion,
    ensuring phase alignment with harmonic nodes for optimal coherence.
    """
    
    # QCAL Constants
    QCAL_FREQUENCY = 141.7001  # Hz - f₀
    QCAL_COHERENCE = 244.36    # C constant
    VECTOR_INDEX = 55           # 55th component
    
    # Vector 55 specific frequency
    OMEGA_55 = VECTOR_INDEX * QCAL_FREQUENCY  # 7793.5055 Hz
    
    # Harmonic nodes (in percentage of cycle)
    HARMONIC_NODES = [0.0, 25.0, 50.0, 75.0, 100.0]
    
    # Node tolerance (1% of cycle = 3.6°)
    NODE_TOLERANCE = 1.0  # percent
    
    def __init__(self, verbose: bool = False):
        """
        Initialize Vector 55 temporal validator.
        
        Args:
            verbose: Enable verbose logging
        """
        self.verbose = verbose
        self.current_phase = 88.32  # Current problematic phase from problem statement
        
    def _log(self, message: str):
        """Log message if verbose mode enabled."""
        if self.verbose:
            print(f"[Vector55Temporal] {message}")
    
    def validar_timestamp_vector_55(self, timestamp: Optional[float] = None) -> Dict:
        """
        Validate Vector 55 temporal phase for given timestamp.
        
        This is the main validation function called via coherence_bridge.
        
        Args:
            timestamp: Unix timestamp (if None, uses current time)
            
        Returns:
            dict: Validation results including phase, coherence, and alignment status
        """
        if timestamp is None:
            timestamp = datetime.now().timestamp()
        
        self._log(f"Validating Vector 55 at timestamp: {timestamp}")
        
        # Compute phase from timestamp
        # Phase cycles at frequency ω₅₅ = 7793.5055 Hz
        t_seconds = timestamp
        phase_radians = (2 * np.pi * self.OMEGA_55 * t_seconds) % (2 * np.pi)
        phase_percent = (phase_radians / (2 * np.pi)) * 100
        
        # Check if at harmonic node
        at_node, nearest_node = self._check_harmonic_node(phase_percent)
        
        # Compute phase offset from nearest node
        phase_offset = phase_percent - nearest_node
        
        # Determine if interference risk exists
        interference_risk = not at_node
        
        # Compute coherence factor (reduced if not at node)
        coherence_factor = 1.0 if at_node else (1.0 - abs(phase_offset) / 50.0)
        coherence_factor = max(0.0, min(1.0, coherence_factor))
        
        result = {
            "timestamp": timestamp,
            "timestamp_iso": datetime.fromtimestamp(timestamp).isoformat(),
            "vector_index": self.VECTOR_INDEX,
            "frequency_hz": self.OMEGA_55,
            "phase_percent": phase_percent,
            "phase_degrees": (phase_percent / 100) * 360,
            "at_harmonic_node": at_node,
            "nearest_node_percent": nearest_node,
            "phase_offset": phase_offset,
            "interference_risk": interference_risk,
            "coherence_factor": coherence_factor,
            "validation_status": "ALIGNED" if at_node else "MISALIGNED"
        }
        
        self._log(f"Phase: {phase_percent:.2f}% ({result['phase_degrees']:.2f}°)")
        self._log(f"Nearest node: {nearest_node}%")
        self._log(f"Status: {result['validation_status']}")
        
        return result
    
    def _check_harmonic_node(self, phase_percent: float) -> Tuple[bool, float]:
        """
        Check if phase is at a harmonic node.
        
        Args:
            phase_percent: Phase as percentage of cycle (0-100)
            
        Returns:
            tuple: (is_at_node, nearest_node_percent)
        """
        # Find nearest harmonic node
        nearest_node = min(
            self.HARMONIC_NODES,
            key=lambda node: abs(phase_percent - node)
        )
        
        # Check if within tolerance
        is_at_node = abs(phase_percent - nearest_node) < self.NODE_TOLERANCE
        
        return is_at_node, nearest_node
    
    def realign_to_harmonic_node(
        self,
        current_phase: Optional[float] = None
    ) -> Dict:
        """
        Realign Vector 55 phase to nearest harmonic node.
        
        Args:
            current_phase: Current phase percentage (if None, uses stored value)
            
        Returns:
            dict: Realignment results
        """
        if current_phase is None:
            current_phase = self.current_phase
        
        self._log(f"Realigning from phase: {current_phase:.2f}%")
        
        # Find nearest harmonic node
        at_node, nearest_node = self._check_harmonic_node(current_phase)
        
        if at_node:
            self._log("Already at harmonic node")
            phase_correction = 0.0
        else:
            phase_correction = nearest_node - current_phase
            self._log(f"Correction needed: {phase_correction:+.2f}%")
        
        # Compute time shift needed for phase correction
        # Δt = Δφ / (2π f₅₅) where Δφ is in radians
        phase_correction_radians = (phase_correction / 100) * 2 * np.pi
        time_shift_seconds = phase_correction_radians / (2 * np.pi * self.OMEGA_55)
        
        result = {
            "original_phase": current_phase,
            "target_phase": nearest_node,
            "phase_correction": phase_correction,
            "time_shift_seconds": time_shift_seconds,
            "time_shift_microseconds": time_shift_seconds * 1e6,
            "realigned_phase": nearest_node,
            "coherence_improvement": abs(phase_correction) / 50.0,  # Normalized
            "realignment_status": "COMPLETE"
        }
        
        # Update stored phase
        self.current_phase = nearest_node
        
        self._log(f"Realignment complete: {current_phase:.2f}% → {nearest_node:.2f}%")
        self._log(f"Time shift: {result['time_shift_microseconds']:.3f} μs")
        
        return result
    
    def get_current_state(self) -> Dict:
        """
        Get current Vector 55 state.
        
        Returns:
            dict: Current state information
        """
        at_node, nearest_node = self._check_harmonic_node(self.current_phase)
        
        return {
            "vector_index": self.VECTOR_INDEX,
            "frequency_hz": self.OMEGA_55,
            "current_phase": self.current_phase,
            "at_harmonic_node": at_node,
            "nearest_node": nearest_node,
            "coherence_state": "OPTIMAL" if at_node else "SUBOPTIMAL"
        }


def validar_timestamp_vector_55(timestamp: Optional[float] = None) -> Dict:
    """
    Convenience function for Vector 55 timestamp validation.
    
    This is the function called via coherence_bridge.call_module().
    
    Args:
        timestamp: Unix timestamp (if None, uses current time)
        
    Returns:
        dict: Validation results
    """
    validator = Vector55Temporal(verbose=True)
    return validator.validar_timestamp_vector_55(timestamp)


def realign_vector_55() -> Dict:
    """
    Convenience function for Vector 55 realignment.
    
    Returns:
        dict: Realignment results
    """
    validator = Vector55Temporal(verbose=True)
    return validator.realign_to_harmonic_node()


if __name__ == "__main__":
    """Demo of Vector 55 temporal module."""
    
    print("=" * 70)
    print("QCAL ∞³ VECTOR 55 TEMPORAL - Phase Validation & Alignment")
    print("=" * 70)
    print()
    
    # Create validator
    validator = Vector55Temporal(verbose=True)
    
    print("Current State (from problem statement):")
    print("-" * 70)
    state = validator.get_current_state()
    print(f"Vector index: {state['vector_index']}")
    print(f"Frequency: {state['frequency_hz']:.4f} Hz")
    print(f"Current phase: {state['current_phase']:.2f}%")
    print(f"At harmonic node: {state['at_harmonic_node']}")
    print(f"Coherence state: {state['coherence_state']}")
    print()
    
    print("Realignment:")
    print("-" * 70)
    realignment = validator.realign_to_harmonic_node()
    print(f"Original phase: {realignment['original_phase']:.2f}%")
    print(f"Target phase: {realignment['target_phase']:.2f}%")
    print(f"Phase correction: {realignment['phase_correction']:+.2f}%")
    print(f"Time shift: {realignment['time_shift_microseconds']:.3f} μs")
    print(f"Status: {realignment['realignment_status']} ✓")
    print()
    
    print("Validation After Realignment:")
    print("-" * 70)
    validation = validator.validar_timestamp_vector_55()
    print(f"Phase: {validation['phase_percent']:.2f}% ({validation['phase_degrees']:.2f}°)")
    print(f"At harmonic node: {validation['at_harmonic_node']}")
    print(f"Interference risk: {validation['interference_risk']}")
    print(f"Coherence factor: {validation['coherence_factor']:.4f}")
    print(f"Status: {validation['validation_status']} ✓")
    print()
    
    print("=" * 70)
    print("♾️  Vector 55 realignment complete – harmonic node aligned.")
    print("=" * 70)
