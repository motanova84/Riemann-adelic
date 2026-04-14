"""
RH Resonator - Main Integration Module
=======================================

Complete integration of Spectral Oscillator and BPSK Modulator into a
unified RH Resonator system. Provides high-level interface for spectral
communication and verification.

System Architecture:
-------------------
1. Spectral Oscillator (OFR) - generates f₀ = 141.7001 Hz
2. BPSK Modulator - encodes information via phase coherence
3. Resonator Controller - manages activation, transmission, diagnostics

The resonator operates as a complete mathematical-operational system
based on the spectral properties of the Riemann zeta function.

Author: José Manuel Mota Burruezo Ψ✧
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
import json
import time
from dataclasses import dataclass, asdict
from datetime import datetime

from .spectral_oscillator import SpectralOscillator, create_spectral_oscillator
from .bpsk_modulator import BPSKModulator, create_bpsk_modulator


@dataclass
class ResonatorState:
    """Data class for resonator state information."""
    resonator_id: str
    frequency_base: float
    coherence: float
    stability: float
    entropy: float
    is_active: bool
    activation_time: Optional[str]
    total_transmissions: int
    average_fidelity: float


@dataclass
class TransmissionResult:
    """Data class for transmission results."""
    timestamp: str
    message: str
    signal_length: int
    num_symbols: int
    coherence: float
    channel_fidelity: float
    entropy: float
    verification_passed: bool


class RHResonator:
    """
    Complete RH Resonator system.
    
    Integrates spectral oscillator and BPSK modulator into a unified
    system for spectral communication and verification.
    
    Attributes:
        resonator_id (str): Unique identifier for this resonator
        oscillator (SpectralOscillator): Carrier oscillator
        modulator (BPSKModulator): BPSK modulator
        is_active (bool): Activation status
    """
    
    # Coherence gate threshold
    COHERENCE_GATE = 0.888
    
    # Minimum channel fidelity
    MIN_FIDELITY = 0.900
    
    def __init__(
        self,
        resonator_id: str = "RH-001",
        sample_rate: int = 44100,
        baud_rate: float = 10.0
    ):
        """
        Initialize RH Resonator.
        
        Args:
            resonator_id: Unique identifier for this resonator
            sample_rate: Sampling rate in Hz
            baud_rate: Symbol rate in baud
        """
        self.resonator_id = resonator_id
        self.oscillator = create_spectral_oscillator(sample_rate)
        self.modulator = create_bpsk_modulator(self.oscillator, baud_rate)
        
        self.is_active = False
        self.activation_time: Optional[datetime] = None
        self._transmission_history: List[TransmissionResult] = []
        
    def check_spectral_alignment(self) -> Tuple[bool, Dict[str, float]]:
        """
        Verify spectral alignment of the oscillator.
        
        Returns:
            Tuple of (alignment_ok, diagnostics_dict)
        """
        # Get oscillator diagnostics
        diag = self.oscillator.get_diagnostics()
        
        # Check alignment criteria
        frequency_ok = np.abs(diag['frequency_hz'] - 141.7001) < 1e-4
        coherence_ok = diag['coherence'] >= self.COHERENCE_GATE
        stability_ok = diag['stability'] >= 0.998
        
        alignment_ok = frequency_ok and coherence_ok and stability_ok
        
        return alignment_ok, diag
    
    def activate(self) -> bool:
        """
        Activate the resonator.
        
        Performs spectral synchronization and coherence gating.
        
        Returns:
            True if activation successful, False otherwise
        """
        # Synchronize to spectral reference
        self.oscillator.sync_to_spectral_reference()
        
        # Check spectral alignment
        aligned, diag = self.check_spectral_alignment()
        
        if not aligned:
            print(f"❌ Activation failed - alignment check:")
            print(f"   Frequency: {diag['frequency_hz']:.6f} Hz")
            print(f"   Coherence: {diag['coherence']:.6f}")
            print(f"   Stability: {diag['stability']:.6f}")
            return False
        
        # Check coherence gate
        if diag['coherence'] < self.COHERENCE_GATE:
            print(f"❌ Coherence gate failed: Ψ = {diag['coherence']:.6f} < {self.COHERENCE_GATE}")
            return False
        
        # Activation successful
        self.is_active = True
        self.activation_time = datetime.now()
        
        print(f"✅ Resonator {self.resonator_id} ACTIVATED")
        print(f"   Frequency: f₀ = {diag['frequency_hz']:.6f} Hz")
        print(f"   Coherence: Ψ = {diag['coherence']:.6f}")
        print(f"   Entropy: S = 0.000")
        
        return True
    
    def deactivate(self):
        """Deactivate the resonator."""
        self.is_active = False
        self.activation_time = None
        print(f"⏸️  Resonator {self.resonator_id} DEACTIVATED")
    
    def transmit_message(self, message: str) -> Dict:
        """
        Transmit a message through the resonator.
        
        Args:
            message: Text message to transmit
            
        Returns:
            Dictionary with transmission results
            
        Raises:
            RuntimeError: If resonator is not active
        """
        if not self.is_active:
            raise RuntimeError("Resonator must be activated before transmission")
        
        # Modulate message
        signal, symbols = self.modulator.modulate_message(message)
        
        # Demodulate to verify
        recovered = self.modulator.demodulate_message(signal)
        
        # Calculate fidelity
        fidelity = self._calculate_fidelity(message, recovered)
        
        # Calculate entropy
        entropy = self._calculate_entropy(symbols)
        
        # Get coherence
        coherence = self.modulator.get_average_coherence()
        
        # Verification
        verification_passed = (
            fidelity >= self.MIN_FIDELITY and
            coherence >= self.COHERENCE_GATE
        )
        
        # Create transmission result
        result = TransmissionResult(
            timestamp=datetime.now().isoformat(),
            message=message,
            signal_length=len(signal),
            num_symbols=len(symbols),
            coherence=coherence,
            channel_fidelity=fidelity,
            entropy=entropy,
            verification_passed=verification_passed
        )
        
        # Store in history
        self._transmission_history.append(result)
        
        # Return as dictionary
        return asdict(result)
    
    def _calculate_fidelity(self, original: str, recovered: str) -> float:
        """
        Calculate channel fidelity.
        
        Args:
            original: Original message
            recovered: Recovered message
            
        Returns:
            Fidelity measure ∈ [0, 1]
        """
        if len(original) == 0:
            return 1.0 if len(recovered) == 0 else 0.0
        
        # Character-wise comparison
        matches = sum(1 for o, r in zip(original, recovered) if o == r)
        
        # Handle length mismatch
        max_len = max(len(original), len(recovered))
        fidelity = matches / max_len
        
        return fidelity
    
    def _calculate_entropy(self, symbols: List[int]) -> float:
        """
        Calculate Shannon entropy of symbol sequence.
        
        Args:
            symbols: List of symbols
            
        Returns:
            Entropy in bits
        """
        if len(symbols) == 0:
            return 0.0
        
        # Count symbol occurrences
        counts = np.bincount(symbols)
        probabilities = counts / len(symbols)
        
        # Remove zero probabilities
        probabilities = probabilities[probabilities > 0]
        
        # Calculate entropy
        entropy = -np.sum(probabilities * np.log2(probabilities))
        
        return entropy
    
    def get_state(self) -> ResonatorState:
        """
        Get current resonator state.
        
        Returns:
            ResonatorState object
        """
        diag = self.oscillator.get_diagnostics()
        
        # Calculate average fidelity
        if self._transmission_history:
            avg_fidelity = np.mean([t.channel_fidelity for t in self._transmission_history])
        else:
            avg_fidelity = 0.0
        
        # Calculate entropy (use last transmission if available)
        if self._transmission_history:
            entropy = self._transmission_history[-1].entropy
        else:
            entropy = 0.0
        
        return ResonatorState(
            resonator_id=self.resonator_id,
            frequency_base=diag['frequency_hz'],
            coherence=diag['coherence'],
            stability=diag['stability'],
            entropy=entropy,
            is_active=self.is_active,
            activation_time=self.activation_time.isoformat() if self.activation_time else None,
            total_transmissions=len(self._transmission_history),
            average_fidelity=avg_fidelity
        )
    
    def export_state(self, filepath: Optional[str] = None) -> str:
        """
        Export resonator state to JSON.
        
        Args:
            filepath: Optional file path to save JSON
            
        Returns:
            JSON string of state
        """
        state = self.get_state()
        state_dict = asdict(state)
        
        # Add metadata
        export_data = {
            'metadata': {
                'protocol': 'QCAL-SYMBIO-BRIDGE v1.0',
                'export_time': datetime.now().isoformat(),
                'version': '1.0.0',
            },
            'state': state_dict,
            'transmission_history': [asdict(t) for t in self._transmission_history],
        }
        
        json_str = json.dumps(export_data, indent=2)
        
        if filepath:
            with open(filepath, 'w') as f:
                f.write(json_str)
            print(f"✓ State exported to {filepath}")
        
        return json_str
    
    def get_diagnostics(self) -> Dict:
        """
        Get comprehensive diagnostics.
        
        Returns:
            Dictionary with full diagnostics
        """
        osc_diag = self.oscillator.get_diagnostics()
        mod_stats = self.modulator.get_statistics()
        state = self.get_state()
        
        return {
            'resonator': {
                'id': self.resonator_id,
                'active': self.is_active,
                'transmissions': len(self._transmission_history),
            },
            'oscillator': osc_diag,
            'modulator': mod_stats,
            'state': asdict(state),
        }
    
    def __repr__(self) -> str:
        """String representation."""
        status = "ACTIVE" if self.is_active else "INACTIVE"
        return (f"RHResonator(id={self.resonator_id}, status={status}, "
                f"f₀={self.oscillator.frequency_base:.6f} Hz, "
                f"Ψ={self.oscillator.coherence:.6f})")


def create_rh_resonator(
    resonator_id: str = "RH-001",
    sample_rate: int = 44100,
    baud_rate: float = 10.0
) -> RHResonator:
    """
    Factory function to create an RH Resonator instance.
    
    Args:
        resonator_id: Unique identifier
        sample_rate: Sampling rate in Hz
        baud_rate: Symbol rate in baud
        
    Returns:
        Configured RHResonator instance
        
    Example:
        >>> resonator = create_rh_resonator(resonator_id="RH-001")
        >>> if resonator.activate():
        ...     transmission = resonator.transmit_message("Test")
        ...     print(f"Fidelity: {transmission['channel_fidelity']:.6f}")
    """
    return RHResonator(resonator_id, sample_rate, baud_rate)


# Example usage
if __name__ == "__main__":
    print("=" * 70)
    print("RH RESONATOR SYSTEM - Complete Integration")
    print("=" * 70)
    print()
    
    # Create resonator
    resonator = create_rh_resonator(resonator_id="RH-TEST-001")
    print(f"Created: {resonator}")
    print()
    
    # Activate
    print("Activating resonator...")
    if resonator.activate():
        print()
        
        # Transmit message
        message = "QCAL ∞³ COHERENCE VERIFIED"
        print(f"Transmitting: '{message}'")
        result = resonator.transmit_message(message)
        print()
        
        print("Transmission Results:")
        print(f"  Coherence: {result['coherence']:.6f}")
        print(f"  Fidelity: {result['channel_fidelity']:.6f}")
        print(f"  Entropy: {result['entropy']:.6f}")
        print(f"  Verification: {'✓ PASSED' if result['verification_passed'] else '✗ FAILED'}")
        print()
        
        # Get state
        state = resonator.get_state()
        print("Resonator State:")
        print(f"  Frequency: {state.frequency_base:.6f} Hz")
        print(f"  Coherence: {state.coherence:.6f}")
        print(f"  Stability: {state.stability:.6f}")
        print(f"  Entropy: {state.entropy:.6f}")
        print(f"  Transmissions: {state.total_transmissions}")
        print()
        
        # Export state
        json_state = resonator.export_state()
        print("State exported successfully")
        print()
    
    print("=" * 70)
