"""
BPSK Modulator for RH Resonator
================================

Binary Phase-Shift Keying (BPSK) modulator using the spectral oscillator
as carrier signal. Encodes binary information through phase coherence.

Modulation Scheme:
-----------------
- Bit 0 → Phase 0 rad (in-phase)
- Bit 1 → Phase π rad (inverted)

The modulation preserves spectral coherence while encoding information
through phase shifts aligned with the fundamental frequency f₀ = 141.7001 Hz.

Author: José Manuel Mota Burruezo Ψ✧
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from .spectral_oscillator import SpectralOscillator


class BPSKModulator:
    """
    Binary Phase-Shift Keying modulator for RH Resonator.
    
    Uses the SpectralOscillator as carrier and modulates binary data
    through phase shifts while maintaining spectral coherence.
    
    Attributes:
        oscillator (SpectralOscillator): Carrier oscillator
        baud_rate (float): Symbol rate in baud (symbols/second)
        coherence_history (List[float]): History of per-symbol coherence
    """
    
    def __init__(self, oscillator: SpectralOscillator, baud_rate: float = 10.0):
        """
        Initialize BPSK modulator.
        
        Args:
            oscillator: SpectralOscillator instance to use as carrier
            baud_rate: Symbol rate in baud (default: 10 baud)
        """
        self.oscillator = oscillator
        self.baud_rate = baud_rate
        self.coherence_history: List[float] = []
        self._modulation_count = 0
        self._current_time = 0.0  # Track time for continuous phase
        
    @property
    def symbol_duration(self) -> float:
        """Duration of one symbol in seconds."""
        return 1.0 / self.baud_rate
    
    def modulate_bit(self, bit: int) -> np.ndarray:
        """
        Modulate a single bit.
        
        Args:
            bit: Bit value (0 or 1)
            
        Returns:
            Modulated signal array for one symbol period
            
        Raises:
            ValueError: If bit is not 0 or 1
        """
        if bit not in [0, 1]:
            raise ValueError(f"Bit must be 0 or 1, got {bit}")
        
        # Determine phase for this bit
        bit_phase = np.pi if bit == 1 else 0.0
        
        # Generate time array for this symbol
        num_samples = int(self.symbol_duration * self.oscillator.sample_rate)
        t = np.arange(num_samples) / self.oscillator.sample_rate
        
        # Generate signal with appropriate phase
        # Use continuous time reference
        signal = np.sin(2 * np.pi * self.oscillator.frequency_base * (t + self._current_time) + bit_phase)
        
        # Apply coherence
        signal *= self.oscillator.coherence
        
        # Update time for next symbol
        self._current_time += self.symbol_duration
        
        # Track coherence
        self.coherence_history.append(self.oscillator.get_coherence())
        self._modulation_count += 1
        
        return signal
    
    def modulate_bits(self, bits: List[int]) -> Tuple[np.ndarray, List[int]]:
        """
        Modulate a sequence of bits.
        
        Args:
            bits: List of bit values (0 or 1)
            
        Returns:
            Tuple of (modulated_signal, symbol_list)
        """
        signals = []
        symbols = []
        
        for bit in bits:
            signal = self.modulate_bit(bit)
            signals.append(signal)
            symbols.append(bit)
        
        # Concatenate all signals
        modulated_signal = np.concatenate(signals)
        
        return modulated_signal, symbols
    
    def string_to_bits(self, message: str) -> List[int]:
        """
        Convert string message to list of bits.
        
        Args:
            message: String message to convert
            
        Returns:
            List of bits (8 bits per character, ASCII encoding)
        """
        bits = []
        for char in message:
            # Get ASCII value
            ascii_val = ord(char)
            # Convert to 8-bit binary
            char_bits = [(ascii_val >> i) & 1 for i in range(7, -1, -1)]
            bits.extend(char_bits)
        
        return bits
    
    def bits_to_string(self, bits: List[int]) -> str:
        """
        Convert list of bits back to string message.
        
        Args:
            bits: List of bits (must be multiple of 8)
            
        Returns:
            Decoded string message
            
        Raises:
            ValueError: If bits length is not multiple of 8
        """
        if len(bits) % 8 != 0:
            raise ValueError(f"Bits length must be multiple of 8, got {len(bits)}")
        
        message = []
        for i in range(0, len(bits), 8):
            # Get 8-bit chunk
            byte_bits = bits[i:i+8]
            # Convert to ASCII value
            ascii_val = sum(bit << (7-j) for j, bit in enumerate(byte_bits))
            # Convert to character
            message.append(chr(ascii_val))
        
        return ''.join(message)
    
    def modulate_message(self, message: str) -> Tuple[np.ndarray, List[int]]:
        """
        Modulate a text message.
        
        Args:
            message: Text message to modulate
            
        Returns:
            Tuple of (modulated_signal, symbol_list)
            
        Example:
            >>> modulator = BPSKModulator(oscillator)
            >>> signal, symbols = modulator.modulate_message("QCAL")
            >>> print(f"Transmitted {len(symbols)} symbols")
        """
        # Reset time for each message to ensure clean start
        self._current_time = 0.0
        
        # Convert message to bits
        bits = self.string_to_bits(message)
        
        # Modulate bits
        signal, symbols = self.modulate_bits(bits)
        
        return signal, symbols
    
    def demodulate_signal(self, signal: np.ndarray) -> List[int]:
        """
        Demodulate BPSK signal to recover bits.
        
        This is a simplified demodulator using correlation detection.
        
        Args:
            signal: Modulated signal
            
        Returns:
            List of recovered bits
        """
        bits = []
        samples_per_symbol = int(self.symbol_duration * self.oscillator.sample_rate)
        
        # Process each symbol
        num_symbols = len(signal) // samples_per_symbol
        
        for i in range(num_symbols):
            # Extract symbol
            start = i * samples_per_symbol
            end = start + samples_per_symbol
            symbol = signal[start:end]
            
            # Generate reference signal for bit 0 (in-phase)
            t = np.arange(len(symbol)) / self.oscillator.sample_rate
            t_offset = i * self.symbol_duration  # Account for time offset
            ref = np.sin(2 * np.pi * self.oscillator.frequency_base * (t + t_offset))
            
            # Correlate with reference (positive = in-phase/bit 0, negative = inverted/bit 1)
            correlation = np.sum(symbol * ref)
            
            # Decide bit based on correlation sign
            bit = 0 if correlation >= 0 else 1
            bits.append(bit)
        
        return bits
    
    def demodulate_message(self, signal: np.ndarray) -> str:
        """
        Demodulate signal to recover text message.
        
        Args:
            signal: Modulated signal
            
        Returns:
            Recovered text message
        """
        # Demodulate to bits
        bits = self.demodulate_signal(signal)
        
        # Convert bits to string
        # Truncate to multiple of 8
        num_bytes = len(bits) // 8
        bits = bits[:num_bytes * 8]
        
        message = self.bits_to_string(bits)
        
        return message
    
    def get_average_coherence(self) -> float:
        """
        Get average coherence across all modulated symbols.
        
        Returns:
            Average coherence value
        """
        if not self.coherence_history:
            return 0.0
        
        return np.mean(self.coherence_history)
    
    def get_coherence_variance(self) -> float:
        """
        Get variance of coherence across symbols.
        
        Returns:
            Coherence variance
        """
        if len(self.coherence_history) < 2:
            return 0.0
        
        return np.var(self.coherence_history)
    
    def get_statistics(self) -> Dict[str, float]:
        """
        Get modulation statistics.
        
        Returns:
            Dictionary with statistics
        """
        return {
            'baud_rate': self.baud_rate,
            'symbol_duration_s': self.symbol_duration,
            'symbols_modulated': self._modulation_count,
            'average_coherence': self.get_average_coherence(),
            'coherence_variance': self.get_coherence_variance(),
            'min_coherence': min(self.coherence_history) if self.coherence_history else 0.0,
            'max_coherence': max(self.coherence_history) if self.coherence_history else 0.0,
        }
    
    def reset_statistics(self):
        """Reset modulation statistics."""
        self.coherence_history.clear()
        self._modulation_count = 0
    
    def __repr__(self) -> str:
        """String representation."""
        return (f"BPSKModulator(baud_rate={self.baud_rate}, "
                f"symbols={self._modulation_count}, "
                f"avg_coherence={self.get_average_coherence():.6f})")


def create_bpsk_modulator(
    oscillator: SpectralOscillator,
    baud_rate: float = 10.0
) -> BPSKModulator:
    """
    Factory function to create a BPSKModulator instance.
    
    Args:
        oscillator: SpectralOscillator instance to use as carrier
        baud_rate: Symbol rate in baud (default: 10 baud)
        
    Returns:
        Configured BPSKModulator instance
        
    Example:
        >>> from core.spectral_oscillator import create_spectral_oscillator
        >>> osc = create_spectral_oscillator()
        >>> modulator = create_bpsk_modulator(osc, baud_rate=10)
        >>> signal, symbols = modulator.modulate_message("Test")
        >>> print(f"Average coherence: {modulator.get_average_coherence():.6f}")
    """
    return BPSKModulator(oscillator, baud_rate)


# Example usage
if __name__ == "__main__":
    from .spectral_oscillator import create_spectral_oscillator
    
    print("=" * 70)
    print("RH BPSK Modulator - Phase Coherence Encoding")
    print("=" * 70)
    print()
    
    # Create oscillator and modulator
    osc = create_spectral_oscillator()
    modulator = create_bpsk_modulator(osc, baud_rate=10)
    
    # Test message
    message = "QCAL ∞³"
    print(f"Message: '{message}'")
    print()
    
    # Modulate
    print("Modulating...")
    signal, symbols = modulator.modulate_message(message)
    print(f"✓ Generated {len(signal)} samples")
    print(f"✓ Transmitted {len(symbols)} symbols")
    print()
    
    # Demodulate
    print("Demodulating...")
    recovered = modulator.demodulate_message(signal)
    print(f"✓ Recovered: '{recovered}'")
    print()
    
    # Statistics
    print("Statistics:")
    stats = modulator.get_statistics()
    for key, value in stats.items():
        print(f"  {key}: {value:.6f}")
    print()
    
    # Verify
    print(f"Fidelity: {'✓ PERFECT' if message == recovered else '✗ ERROR'}")
    print()
    print("=" * 70)
