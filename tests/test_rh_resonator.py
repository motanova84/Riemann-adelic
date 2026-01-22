"""
Test Suite for RH Resonator System
===================================

Comprehensive test suite covering all components of the RH Resonator:
- SpectralOscillator (6 tests)
- BPSKModulator (5 tests)
- RHResonator (8 tests)
- Integration (2 tests)

Total: 21 tests

Author: José Manuel Mota Burruezo Ψ✧
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add core to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from core.spectral_oscillator import SpectralOscillator, create_spectral_oscillator
from core.bpsk_modulator import BPSKModulator, create_bpsk_modulator
from core.rh_resonator import RHResonator, create_rh_resonator


class TestSpectralOscillator:
    """Test suite for SpectralOscillator."""
    
    def test_oscillator_creation(self):
        """Test oscillator creation and initialization."""
        osc = create_spectral_oscillator()
        
        assert osc is not None
        assert osc.frequency_base == 141.7001
        assert osc.sample_rate == 44100
        assert osc.coherence >= 0.888
        assert osc.stability >= 0.998
    
    def test_spectral_synchronization(self):
        """Test spectral reference synchronization."""
        osc = SpectralOscillator(sample_rate=44100)
        
        # Synchronize
        coherence = osc.sync_to_spectral_reference()
        
        assert coherence >= 0.888
        assert coherence <= 1.0
        assert osc.coherence == coherence
    
    def test_coherence_threshold(self):
        """Test that coherence meets minimum threshold."""
        osc = create_spectral_oscillator()
        
        # Check coherence
        assert osc.get_coherence() >= SpectralOscillator.MIN_COHERENCE
        assert osc.get_coherence() >= 0.888
    
    def test_signal_generation(self):
        """Test signal generation."""
        osc = create_spectral_oscillator()
        
        # Generate 1-second signal
        signal = osc.generate_duration(1.0)
        
        assert len(signal) == 44100  # 1 second at 44100 Hz
        assert np.all(np.abs(signal) <= 1.0)  # Amplitude check
    
    def test_stability_metric(self):
        """Test stability metric."""
        osc = create_spectral_oscillator()
        
        # Generate signal to update stability
        signal = osc.generate_duration(0.5)
        
        stability = osc.get_stability()
        assert stability >= SpectralOscillator.MIN_STABILITY
        assert stability >= 0.998
    
    def test_frequency_precision(self):
        """Test frequency precision."""
        osc = create_spectral_oscillator()
        
        # Generate signal
        signal = osc.generate_duration(1.0)
        
        # Verify frequency
        passed, measured = osc.verify_frequency_precision(signal, tolerance=1e-3)
        
        assert passed
        assert np.abs(measured - 141.7001) < 1e-3


class TestBPSKModulator:
    """Test suite for BPSKModulator."""
    
    def test_modulator_creation(self):
        """Test modulator creation."""
        osc = create_spectral_oscillator()
        modulator = create_bpsk_modulator(osc, baud_rate=10)
        
        assert modulator is not None
        assert modulator.baud_rate == 10.0
        assert modulator.symbol_duration == 0.1
    
    def test_single_bit_modulation(self):
        """Test modulation of single bits."""
        osc = create_spectral_oscillator()
        modulator = create_bpsk_modulator(osc, baud_rate=10)
        
        # Modulate bit 0
        signal_0 = modulator.modulate_bit(0)
        assert len(signal_0) > 0
        
        # Modulate bit 1
        signal_1 = modulator.modulate_bit(1)
        assert len(signal_1) > 0
        
        # Signals should be different (phase-shifted)
        correlation = np.corrcoef(signal_0, signal_1)[0, 1]
        assert correlation < 0  # 180° phase shift should give negative correlation
    
    def test_message_modulation(self):
        """Test modulation of text messages."""
        osc = create_spectral_oscillator()
        modulator = create_bpsk_modulator(osc, baud_rate=10)
        
        message = "TEST"
        signal, symbols = modulator.modulate_message(message)
        
        assert len(signal) > 0
        assert len(symbols) == len(message) * 8  # 8 bits per character
    
    def test_coherence_tracking(self):
        """Test coherence tracking during modulation."""
        osc = create_spectral_oscillator()
        modulator = create_bpsk_modulator(osc, baud_rate=10)
        
        # Modulate message
        message = "QCAL"
        signal, symbols = modulator.modulate_message(message)
        
        # Check coherence
        avg_coherence = modulator.get_average_coherence()
        assert avg_coherence >= 0.888
        assert avg_coherence <= 1.0
    
    def test_statistics(self):
        """Test modulation statistics."""
        osc = create_spectral_oscillator()
        modulator = create_bpsk_modulator(osc, baud_rate=10)
        
        # Modulate
        message = "AB"
        signal, symbols = modulator.modulate_message(message)
        
        # Get statistics
        stats = modulator.get_statistics()
        
        assert stats['symbols_modulated'] == 16  # 2 chars * 8 bits
        assert stats['average_coherence'] >= 0.888
        assert 'baud_rate' in stats
        assert 'symbol_duration_s' in stats


class TestRHResonator:
    """Test suite for RHResonator."""
    
    def test_resonator_creation(self):
        """Test resonator creation."""
        resonator = create_rh_resonator(resonator_id="TEST-001")
        
        assert resonator is not None
        assert resonator.resonator_id == "TEST-001"
        assert resonator.is_active is False
    
    def test_spectral_alignment(self):
        """Test spectral alignment check."""
        resonator = create_rh_resonator()
        
        # Check alignment
        aligned, diag = resonator.check_spectral_alignment()
        
        assert isinstance(aligned, bool)
        assert 'frequency_hz' in diag
        assert 'coherence' in diag
        assert 'stability' in diag
    
    def test_activation(self):
        """Test resonator activation."""
        resonator = create_rh_resonator()
        
        # Activate
        success = resonator.activate()
        
        assert success is True
        assert resonator.is_active is True
        assert resonator.activation_time is not None
    
    def test_coherence_gate(self):
        """Test coherence gate during activation."""
        resonator = create_rh_resonator()
        
        # Activate
        success = resonator.activate()
        
        assert success is True
        
        # Check coherence meets gate threshold
        state = resonator.get_state()
        assert state.coherence >= RHResonator.COHERENCE_GATE
        assert state.coherence >= 0.888
    
    def test_message_transmission(self):
        """Test message transmission."""
        resonator = create_rh_resonator()
        
        # Activate
        assert resonator.activate() is True
        
        # Transmit
        message = "QCAL"
        result = resonator.transmit_message(message)
        
        assert result is not None
        assert 'coherence' in result
        assert 'channel_fidelity' in result
        assert 'entropy' in result
        assert result['verification_passed'] == True  # Use == instead of is
    
    def test_state_export(self):
        """Test state export to JSON."""
        resonator = create_rh_resonator()
        resonator.activate()
        
        # Export state
        json_str = resonator.export_state()
        
        assert json_str is not None
        assert len(json_str) > 0
        assert 'metadata' in json_str
        assert 'state' in json_str
    
    def test_diagnostics(self):
        """Test diagnostic information."""
        resonator = create_rh_resonator()
        resonator.activate()
        
        # Get diagnostics
        diag = resonator.get_diagnostics()
        
        assert 'resonator' in diag
        assert 'oscillator' in diag
        assert 'modulator' in diag
        assert 'state' in diag
    
    def test_fidelity_calculation(self):
        """Test channel fidelity calculation."""
        resonator = create_rh_resonator()
        resonator.activate()
        
        # Transmit message
        message = "TEST MESSAGE"
        result = resonator.transmit_message(message)
        
        # Check fidelity
        assert result['channel_fidelity'] >= RHResonator.MIN_FIDELITY
        assert result['channel_fidelity'] >= 0.900
        assert result['channel_fidelity'] <= 1.0


class TestIntegration:
    """Integration tests for complete system."""
    
    def test_complete_workflow(self):
        """Test complete end-to-end workflow."""
        # Create resonator
        resonator = create_rh_resonator(resonator_id="INT-001")
        
        # Activate
        assert resonator.activate() is True
        
        # Transmit multiple messages (use ASCII for compatibility)
        messages = ["QCAL", "TEST", "COHERENCE"]
        
        for msg in messages:
            result = resonator.transmit_message(msg)
            assert result['verification_passed'] == True  # Use == instead of is
            assert result['coherence'] >= 0.888
            assert result['channel_fidelity'] >= 0.900
        
        # Check state
        state = resonator.get_state()
        assert state.total_transmissions == len(messages)
        assert state.average_fidelity >= 0.900
    
    def test_frequency_persistence(self):
        """Test that f₀ remains stable across operations."""
        resonator = create_rh_resonator()
        
        # Record initial frequency
        initial_freq = resonator.oscillator.frequency_base
        assert initial_freq == 141.7001
        
        # Activate and transmit
        resonator.activate()
        resonator.transmit_message("Test")
        
        # Check frequency unchanged
        final_freq = resonator.oscillator.frequency_base
        assert np.abs(final_freq - initial_freq) < 1e-6
        assert np.abs(final_freq - 141.7001) < 1e-6


# Test runner
if __name__ == "__main__":
    print("=" * 70)
    print("RH RESONATOR TEST SUITE")
    print("=" * 70)
    print()
    
    # Run tests with pytest
    exit_code = pytest.main([
        __file__,
        "-v",
        "--tb=short",
        "--color=yes"
    ])
    
    print()
    print("=" * 70)
    
    if exit_code == 0:
        print("✅ ALL TESTS PASSED")
        print()
        print("Summary:")
        print("- TestSpectralOscillator: 6/6 ✅")
        print("- TestBPSKModulator: 5/5 ✅")
        print("- TestRHResonator: 8/8 ✅")
        print("- TestIntegration: 2/2 ✅")
        print()
        print("Total: 21/21 PASSING")
    else:
        print("❌ SOME TESTS FAILED")
    
    print("=" * 70)
    
    sys.exit(exit_code)
