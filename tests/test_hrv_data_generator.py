"""
Tests for HRV Data Generator
=============================

Unit tests for HRV and microtubule data generation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-14
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src' / 'biological'))

from hrv_data_generator import (
    HRVGenerator,
    MicrotubuleOscillationGenerator,
    generate_sample_hrv_dataset,
    HRVSignal,
    F0_QCAL
)


class TestHRVGenerator:
    """Test HRV signal generation."""
    
    def test_initialization(self):
        """Test HRV generator initialization."""
        gen = HRVGenerator(
            sample_rate=4.0,
            duration=300.0,
            base_hr=70.0
        )
        assert gen.sample_rate == 4.0
        assert gen.duration == 300.0
        assert gen.base_hr == 70.0
        assert gen.n_samples == 1200  # 4 Hz * 300 s
    
    def test_generate_hrv_signal(self):
        """Test HRV signal generation."""
        gen = HRVGenerator(duration=60.0)
        signal = gen.generate_hrv_signal()
        
        # Check signal structure
        assert isinstance(signal, HRVSignal)
        assert len(signal.time) > 0
        assert len(signal.rr_intervals) == len(signal.time)
        assert len(signal.heart_rate) == len(signal.time)
        
        # Check physiological ranges
        assert np.all(signal.rr_intervals > 0)  # Positive intervals
        assert np.all(signal.heart_rate > 0)  # Positive HR
        assert 40 < np.mean(signal.heart_rate) < 120  # Reasonable HR range
    
    def test_hrv_metadata(self):
        """Test HRV signal metadata."""
        gen = HRVGenerator(base_hr=70.0)
        signal = gen.generate_hrv_signal()
        
        metadata = signal.metadata
        
        assert 'base_hr' in metadata
        assert 'mean_hr' in metadata
        assert 'std_hr' in metadata
        assert 'rmssd' in metadata
        assert 'sdnn' in metadata
        
        # Mean HR should be close to base HR
        assert abs(metadata['mean_hr'] - 70.0) < 10.0
    
    def test_frequency_spectrum(self):
        """Test frequency spectrum computation."""
        gen = HRVGenerator(duration=300.0)
        signal = gen.generate_hrv_signal(respiratory_freq=0.25)
        
        assert signal.frequency_spectrum is not None
        assert signal.spectral_power is not None
        assert len(signal.frequency_spectrum) == len(signal.spectral_power)
        
        # Check for respiratory peak around 0.25 Hz
        peak_idx = np.argmax(signal.spectral_power[1:]) + 1  # Skip DC
        peak_freq = signal.frequency_spectrum[peak_idx]
        assert 0.1 < peak_freq < 0.5  # In HF band
    
    def test_qcal_coupling(self):
        """Test QCAL resonance coupling."""
        gen = HRVGenerator(qcal_coupling=0.05)  # 5% coupling
        signal = gen.generate_hrv_signal()
        
        # With coupling, variance should be affected
        assert signal.metadata['std_hr'] > 0
    
    def test_reproducibility(self):
        """Test signal reproducibility with same parameters."""
        np.random.seed(42)
        gen1 = HRVGenerator(duration=60.0, base_hr=70.0)
        signal1 = gen1.generate_hrv_signal(noise_level=0.0)  # No random noise
        
        np.random.seed(42)
        gen2 = HRVGenerator(duration=60.0, base_hr=70.0)
        signal2 = gen2.generate_hrv_signal(noise_level=0.0)
        
        # Without noise, should be identical
        np.testing.assert_array_almost_equal(
            signal1.rr_intervals,
            signal2.rr_intervals,
            decimal=10
        )


class TestMicrotubuleOscillationGenerator:
    """Test microtubule oscillation generation."""
    
    def test_initialization(self):
        """Test generator initialization."""
        gen = MicrotubuleOscillationGenerator(
            sample_rate=1000.0,
            duration=10.0,
            fundamental_freq=100.0
        )
        assert gen.sample_rate == 1000.0
        assert gen.duration == 10.0
        assert gen.fundamental_freq == 100.0
    
    def test_generate_oscillation(self):
        """Test oscillation generation."""
        gen = MicrotubuleOscillationGenerator(duration=5.0)
        signal = gen.generate_oscillation(n_harmonics=5)
        
        assert 'time' in signal
        assert 'signal' in signal
        assert 'frequencies' in signal
        assert 'power_spectrum' in signal
        assert 'metadata' in signal
        
        assert len(signal['time']) == len(signal['signal'])
    
    def test_harmonic_content(self):
        """Test harmonic content in oscillation."""
        gen = MicrotubuleOscillationGenerator(fundamental_freq=100.0)
        signal = gen.generate_oscillation(n_harmonics=3, thermal_noise=0.0)
        
        # Check for peak at fundamental
        peak_freq = signal['metadata']['peak_frequency']
        assert 50 < peak_freq < 150  # Should be near fundamental
    
    def test_qcal_resonance_inclusion(self):
        """Test QCAL resonance inclusion."""
        gen = MicrotubuleOscillationGenerator(sample_rate=500.0)
        
        signal_with = gen.generate_oscillation(qcal_resonance=True, thermal_noise=0.0)
        signal_without = gen.generate_oscillation(qcal_resonance=False, thermal_noise=0.0)
        
        # Signals should differ
        assert not np.allclose(signal_with['signal'], signal_without['signal'])
    
    def test_damping_effect(self):
        """Test damping envelope effect."""
        gen = MicrotubuleOscillationGenerator(duration=10.0)
        signal = gen.generate_oscillation(damping_factor=0.5)
        
        # Signal should decay over time
        early_amplitude = np.mean(np.abs(signal['signal'][:100]))
        late_amplitude = np.mean(np.abs(signal['signal'][-100:]))
        
        assert late_amplitude < early_amplitude
    
    def test_normalization(self):
        """Test signal normalization."""
        gen = MicrotubuleOscillationGenerator()
        signal = gen.generate_oscillation()
        
        # Signal should be normalized to [-1, 1] range (approximately)
        assert np.max(np.abs(signal['signal'])) <= 1.0 + 1e-6


class TestDatasetGeneration:
    """Test dataset generation utilities."""
    
    def test_generate_sample_dataset(self):
        """Test sample dataset generation."""
        dataset = generate_sample_hrv_dataset(n_subjects=3, duration=60.0)
        
        assert len(dataset) == 3
        assert all(isinstance(sig, HRVSignal) for sig in dataset.values())
        
        # Check subject IDs
        assert 'subject_01' in dataset
        assert 'subject_02' in dataset
        assert 'subject_03' in dataset
    
    def test_dataset_variability(self):
        """Test variability across subjects."""
        dataset = generate_sample_hrv_dataset(n_subjects=5, duration=60.0)
        
        mean_hrs = [sig.metadata['mean_hr'] for sig in dataset.values()]
        
        # Should have some variability
        assert np.std(mean_hrs) > 0


class TestPhysiologicalValidity:
    """Test physiological validity of generated signals."""
    
    def test_hrv_time_domain_metrics(self):
        """Test HRV time-domain metrics are in physiological range."""
        gen = HRVGenerator(base_hr=70.0, duration=300.0)
        signal = gen.generate_hrv_signal()
        
        # SDNN: typically 20-100 ms for healthy adults
        assert 10 < signal.metadata['sdnn'] < 200
        
        # RMSSD: typically 20-80 ms
        rmssd_ms = signal.metadata['rmssd'] * 1000
        assert 5 < rmssd_ms < 200
    
    def test_lf_hf_ratio_effect(self):
        """Test LF/HF ratio effect on variability."""
        gen = HRVGenerator(duration=300.0)
        
        # High sympathetic activity (high LF/HF)
        signal_high = gen.generate_hrv_signal(lf_hf_ratio=3.0)
        
        # High parasympathetic (low LF/HF)
        signal_low = gen.generate_hrv_signal(lf_hf_ratio=0.5)
        
        # Both should be valid
        assert signal_high.metadata['sdnn'] > 0
        assert signal_low.metadata['sdnn'] > 0


# Run tests if executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
