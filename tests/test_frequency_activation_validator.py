"""
Unit tests for Dual EEG-LIGO Frequency Activation Validator

Tests the complete experimental validation framework:
- EEG data generation
- LIGO data generation
- Frequency analysis
- Statistical validation
- Cross-correlation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from experiments.frequency_activation_validator import (
    FrequencyActivationValidator,
    EEGDataGenerator,
    LIGODataGenerator,
    FrequencyAnalyzer,
    DualSystemValidator,
    SystemParameters,
    ValidationResult,
    run_validation,
    F0, PSI_THRESHOLD
)


class TestSystemParameters:
    """Test SystemParameters dataclass."""
    
    def test_default_parameters(self):
        """Test default parameter values."""
        params = SystemParameters()
        
        assert params.f0 == F0
        assert params.duration == 10.0
        assert params.eeg_channels == 256
        assert params.eeg_fs == 4096.0
        assert params.ligo_fs == 4096.0
        
    def test_custom_parameters(self):
        """Test custom parameter initialization."""
        params = SystemParameters(
            duration=5.0,
            eeg_channels=128,
            n_bootstrap=50
        )
        
        assert params.duration == 5.0
        assert params.eeg_channels == 128
        assert params.n_bootstrap == 50


class TestEEGDataGenerator:
    """Test EEG data generation."""
    
    @pytest.fixture
    def eeg_gen(self):
        """Create EEG generator for testing."""
        params = SystemParameters(duration=2.0, eeg_channels=32)
        return EEGDataGenerator(params)
    
    def test_initialization(self, eeg_gen):
        """Test EEG generator initialization."""
        assert eeg_gen.params.eeg_channels == 32
        assert eeg_gen.params.duration == 2.0
        assert len(eeg_gen.t) == eeg_gen.n_samples
        
    def test_brain_rhythms_shape(self, eeg_gen):
        """Test brain rhythm generation shape."""
        rhythms = eeg_gen.generate_brain_rhythms()
        
        assert rhythms.shape == (32, eeg_gen.n_samples)
        assert np.all(np.isfinite(rhythms))
    
    def test_brain_rhythms_content(self, eeg_gen):
        """Test that brain rhythms contain expected frequencies."""
        rhythms = eeg_gen.generate_brain_rhythms()
        
        # Average across channels
        avg_signal = np.mean(rhythms, axis=0)
        
        # Compute spectrum
        fft_vals = np.fft.rfft(avg_signal)
        freqs = np.fft.rfftfreq(len(avg_signal), 1/eeg_gen.params.eeg_fs)
        psd = np.abs(fft_vals)**2
        
        # Should have power in brain rhythm bands
        delta_mask = (freqs >= 0.5) & (freqs <= 4.0)
        alpha_mask = (freqs >= 8.0) & (freqs <= 13.0)
        
        assert np.any(psd[delta_mask] > 0)
        assert np.any(psd[alpha_mask] > 0)
    
    def test_noise_generation(self, eeg_gen):
        """Test EEG noise generation."""
        noise = eeg_gen.generate_noise()
        
        assert noise.shape == (32, eeg_gen.n_samples)
        assert np.all(np.isfinite(noise))
        
        # Check that noise has reasonable statistics
        assert np.std(noise) > 0
    
    def test_signal_injection(self, eeg_gen):
        """Test signal injection."""
        base_data = np.zeros((32, eeg_gen.n_samples))
        freq = 141.7
        amplitude = 5.0
        
        injected = eeg_gen.inject_signal(base_data, freq, amplitude)
        
        # Should have added signal
        assert not np.allclose(injected, base_data)
        
        # Verify frequency content
        avg_signal = np.mean(injected, axis=0)
        fft_vals = np.fft.rfft(avg_signal)
        freqs = np.fft.rfftfreq(len(avg_signal), 1/eeg_gen.params.eeg_fs)
        psd = np.abs(fft_vals)**2
        
        # Find peak near injection frequency
        mask = (freqs >= freq - 2) & (freqs <= freq + 2)
        assert np.max(psd[mask]) > 0
    
    def test_complete_generation(self, eeg_gen):
        """Test complete EEG data generation."""
        data = eeg_gen.generate(inject_f0=True)
        
        assert data.shape == (32, eeg_gen.n_samples)
        assert np.all(np.isfinite(data))
        
    def test_generation_without_signal(self, eeg_gen):
        """Test generation without f₀ injection."""
        data_with = eeg_gen.generate(inject_f0=True)
        data_without = eeg_gen.generate(inject_f0=False)
        
        # Should be different
        assert not np.allclose(data_with, data_without)


class TestLIGODataGenerator:
    """Test LIGO data generation."""
    
    @pytest.fixture
    def ligo_gen(self):
        """Create LIGO generator for testing."""
        params = SystemParameters(duration=2.0)
        return LIGODataGenerator(params)
    
    def test_initialization(self, ligo_gen):
        """Test LIGO generator initialization."""
        assert ligo_gen.params.duration == 2.0
        assert len(ligo_gen.t) == ligo_gen.n_samples
    
    def test_seismic_noise(self, ligo_gen):
        """Test seismic noise generation."""
        noise = ligo_gen.generate_seismic_noise()
        
        assert len(noise) == ligo_gen.n_samples
        assert np.all(np.isfinite(noise))
        
        # Seismic noise should have low-frequency content
        fft_vals = np.fft.rfft(noise)
        freqs = np.fft.rfftfreq(len(noise), 1/ligo_gen.params.ligo_fs)
        psd = np.abs(fft_vals)**2
        
        # More power at low frequencies
        low_freq_mask = freqs < 10
        high_freq_mask = (freqs > 100) & (freqs < 200)
        
        if np.any(low_freq_mask) and np.any(high_freq_mask):
            assert np.mean(psd[low_freq_mask]) > np.mean(psd[high_freq_mask])
    
    def test_shot_noise(self, ligo_gen):
        """Test shot noise generation."""
        noise = ligo_gen.generate_shot_noise()
        
        assert len(noise) == ligo_gen.n_samples
        assert np.all(np.isfinite(noise))
    
    def test_quantum_noise(self, ligo_gen):
        """Test quantum noise generation."""
        noise = ligo_gen.generate_quantum_noise()
        
        assert len(noise) == ligo_gen.n_samples
        assert np.all(np.isfinite(noise))
    
    def test_signal_injection(self, ligo_gen):
        """Test gravitational wave signal injection."""
        base_data = np.zeros(ligo_gen.n_samples)
        freq = 141.7
        amplitude = 1e-21
        
        injected = ligo_gen.inject_signal(base_data, freq, amplitude)
        
        # Should have added signal
        assert not np.allclose(injected, base_data)
    
    def test_complete_generation(self, ligo_gen):
        """Test complete LIGO data generation."""
        data = ligo_gen.generate(inject_f0=True)
        
        assert len(data) == ligo_gen.n_samples
        assert np.all(np.isfinite(data))


class TestFrequencyAnalyzer:
    """Test frequency analysis functionality."""
    
    @pytest.fixture
    def analyzer(self):
        """Create analyzer for testing."""
        return FrequencyAnalyzer(SystemParameters())
    
    def test_spectrum_computation_1d(self, analyzer):
        """Test spectrum computation for 1D data."""
        # Generate test signal
        fs = 1000.0
        t = np.linspace(0, 1, 1000)
        signal = np.sin(2 * np.pi * 50 * t)
        
        freqs, psd = analyzer.compute_spectrum(signal, fs)
        
        assert len(freqs) > 0
        assert len(psd) == len(freqs)
        assert np.all(freqs >= 0)
        assert np.all(psd >= 0)
    
    def test_spectrum_computation_multichannel(self, analyzer):
        """Test spectrum computation for multi-channel data."""
        # Generate test signal
        fs = 1000.0
        t = np.linspace(0, 1, 1000)
        signal = np.array([
            np.sin(2 * np.pi * 50 * t),
            np.sin(2 * np.pi * 50 * t + 0.1),
            np.sin(2 * np.pi * 50 * t - 0.1),
        ])
        
        freqs, psd = analyzer.compute_spectrum(signal, fs)
        
        assert len(freqs) > 0
        assert len(psd) == len(freqs)
    
    def test_peak_detection(self, analyzer):
        """Test peak detection at target frequency."""
        # Generate signal with peak at 141.7 Hz
        fs = 4096.0
        t = np.linspace(0, 2, int(2 * fs))
        signal = 10.0 * np.sin(2 * np.pi * 141.7 * t) + 0.1 * np.random.randn(len(t))
        
        freqs, psd = analyzer.compute_spectrum(signal, fs)
        result = analyzer.detect_peak(freqs, psd, 141.7, freq_window=5.0)
        
        assert 'detected_freq' in result
        assert 'peak_power' in result
        assert 'snr_db' in result
        assert 'coherence' in result
        
        # Should detect frequency close to 141.7 Hz
        assert np.abs(result['detected_freq'] - 141.7) < 2.0
        
        # Should have high SNR
        assert result['snr_db'] > 10.0
    
    def test_bootstrap_significance(self, analyzer):
        """Test bootstrap significance testing."""
        # Generate signal with known peak
        fs = 1000.0
        t = np.linspace(0, 2, 2000)
        signal = 5.0 * np.sin(2 * np.pi * 100 * t) + np.random.randn(len(t))
        
        result = analyzer.bootstrap_significance(signal, fs, 100, n_bootstrap=10)
        
        assert 'p_value' in result
        assert 'ci_lower' in result
        assert 'ci_upper' in result
        
        assert 0 <= result['p_value'] <= 1


class TestValidationResult:
    """Test ValidationResult dataclass."""
    
    def test_passed_property_success(self):
        """Test passed property when validation succeeds."""
        result = ValidationResult(
            system_name="TEST",
            detected_frequency=141.5,
            target_frequency=141.7,
            coherence=0.85,
            snr_db=35.0,
            p_value=0.0001
        )
        
        assert result.passed is True
    
    def test_passed_property_failure_freq(self):
        """Test passed property when frequency doesn't match."""
        result = ValidationResult(
            system_name="TEST",
            detected_frequency=150.0,
            target_frequency=141.7,
            coherence=0.85,
            snr_db=35.0,
            p_value=0.0001
        )
        
        assert result.passed is False
    
    def test_passed_property_failure_coherence(self):
        """Test passed property when coherence is low."""
        result = ValidationResult(
            system_name="TEST",
            detected_frequency=141.5,
            target_frequency=141.7,
            coherence=0.3,
            snr_db=35.0,
            p_value=0.0001
        )
        
        assert result.passed is False
    
    def test_passed_property_failure_pvalue(self):
        """Test passed property when p-value is high."""
        result = ValidationResult(
            system_name="TEST",
            detected_frequency=141.5,
            target_frequency=141.7,
            coherence=0.85,
            snr_db=35.0,
            p_value=0.1
        )
        
        assert result.passed is False


class TestDualSystemValidator:
    """Test dual system validation."""
    
    @pytest.fixture
    def validator(self):
        """Create validator for testing."""
        params = SystemParameters(duration=1.0, eeg_channels=16, n_bootstrap=10)
        return DualSystemValidator(params)
    
    def test_initialization(self, validator):
        """Test validator initialization."""
        assert isinstance(validator.eeg_gen, EEGDataGenerator)
        assert isinstance(validator.ligo_gen, LIGODataGenerator)
        assert isinstance(validator.analyzer, FrequencyAnalyzer)
    
    def test_validate_system(self, validator):
        """Test single system validation."""
        # Generate test data with signal
        fs = 4096.0
        t = np.linspace(0, 1, int(fs))
        data = 5.0 * np.sin(2 * np.pi * F0 * t) + np.random.randn(len(t))
        
        result = validator.validate_system(data, fs, "TEST")
        
        assert isinstance(result, ValidationResult)
        assert result.system_name == "TEST"
        assert result.target_frequency == F0
    
    def test_cross_correlation(self, validator):
        """Test cross-correlation computation."""
        # Generate correlated signals
        t = np.linspace(0, 1, 1000)
        signal1 = np.sin(2 * np.pi * 50 * t) + 0.1 * np.random.randn(len(t))
        signal2 = signal1 + 0.05 * np.random.randn(len(t))
        
        result = validator.compute_cross_correlation(signal1, signal2)
        
        assert 'correlation' in result
        assert 'p_value' in result
        
        # Should be highly correlated
        assert result['correlation'] > 0.8


class TestFrequencyActivationValidator:
    """Test main validator class."""
    
    @pytest.fixture
    def validator(self):
        """Create validator for testing."""
        params = SystemParameters(
            duration=0.5,  # Short for fast tests
            eeg_channels=16,
            n_bootstrap=5
        )
        return FrequencyActivationValidator(params)
    
    def test_initialization(self, validator):
        """Test validator initialization."""
        assert isinstance(validator.validator, DualSystemValidator)
    
    def test_print_results(self, validator, capsys):
        """Test results printing."""
        # Create mock results
        eeg_result = ValidationResult(
            system_name="EEG",
            detected_frequency=141.8,
            coherence=0.75,
            snr_db=38.0,
            p_value=0.0001
        )
        
        ligo_result = ValidationResult(
            system_name="LIGO",
            detected_frequency=141.8,
            coherence=0.75,
            snr_db=35.0,
            p_value=0.0001
        )
        
        results = {
            'eeg': eeg_result,
            'ligo': ligo_result,
            'cross_correlation': {'correlation': 0.999, 'p_value': 0.0001},
            'overall_passed': True
        }
        
        validator.print_results(results)
        
        captured = capsys.readouterr()
        assert "DUAL SYSTEM" in captured.out
        assert "EEG System" in captured.out
        assert "LIGO System" in captured.out
        assert "141.8" in captured.out


class TestIntegration:
    """Integration tests for complete validation pipeline."""
    
    @pytest.mark.slow
    def test_full_validation_pipeline(self):
        """Test complete validation pipeline (slow test)."""
        params = SystemParameters(
            duration=1.0,
            eeg_channels=32,
            n_bootstrap=10
        )
        
        results = run_validation(params, verbose=False)
        
        assert 'eeg' in results
        assert 'ligo' in results
        assert 'cross_correlation' in results
        assert 'overall_passed' in results
        
        # Both systems should detect frequency
        assert isinstance(results['eeg'], ValidationResult)
        assert isinstance(results['ligo'], ValidationResult)
        
        # Detected frequencies should be close to F0
        assert np.abs(results['eeg'].detected_frequency - F0) < 5.0
        assert np.abs(results['ligo'].detected_frequency - F0) < 5.0


class TestNumericalStability:
    """Test numerical stability of algorithms."""
    
    def test_pink_noise_generation(self):
        """Test pink noise generation stability."""
        eeg_gen = EEGDataGenerator(SystemParameters(duration=1.0, eeg_channels=1))
        pink = eeg_gen._generate_pink_noise(1000)
        
        assert len(pink) == 1000
        assert np.all(np.isfinite(pink))
        assert np.std(pink) > 0
    
    def test_spectrum_edge_cases(self):
        """Test spectrum computation edge cases."""
        analyzer = FrequencyAnalyzer()
        
        # Zero signal
        signal = np.zeros(1000)
        freqs, psd = analyzer.compute_spectrum(signal, 1000.0)
        assert np.all(np.isfinite(psd))
        
        # Constant signal
        signal = np.ones(1000)
        freqs, psd = analyzer.compute_spectrum(signal, 1000.0)
        assert np.all(np.isfinite(psd))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
