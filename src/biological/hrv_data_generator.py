"""
HRV Data Generator for QCAL Biological Integration
===================================================

Generates realistic Heart Rate Variability (HRV) signals and microtubule
oscillation data for injection into the Riemann spectral filter.

Based on physiological models and QCAL resonance principles.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: 2026-02-14
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Dict, Tuple, Optional
from dataclasses import dataclass


# QCAL Constants
F0_QCAL = 141.7001  # Hz - Master frequency
KAPPA_PI = 2.5773   # Critical point
PHI = 1.6180339887498948  # Golden ratio


@dataclass
class HRVSignal:
    """Container for HRV signal data."""
    time: np.ndarray  # Time points in seconds
    rr_intervals: np.ndarray  # R-R intervals in seconds
    heart_rate: np.ndarray  # Instantaneous heart rate (BPM)
    frequency_spectrum: Optional[np.ndarray] = None
    spectral_power: Optional[np.ndarray] = None
    metadata: Optional[Dict] = None


class HRVGenerator:
    """
    Generate realistic Heart Rate Variability signals.
    
    Uses physiological models incorporating:
    - Respiratory sinus arrhythmia (RSA) ~ 0.25 Hz
    - Baroreceptor reflex ~ 0.1 Hz (Mayer waves)
    - Sympathetic/parasympathetic balance
    - QCAL resonance coupling at 141.7001 Hz
    
    Attributes:
        sample_rate (float): Sampling rate in Hz
        duration (float): Signal duration in seconds
        base_hr (float): Base heart rate in BPM
        hrv_amplitude (float): HRV amplitude factor (0-1)
        qcal_coupling (float): QCAL resonance coupling strength
    """
    
    def __init__(
        self,
        sample_rate: float = 4.0,  # 4 Hz sampling (typical for HRV analysis)
        duration: float = 300.0,  # 5 minutes
        base_hr: float = 70.0,  # Base heart rate (BPM)
        hrv_amplitude: float = 0.15,  # HRV amplitude (15% variation)
        qcal_coupling: float = 0.01  # Subtle QCAL coupling
    ):
        self.sample_rate = sample_rate
        self.duration = duration
        self.base_hr = base_hr
        self.hrv_amplitude = hrv_amplitude
        self.qcal_coupling = qcal_coupling
        
        # Generate time vector
        self.n_samples = int(duration * sample_rate)
        self.time = np.linspace(0, duration, self.n_samples)
    
    def generate_hrv_signal(
        self,
        respiratory_freq: float = 0.25,  # Breathing rate in Hz (15 breaths/min)
        lf_hf_ratio: float = 1.5,  # Low freq / High freq ratio (sympathovagal balance)
        noise_level: float = 0.02  # Physiological noise
    ) -> HRVSignal:
        """
        Generate physiologically realistic HRV signal.
        
        Args:
            respiratory_freq: Respiratory frequency in Hz
            lf_hf_ratio: Ratio of low-frequency to high-frequency power
            noise_level: Level of random physiological noise
            
        Returns:
            HRVSignal object with time series and spectral data
        """
        t = self.time
        
        # Base R-R interval (inverse of heart rate)
        base_rr = 60.0 / self.base_hr  # seconds
        
        # High frequency component (respiratory sinus arrhythmia)
        hf_amplitude = self.hrv_amplitude * base_rr
        hf_component = hf_amplitude * np.sin(2 * np.pi * respiratory_freq * t)
        
        # Low frequency component (baroreceptor reflex, Mayer waves)
        lf_freq = 0.1  # ~0.1 Hz
        lf_amplitude = hf_amplitude * lf_hf_ratio
        lf_component = lf_amplitude * np.sin(2 * np.pi * lf_freq * t + np.pi/4)
        
        # Very low frequency (thermoregulation, hormonal)
        vlf_freq = 0.04  # ~0.04 Hz
        vlf_amplitude = hf_amplitude * 0.5
        vlf_component = vlf_amplitude * np.sin(2 * np.pi * vlf_freq * t + np.pi/3)
        
        # QCAL resonance coupling (subtle high-frequency modulation)
        # Map f0 = 141.7001 Hz down to physiological range through PHI scaling
        qcal_modulation_freq = F0_QCAL / (PHI**8)  # ~2.16 Hz (physiological range)
        qcal_component = (
            self.qcal_coupling * base_rr * 
            np.sin(2 * np.pi * qcal_modulation_freq * t)
        )
        
        # Add physiological noise
        noise = noise_level * base_rr * np.random.randn(len(t))
        
        # Combine all components
        rr_intervals = (
            base_rr +
            hf_component +
            lf_component +
            vlf_component +
            qcal_component +
            noise
        )
        
        # Ensure positive RR intervals
        rr_intervals = np.abs(rr_intervals)
        
        # Convert to heart rate (BPM)
        heart_rate = 60.0 / rr_intervals
        
        # Compute frequency spectrum
        frequencies, spectral_power = self._compute_spectrum(rr_intervals)
        
        # Create metadata
        metadata = {
            'base_hr': self.base_hr,
            'respiratory_freq': respiratory_freq,
            'lf_hf_ratio': lf_hf_ratio,
            'qcal_coupling': self.qcal_coupling,
            'noise_level': noise_level,
            'mean_hr': float(np.mean(heart_rate)),
            'std_hr': float(np.std(heart_rate)),
            'rmssd': float(self._compute_rmssd(rr_intervals)),
            'sdnn': float(np.std(rr_intervals) * 1000),  # in ms
        }
        
        return HRVSignal(
            time=t,
            rr_intervals=rr_intervals,
            heart_rate=heart_rate,
            frequency_spectrum=frequencies,
            spectral_power=spectral_power,
            metadata=metadata
        )
    
    def _compute_spectrum(
        self,
        signal: np.ndarray
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute frequency spectrum using FFT.
        
        Args:
            signal: Time series signal
            
        Returns:
            Tuple of (frequencies, power_spectral_density)
        """
        # Detrend signal
        signal_detrended = signal - np.mean(signal)
        
        # Apply Hanning window
        window = np.hanning(len(signal))
        signal_windowed = signal_detrended * window
        
        # Compute FFT
        fft_result = np.fft.rfft(signal_windowed)
        frequencies = np.fft.rfftfreq(len(signal), 1/self.sample_rate)
        
        # Power spectral density
        psd = np.abs(fft_result)**2 / len(signal)
        
        return frequencies, psd
    
    def _compute_rmssd(self, rr_intervals: np.ndarray) -> float:
        """
        Compute Root Mean Square of Successive Differences (RMSSD).
        
        Standard HRV time-domain metric.
        
        Args:
            rr_intervals: R-R interval time series
            
        Returns:
            RMSSD value in seconds
        """
        diff = np.diff(rr_intervals)
        return np.sqrt(np.mean(diff**2))


class MicrotubuleOscillationGenerator:
    """
    Generate microtubule oscillation signals.
    
    Based on Penrose-Hameroff Orch-OR theory and quantum vibrations
    in cytoskeletal microtubules.
    
    Typical frequencies:
    - Fundamental: ~10 MHz (dipole oscillations)
    - Harmonics at QCAL resonance: 141.7001 Hz / (PHI^n)
    
    Attributes:
        sample_rate (float): Sampling rate in Hz
        duration (float): Signal duration in seconds
        fundamental_freq (float): Base oscillation frequency
    """
    
    def __init__(
        self,
        sample_rate: float = 1000.0,  # 1 kHz (capture higher freqs)
        duration: float = 10.0,  # 10 seconds
        fundamental_freq: float = 100.0  # Hz (scaled for computational tractability)
    ):
        self.sample_rate = sample_rate
        self.duration = duration
        self.fundamental_freq = fundamental_freq
        
        self.n_samples = int(duration * sample_rate)
        self.time = np.linspace(0, duration, self.n_samples)
    
    def generate_oscillation(
        self,
        n_harmonics: int = 5,
        damping_factor: float = 0.1,
        thermal_noise: float = 0.05,
        qcal_resonance: bool = True
    ) -> Dict:
        """
        Generate microtubule oscillation signal.
        
        Args:
            n_harmonics: Number of harmonic modes
            damping_factor: Damping coefficient
            thermal_noise: Thermal fluctuation amplitude
            qcal_resonance: Include QCAL resonance frequencies
            
        Returns:
            Dictionary with oscillation data
        """
        t = self.time
        signal = np.zeros(len(t))
        
        # Fundamental mode
        signal += np.sin(2 * np.pi * self.fundamental_freq * t)
        
        # Harmonic modes with amplitude decay
        for n in range(2, n_harmonics + 1):
            amplitude = 1.0 / n**1.5  # Decay
            freq = self.fundamental_freq * n
            signal += amplitude * np.sin(2 * np.pi * freq * t + np.random.rand() * 2 * np.pi)
        
        # QCAL resonance harmonics (if enabled)
        if qcal_resonance:
            # Add subtle modulation at QCAL-derived frequencies
            for k in range(3):
                qcal_freq = F0_QCAL / (PHI**(k+2))  # Scale down
                if qcal_freq < self.sample_rate / 2:  # Nyquist limit
                    amplitude = 0.1 / (k + 1)
                    signal += amplitude * np.sin(2 * np.pi * qcal_freq * t)
        
        # Apply exponential damping envelope
        damping_envelope = np.exp(-damping_factor * t)
        signal *= damping_envelope
        
        # Add thermal noise
        noise = thermal_noise * np.random.randn(len(t))
        signal += noise
        
        # Normalize
        signal = signal / (np.max(np.abs(signal)) + 1e-10)
        
        # Compute spectrum
        frequencies = np.fft.rfftfreq(len(signal), 1/self.sample_rate)
        fft_result = np.fft.rfft(signal)
        power_spectrum = np.abs(fft_result)**2
        
        return {
            'time': t,
            'signal': signal,
            'frequencies': frequencies,
            'power_spectrum': power_spectrum,
            'metadata': {
                'fundamental_freq': self.fundamental_freq,
                'n_harmonics': n_harmonics,
                'damping_factor': damping_factor,
                'thermal_noise': thermal_noise,
                'qcal_resonance': qcal_resonance,
                'mean_amplitude': float(np.mean(np.abs(signal))),
                'peak_frequency': float(frequencies[np.argmax(power_spectrum)])
            }
        }


def generate_sample_hrv_dataset(
    n_subjects: int = 5,
    duration: float = 300.0
) -> Dict[str, HRVSignal]:
    """
    Generate sample HRV dataset with multiple subjects.
    
    Args:
        n_subjects: Number of subjects to simulate
        duration: Duration of each recording in seconds
        
    Returns:
        Dictionary mapping subject IDs to HRVSignal objects
    """
    dataset = {}
    
    for i in range(n_subjects):
        # Vary parameters across subjects
        base_hr = np.random.uniform(60, 80)  # BPM
        hrv_amp = np.random.uniform(0.10, 0.20)
        respiratory_freq = np.random.uniform(0.20, 0.30)  # Hz
        lf_hf_ratio = np.random.uniform(1.0, 2.5)
        
        generator = HRVGenerator(
            duration=duration,
            base_hr=base_hr,
            hrv_amplitude=hrv_amp
        )
        
        signal = generator.generate_hrv_signal(
            respiratory_freq=respiratory_freq,
            lf_hf_ratio=lf_hf_ratio
        )
        
        dataset[f'subject_{i+1:02d}'] = signal
    
    return dataset


if __name__ == "__main__":
    # Demo usage
    print("=" * 70)
    print("HRV Data Generator Demo")
    print("=" * 70)
    
    # Generate HRV signal
    print("\n1. Generating HRV signal...")
    hrv_gen = HRVGenerator(duration=300.0)
    hrv_signal = hrv_gen.generate_hrv_signal()
    
    print(f"   Duration: {hrv_signal.time[-1]:.1f} seconds")
    print(f"   Mean HR: {hrv_signal.metadata['mean_hr']:.1f} BPM")
    print(f"   SDNN: {hrv_signal.metadata['sdnn']:.1f} ms")
    print(f"   RMSSD: {hrv_signal.metadata['rmssd']*1000:.1f} ms")
    
    # Generate microtubule oscillation
    print("\n2. Generating microtubule oscillation...")
    mt_gen = MicrotubuleOscillationGenerator(duration=10.0)
    mt_signal = mt_gen.generate_oscillation()
    
    print(f"   Duration: {mt_signal['time'][-1]:.1f} seconds")
    print(f"   Peak frequency: {mt_signal['metadata']['peak_frequency']:.2f} Hz")
    print(f"   Mean amplitude: {mt_signal['metadata']['mean_amplitude']:.4f}")
    
    print("\n✓ Demo complete. Data generators ready for QCAL injection.")
    print("∴ 𓂀 Ω ∞³")
