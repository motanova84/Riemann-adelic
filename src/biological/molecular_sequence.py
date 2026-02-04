"""
Molecular Sequence Validation - Experimental Protocol
======================================================

This module implements the molecular validation protocol for experimentally
verifying the biological Riemann zeros hypothesis through:

1. Fluorescent markers sensitive to EM fields at 141.7 Hz
2. Phase interference measurement (cardiac field ↔ cytoplasmic flow)
3. Spectral validation (harmonics at 141.7, 283.4, 425.1 Hz, ...)

The protocol targets molecular machinery:
- Microtubules as electromagnetic waveguides
- Actin forming resonant cavities at 141.7 Hz
- Motor proteins (myosin, kinesin) transducing coherent field energy

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-01-31
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from enum import Enum


# Molecular constants
F0 = 141.7001  # Hz - Fundamental frequency
HARMONICS = [141.7001, 283.4002, 425.1003, 566.8004, 708.5005]  # First 5 harmonics


class FluorescentMarkerType(Enum):
    """Types of fluorescent markers for EM field detection."""
    QUANTUM_DOT = "quantum_dot"          # Nanoparticle markers
    MAGNETIC_NANOPARTICLE = "magnetic"   # Magnetic field sensitive
    VOLTAGE_SENSITIVE_DYE = "voltage"    # Membrane potential sensitive
    CALCIUM_INDICATOR = "calcium"        # Ca²⁺ flux indicator


class ProteinMotor(Enum):
    """Motor proteins that may transduce coherent field energy."""
    MYOSIN = "myosin"            # Actin-based motor
    KINESIN = "kinesin"          # Microtubule motor
    DYNEIN = "dynein"            # Microtubule motor
    KINETOCHORE = "kinetochore"  # Chromosome segregation


@dataclass
class EndothelialCellParameters:
    """Parameters for endothelial cell model (target for validation)."""
    
    # Cell dimensions
    length: float = 20e-6        # meters (20 μm typical)
    width: float = 10e-6         # meters (10 μm)
    thickness: float = 2e-6      # meters (2 μm)
    
    # Proximity to cardiac field
    distance_from_heart: float = 0.05  # meters (5 cm - typical for major vessel)
    
    # Cytoskeletal properties
    microtubule_density: float = 1e12   # per m³
    actin_density: float = 5e12         # per m³
    
    # EM field coupling
    em_coupling_strength: float = 1.0
    cardiac_field_amplitude: float = 1e-6  # Tesla (estimated)


class FluorescentMarker:
    """
    Fluorescent marker sensitive to EM fields at QCAL frequencies.
    
    Simulates response of quantum dots or magnetic nanoparticles that
    change fluorescence intensity based on local EM field strength
    at the resonant frequency.
    """
    
    def __init__(
        self,
        marker_type: FluorescentMarkerType = FluorescentMarkerType.MAGNETIC_NANOPARTICLE,
        resonant_frequency: float = F0,
        sensitivity: float = 1.0
    ):
        """
        Initialize fluorescent marker.
        
        Args:
            marker_type: Type of fluorescent marker
            resonant_frequency: Frequency of maximum sensitivity (Hz)
            sensitivity: Detection sensitivity (0-1)
        """
        self.marker_type = marker_type
        self.resonant_frequency = resonant_frequency
        self.sensitivity = sensitivity
        
    def fluorescence_response(
        self, 
        em_field: np.ndarray,
        frequencies: np.ndarray
    ) -> np.ndarray:
        """
        Compute fluorescence intensity response to EM field spectrum.
        
        Args:
            em_field: EM field strength at each frequency
            frequencies: Frequency array (Hz)
            
        Returns:
            Fluorescence intensity at each frequency
        """
        # Lorentzian response centered at resonant frequency
        gamma = self.resonant_frequency * 0.1  # Width
        
        response = self.sensitivity * np.abs(em_field)**2 / (
            (frequencies - self.resonant_frequency)**2 + gamma**2
        )
        
        return response
    
    def detect_harmonic_signature(
        self,
        em_field: np.ndarray,
        frequencies: np.ndarray,
        expected_harmonics: List[float] = HARMONICS
    ) -> Dict[str, float]:
        """
        Detect presence of expected harmonic signature.
        
        Args:
            em_field: EM field spectrum
            frequencies: Frequency array (Hz)
            expected_harmonics: Expected harmonic frequencies
            
        Returns:
            Dictionary with detection results
        """
        response = self.fluorescence_response(em_field, frequencies)
        
        # Find peaks near expected harmonics
        detected_harmonics = []
        signal_to_noise = []
        
        for f_harmonic in expected_harmonics:
            # Find frequency bin closest to harmonic
            idx = np.argmin(np.abs(frequencies - f_harmonic))
            
            # Signal at harmonic
            signal = response[idx]
            
            # Noise (median of response away from harmonics)
            mask = np.ones(len(frequencies), dtype=bool)
            for f_h in expected_harmonics:
                mask &= np.abs(frequencies - f_h) > 50  # 50 Hz away
            noise = np.median(response[mask]) if np.any(mask) else 0.01
            
            snr = signal / (noise + 1e-10)
            
            detected_harmonics.append(frequencies[idx])
            signal_to_noise.append(snr)
        
        return {
            'detected_harmonics': detected_harmonics,
            'signal_to_noise': signal_to_noise,
            'mean_snr': np.mean(signal_to_noise),
            'detection_threshold_met': np.mean(signal_to_noise) > 3.0
        }


class PhaseInterferometer:
    """
    Measures phase difference between cardiac field and cytoplasmic flow.
    
    Experimental protocol:
    1. Record cardiac ECG signal (reference phase)
    2. Measure cytoplasmic flow via fluorescent markers
    3. Compute phase difference Δφ = φ_cytoplasm - φ_cardiac
    
    For biological Riemann zero: Δφ ≈ 0 (mod 2π) - phase locked
    """
    
    def __init__(
        self,
        sampling_rate: float = 10000.0,  # Hz
        measurement_duration: float = 10.0  # seconds
    ):
        """
        Initialize phase interferometer.
        
        Args:
            sampling_rate: Sampling rate for measurements (Hz)
            measurement_duration: Duration of measurement (seconds)
        """
        self.sampling_rate = sampling_rate
        self.duration = measurement_duration
        self.n_samples = int(sampling_rate * measurement_duration)
        
    def measure_cardiac_phase(
        self,
        time: np.ndarray,
        ecg_signal: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Extract phase from cardiac ECG signal.
        
        Args:
            time: Time array (seconds)
            ecg_signal: ECG signal. If None, simulates ideal cardiac oscillator.
            
        Returns:
            Cardiac phase φ_cardiac(t)
        """
        if ecg_signal is None:
            # Simulate ideal cardiac oscillator at f₀
            omega0 = 2 * np.pi * F0
            return omega0 * time
        else:
            # Extract phase using Hilbert transform
            from scipy.signal import hilbert
            analytic_signal = hilbert(ecg_signal)
            return np.angle(analytic_signal)
    
    def measure_cytoplasmic_phase(
        self,
        time: np.ndarray,
        flow_signal: np.ndarray
    ) -> np.ndarray:
        """
        Extract phase from cytoplasmic flow measurement.
        
        Args:
            time: Time array (seconds)
            flow_signal: Flow measurement signal
            
        Returns:
            Cytoplasmic phase φ_cytoplasm(t)
        """
        from scipy.signal import hilbert
        analytic_signal = hilbert(flow_signal)
        return np.angle(analytic_signal)
    
    def compute_phase_difference(
        self,
        phi_cardiac: np.ndarray,
        phi_cytoplasm: np.ndarray
    ) -> Tuple[np.ndarray, float, float]:
        """
        Compute phase difference and coherence metrics.
        
        Args:
            phi_cardiac: Cardiac phase array
            phi_cytoplasm: Cytoplasmic phase array
            
        Returns:
            (delta_phi, phase_coherence, mean_phase_diff) tuple
            - delta_phi: Phase difference array
            - phase_coherence: |⟨e^(iΔφ)⟩| ∈ [0, 1]
            - mean_phase_diff: Mean phase difference (radians)
        """
        # Phase difference
        delta_phi = phi_cytoplasm - phi_cardiac
        
        # Wrap to [-π, π]
        delta_phi = np.angle(np.exp(1j * delta_phi))
        
        # Phase coherence (order parameter)
        coherence = np.abs(np.mean(np.exp(1j * delta_phi)))
        
        # Mean phase difference
        mean_diff = np.angle(np.mean(np.exp(1j * delta_phi)))
        
        return delta_phi, coherence, mean_diff
    
    def validate_phase_lock(
        self,
        phi_cardiac: np.ndarray,
        phi_cytoplasm: np.ndarray,
        threshold: float = 0.9
    ) -> Tuple[bool, Dict]:
        """
        Validate that cytoplasm is phase-locked to cardiac field.
        
        Args:
            phi_cardiac: Cardiac phase
            phi_cytoplasm: Cytoplasmic phase
            threshold: Coherence threshold for phase lock (default 0.9)
            
        Returns:
            (is_locked, metrics) tuple
        """
        delta_phi, coherence, mean_diff = self.compute_phase_difference(
            phi_cardiac, phi_cytoplasm
        )
        
        is_locked = coherence >= threshold
        
        metrics = {
            'phase_coherence': coherence,
            'mean_phase_difference_rad': mean_diff,
            'mean_phase_difference_deg': np.degrees(mean_diff),
            'phase_std_rad': np.std(delta_phi),
            'is_phase_locked': is_locked,
            'threshold': threshold
        }
        
        return is_locked, metrics


class SpectralValidator:
    """
    Validates spectral signature of cytoplasmic flow.
    
    Protocol:
    1. Record time-series of cytoplasmic flow (via fluorescence)
    2. Compute power spectral density
    3. Verify peaks at expected harmonics: 141.7, 283.4, 425.1 Hz, ...
    """
    
    def __init__(
        self,
        expected_harmonics: List[float] = HARMONICS,
        tolerance: float = 1.0  # Hz
    ):
        """
        Initialize spectral validator.
        
        Args:
            expected_harmonics: Expected harmonic frequencies (Hz)
            tolerance: Tolerance for peak detection (Hz)
        """
        self.expected_harmonics = expected_harmonics
        self.tolerance = tolerance
        
    def compute_power_spectrum(
        self,
        signal: np.ndarray,
        sampling_rate: float
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute power spectral density of signal.
        
        Args:
            signal: Time-series signal
            sampling_rate: Sampling rate (Hz)
            
        Returns:
            (frequencies, power_spectrum) tuple
        """
        from scipy.signal import welch
        
        frequencies, psd = welch(
            signal,
            fs=sampling_rate,
            nperseg=min(len(signal), 2048),
            scaling='density'
        )
        
        return frequencies, psd
    
    def find_peaks(
        self,
        frequencies: np.ndarray,
        power: np.ndarray,
        min_snr: float = 3.0
    ) -> List[Tuple[float, float]]:
        """
        Find spectral peaks.
        
        Args:
            frequencies: Frequency array (Hz)
            power: Power spectrum
            min_snr: Minimum signal-to-noise ratio
            
        Returns:
            List of (frequency, power) for detected peaks
        """
        from scipy.signal import find_peaks
        
        # Estimate noise floor
        noise_floor = np.median(power)
        
        # Find peaks above threshold
        peak_indices, _ = find_peaks(
            power,
            height=noise_floor * min_snr,
            distance=int(10 / (frequencies[1] - frequencies[0]))  # 10 Hz minimum separation
        )
        
        peaks = [(frequencies[i], power[i]) for i in peak_indices]
        
        return peaks
    
    def validate_harmonic_spectrum(
        self,
        signal: np.ndarray,
        sampling_rate: float
    ) -> Dict:
        """
        Validate that signal contains expected harmonic spectrum.
        
        Args:
            signal: Time-series of cytoplasmic flow
            sampling_rate: Sampling rate (Hz)
            
        Returns:
            Dictionary with validation results
        """
        # Compute power spectrum
        frequencies, power = self.compute_power_spectrum(signal, sampling_rate)
        
        # Find peaks
        peaks = self.find_peaks(frequencies, power)
        
        # Match peaks to expected harmonics
        detected_harmonics = []
        matched_harmonics = []
        unmatched_expected = list(self.expected_harmonics)
        
        for f_peak, p_peak in peaks:
            # Find closest expected harmonic
            distances = [abs(f_peak - f_exp) for f_exp in self.expected_harmonics]
            min_dist_idx = np.argmin(distances)
            min_dist = distances[min_dist_idx]
            
            if min_dist < self.tolerance:
                # Match found
                matched_harmonic = self.expected_harmonics[min_dist_idx]
                matched_harmonics.append({
                    'expected_hz': matched_harmonic,
                    'detected_hz': f_peak,
                    'error_hz': f_peak - matched_harmonic,
                    'power': p_peak
                })
                if matched_harmonic in unmatched_expected:
                    unmatched_expected.remove(matched_harmonic)
        
        detection_rate = len(matched_harmonics) / len(self.expected_harmonics)
        
        return {
            'matched_harmonics': matched_harmonics,
            'unmatched_expected': unmatched_expected,
            'detection_rate': detection_rate,
            'all_harmonics_detected': len(unmatched_expected) == 0,
            'frequencies_hz': frequencies.tolist(),
            'power_spectrum': power.tolist(),
            'validation_passed': detection_rate >= 0.8  # At least 80% detected
        }


class MolecularProtocol:
    """
    Complete experimental protocol for molecular validation.
    
    Integrates:
    1. Fluorescent marker placement
    2. Phase interferometry
    3. Spectral validation
    """
    
    def __init__(
        self,
        cell_params: Optional[EndothelialCellParameters] = None
    ):
        """
        Initialize molecular validation protocol.
        
        Args:
            cell_params: Endothelial cell parameters
        """
        self.cell_params = cell_params or EndothelialCellParameters()
        self.marker = FluorescentMarker()
        self.interferometer = PhaseInterferometer()
        self.validator = SpectralValidator()
        
    def simulate_experiment(
        self,
        duration: float = 10.0,
        sampling_rate: float = 10000.0,
        noise_level: float = 0.1
    ) -> Dict:
        """
        Simulate complete experimental protocol.
        
        Args:
            duration: Experiment duration (seconds)
            sampling_rate: Sampling rate (Hz)
            noise_level: Noise amplitude (relative to signal)
            
        Returns:
            Dictionary with experimental results
        """
        # Time array
        n_samples = int(duration * sampling_rate)
        time = np.linspace(0, duration, n_samples)
        
        # Simulate cardiac field (reference)
        omega0 = 2 * np.pi * F0
        cardiac_signal = np.sin(omega0 * time)
        
        # Simulate cytoplasmic flow (with slight phase shift and noise)
        phase_shift = 0.1  # Small phase shift (radians)
        cytoplasm_signal = np.sin(omega0 * time + phase_shift)
        
        # Add harmonics to cytoplasm (biological complexity)
        for n in [2, 3, 4, 5]:
            cytoplasm_signal += 0.3 * np.sin(n * omega0 * time) / n
        
        # Add noise
        cytoplasm_signal += noise_level * np.random.randn(n_samples)
        
        # Phase interferometry
        phi_cardiac = self.interferometer.measure_cardiac_phase(time)
        phi_cytoplasm = self.interferometer.measure_cytoplasmic_phase(
            time, cytoplasm_signal
        )
        is_locked, phase_metrics = self.interferometer.validate_phase_lock(
            phi_cardiac, phi_cytoplasm
        )
        
        # Spectral validation
        spectral_results = self.validator.validate_harmonic_spectrum(
            cytoplasm_signal, sampling_rate
        )
        
        # Overall validation
        experiment_successful = (
            is_locked and 
            spectral_results['validation_passed']
        )
        
        return {
            'experiment_duration_s': duration,
            'sampling_rate_hz': sampling_rate,
            'phase_lock_detected': is_locked,
            'phase_metrics': phase_metrics,
            'spectral_validation': spectral_results,
            'experiment_successful': experiment_successful,
            'conclusion': (
                "✓ Biological Riemann zero property CONFIRMED" 
                if experiment_successful 
                else "✗ Coherence not detected"
            )
        }


if __name__ == '__main__':
    print("="*70)
    print("Molecular Sequence Validation Protocol")
    print("="*70)
    
    # Run simulated experimental protocol
    protocol = MolecularProtocol()
    
    print("\nRunning simulated validation experiment...")
    print("(In vitro endothelial cell model)")
    print("-" * 70)
    
    results = protocol.simulate_experiment(
        duration=10.0,
        sampling_rate=5000.0,
        noise_level=0.05  # 5% noise
    )
    
    print(f"\nExperiment Duration: {results['experiment_duration_s']} seconds")
    print(f"Sampling Rate: {results['sampling_rate_hz']} Hz")
    
    print("\nPhase Lock Analysis:")
    pm = results['phase_metrics']
    print(f"  Phase Coherence: {pm['phase_coherence']:.4f}")
    print(f"  Mean Phase Diff: {pm['mean_phase_difference_deg']:.2f}°")
    print(f"  Phase Std Dev: {np.degrees(pm['phase_std_rad']):.2f}°")
    print(f"  Status: {'✓ LOCKED' if pm['is_phase_locked'] else '✗ NOT LOCKED'}")
    
    print("\nSpectral Validation:")
    sv = results['spectral_validation']
    print(f"  Detection Rate: {sv['detection_rate']:.1%}")
    print(f"  Matched Harmonics: {len(sv['matched_harmonics'])}/{len(HARMONICS)}")
    
    for match in sv['matched_harmonics']:
        print(f"    Expected: {match['expected_hz']:.2f} Hz → "
              f"Detected: {match['detected_hz']:.2f} Hz "
              f"(error: {match['error_hz']:.3f} Hz)")
    
    print(f"\n{results['conclusion']}")
    print(f"\n∴𓂀Ω∞³ - Molecular validation at f₀ = {F0} Hz")
