#!/usr/bin/env python3
"""
QCAL Vibro-Fluorescent Experimental Framework
==============================================

This module implements the theoretical and computational framework for validating
the QCAL (Quantum Coherence Adelic Lattice) framework through vibro-fluorescent
coupling experiments in proteins (e.g., GFP - Green Fluorescent Protein).

Theoretical Foundation:
-----------------------
The framework is based on the master equation for vibro-fluorescent coupling:

    H_total = H_protein + H_campo + H_acoplamiento

Where:
    H_acoplamiento = μ·E(ω,t) + Q:∇E(ω,t) + χ⁽²⁾E² + χ⁽³⁾E³ + ...

Key Components:
    - μ·E: Electric dipole transition
    - Q:∇E: Quadrupole + vibrational coupling (critical for QCAL)
    - Nonlinear terms: Specific spectral response

QCAL Frequency: 141.7001 Hz (fundamental cosmic resonance)

Experimental Design:
-------------------
The experiment tests whether biological systems show spectral structure
(peaks at specific frequencies) independent of total energy, as predicted
by QCAL, versus flat frequency response predicted by traditional biology.

Critical Test:
    If ΔF(141.7 Hz) / ΔF(100 Hz) > 1.5 with same energy → QCAL supported
    If ΔF(ω) = constant ± error → QCAL falsified

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Callable
from dataclasses import dataclass, field
from scipy import signal, fft, stats
from scipy.optimize import curve_fit
import warnings


# QCAL Fundamental Constants
QCAL_CARRIER_FREQUENCY = 141.7001  # Hz - Fundamental cosmic resonance
QCAL_COHERENCE_THRESHOLD = 0.888   # Critical amplitude threshold
QCAL_SIGNATURE_RATIO = 1.5         # Minimum ratio for QCAL confirmation


@dataclass
class ExperimentalParameters:
    """
    Parameters for vibro-fluorescent experimental setup.
    
    Attributes:
        carrier_frequency: ω₀ = 141.7001 Hz (QCAL portadora)
        modulation_frequencies: ωₚ sweep range (0.1-10 Hz, biological range)
        modulation_index: m ∈ [0, 1] (amplitude modulation depth)
        amplitude: A₀ (constant energy across all frequencies)
        sampling_rate: Data acquisition rate (>10 kHz recommended)
        duration: Measurement duration per frequency (seconds)
        num_samples: Number of samples per measurement
    """
    carrier_frequency: float = QCAL_CARRIER_FREQUENCY
    modulation_frequencies: np.ndarray = field(
        default_factory=lambda: np.linspace(0.1, 10.0, 100)
    )
    modulation_index: float = 0.5
    amplitude: float = 1.0
    sampling_rate: float = 10000.0  # Hz
    duration: float = 10.0  # seconds
    num_samples: int = field(init=False)
    
    def __post_init__(self):
        """Calculate number of samples from duration and sampling rate."""
        self.num_samples = int(self.duration * self.sampling_rate)


@dataclass
class ProteinDynamicsParameters:
    """
    Parameters for protein domain dynamics (coupled oscillator model).
    
    Based on Section IV equations:
        mᵢ d²xᵢ/dt² + γᵢ dxᵢ/dt + kᵢxᵢ + Σⱼ κᵢⱼ(xᵢ - xⱼ) = qᵢE(ωₚ,t)
    
    Attributes:
        num_domains: Number of protein domains
        masses: mᵢ - Effective masses (normalized units)
        damping: γᵢ - Damping coefficients
        spring_constants: kᵢ - Elastic constants
        coupling_constants: κᵢⱼ - Inter-domain coupling
        charges: qᵢ - Effective charges
    """
    num_domains: int = 5
    masses: np.ndarray = field(
        default_factory=lambda: np.ones(5)
    )
    damping: np.ndarray = field(
        default_factory=lambda: 0.1 * np.ones(5)
    )
    spring_constants: np.ndarray = field(
        default_factory=lambda: (2 * np.pi * QCAL_CARRIER_FREQUENCY)**2 * np.ones(5)
    )
    coupling_constants: np.ndarray = field(init=False)
    charges: np.ndarray = field(
        default_factory=lambda: np.ones(5)
    )
    
    def __post_init__(self):
        """Initialize coupling matrix."""
        # Create nearest-neighbor coupling matrix
        self.coupling_constants = np.zeros((self.num_domains, self.num_domains))
        for i in range(self.num_domains - 1):
            self.coupling_constants[i, i+1] = 0.5
            self.coupling_constants[i+1, i] = 0.5


class QCALSignalGenerator:
    """
    Generate modulated QCAL signals with constant energy across frequencies.
    
    Implements Section II equation:
        Ψ_input(t) = A₀[1 + m·sin(ωₚt)]·sin(ω₀t)
    
    With critical constraint:
        E_total = ∫|Ψ_input(t)|²dt = constant ∀ ωₚ
    """
    
    def __init__(self, params: ExperimentalParameters):
        """
        Initialize signal generator.
        
        Args:
            params: Experimental parameters
        """
        self.params = params
        
    def generate_signal(
        self, 
        modulation_frequency: float,
        normalize_energy: bool = True
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Generate modulated QCAL signal.
        
        Args:
            modulation_frequency: ωₚ (Hz)
            normalize_energy: If True, normalize to constant energy
            
        Returns:
            (time_array, signal_array)
        """
        t = np.linspace(0, self.params.duration, self.params.num_samples)
        
        # Modulated amplitude: A(t) = A₀[1 + m·sin(ωₚt)]
        modulation = 1 + self.params.modulation_index * np.sin(
            2 * np.pi * modulation_frequency * t
        )
        
        # Carrier signal: sin(ω₀t)
        carrier = np.sin(2 * np.pi * self.params.carrier_frequency * t)
        
        # Combined signal
        signal_array = self.params.amplitude * modulation * carrier
        
        if normalize_energy:
            # Normalize to constant total energy
            energy = np.sum(signal_array**2) * (t[1] - t[0])
            signal_array = signal_array / np.sqrt(energy)
            
        return t, signal_array
    
    def calculate_energy(self, signal_array: np.ndarray) -> float:
        """
        Calculate total signal energy.
        
        Args:
            signal_array: Signal to analyze
            
        Returns:
            E_total = ∫|Ψ|²dt
        """
        dt = self.params.duration / self.params.num_samples
        return np.sum(signal_array**2) * dt


class ProteinOscillatorModel:
    """
    Coupled oscillator model for protein domain dynamics.
    
    Implements Section IV equations for protein response to QCAL field.
    """
    
    def __init__(self, protein_params: ProteinDynamicsParameters):
        """
        Initialize protein oscillator model.
        
        Args:
            protein_params: Protein dynamics parameters
        """
        self.params = protein_params
        
    def calculate_response_fourier(
        self,
        omega: float,
        domain_index: int = 0
    ) -> complex:
        """
        Calculate frequency domain response for a protein domain.
        
        Implements Section IV equation:
            x̃ᵢ(ω) = [qᵢ/(mᵢ(ωᵢ² - ω²) + iγᵢω)]·Ẽ(ω)
        
        Args:
            omega: Angular frequency (rad/s)
            domain_index: Which protein domain (0 to num_domains-1)
            
        Returns:
            Complex response amplitude
        """
        i = domain_index
        m = self.params.masses[i]
        gamma = self.params.damping[i]
        k = self.params.spring_constants[i]
        q = self.params.charges[i]
        
        omega_res = np.sqrt(k / m)  # Resonance frequency
        
        # Response function (normalized E = 1)
        denominator = m * (omega_res**2 - omega**2) + 1j * gamma * omega
        response = q / denominator
        
        return response
    
    def calculate_resonance_frequency(self, domain_index: int = 0) -> float:
        """
        Calculate resonance frequency for a protein domain.
        
        Implements: ω_res = √(k_eff/m_eff)
        
        Args:
            domain_index: Which protein domain
            
        Returns:
            Resonance frequency (rad/s)
        """
        i = domain_index
        omega_res = np.sqrt(self.params.spring_constants[i] / self.params.masses[i])
        return omega_res
    
    def check_qcal_resonance(self, domain_index: int = 0) -> bool:
        """
        Check if domain resonates at QCAL frequency.
        
        Expected: ω_res ≈ 2π × 141.7 Hz
        
        Args:
            domain_index: Which protein domain
            
        Returns:
            True if resonance matches QCAL frequency within 5%
        """
        omega_res = self.calculate_resonance_frequency(domain_index)
        f_res = omega_res / (2 * np.pi)
        
        relative_error = abs(f_res - QCAL_CARRIER_FREQUENCY) / QCAL_CARRIER_FREQUENCY
        return relative_error < 0.05


class FluorescenceResponseModel:
    """
    Model fluorescence response from protein conformational changes.
    
    Implements Section III & V equations for GFP chromophore response.
    """
    
    def __init__(
        self,
        protein_model: ProteinOscillatorModel,
        baseline_fluorescence: float = 1.0
    ):
        """
        Initialize fluorescence response model.
        
        Args:
            protein_model: Protein oscillator model
            baseline_fluorescence: F₀ (fluorescence without stimulation)
        """
        self.protein = protein_model
        self.F0 = baseline_fluorescence
        
    def calculate_fluorescence_response(
        self,
        modulation_frequency: float,
        signal_amplitude: float = 1.0,
        phase_lag: float = 0.0
    ) -> Dict[str, float]:
        """
        Calculate fluorescence response to modulated QCAL field.
        
        Implements Section III equation:
            F(t) = F₀ + ΔF(ωₚ)·[1 + η·sin(ωₚt + φ(ωₚ))]
        
        Args:
            modulation_frequency: ωₚ (Hz)
            signal_amplitude: Field amplitude
            phase_lag: φ(ωₚ) - phase between stimulus and response
            
        Returns:
            Dictionary with:
                - delta_F: Response amplitude
                - eta: Information transfer efficiency
                - phase: Phase lag
        """
        omega_p = 2 * np.pi * modulation_frequency
        
        # Calculate protein domain responses
        responses = []
        for i in range(self.protein.params.num_domains):
            response = self.protein.calculate_response_fourier(omega_p, i)
            responses.append(abs(response))
        
        # Average response across domains
        avg_response = np.mean(responses)
        
        # Fluorescence amplitude change (proportional to conformational change)
        delta_F = signal_amplitude * avg_response
        
        # Information transfer efficiency (QCAL key parameter)
        # For now, model as frequency-dependent
        eta = self._calculate_efficiency(modulation_frequency)
        
        return {
            'delta_F': delta_F,
            'eta': eta,
            'phase': phase_lag,
            'F0': self.F0
        }
    
    def _calculate_efficiency(self, modulation_frequency: float) -> float:
        """
        Calculate frequency-dependent information transfer efficiency.
        
        QCAL prediction: η varies with ωₚ even at constant energy.
        
        Args:
            modulation_frequency: ωₚ (Hz)
            
        Returns:
            η - efficiency parameter
        """
        # Check for resonance with QCAL harmonics
        qcal_harmonics = [QCAL_CARRIER_FREQUENCY / n for n in [1, 2, 3, 13, 17]]
        
        # Maximum efficiency at resonances
        efficiency = 0.1  # Baseline
        for harmonic in qcal_harmonics:
            # Lorentzian peak at each harmonic
            width = 5.0  # Hz
            efficiency += 0.5 * (width**2) / (
                (modulation_frequency - harmonic)**2 + width**2
            )
        
        return min(efficiency, 1.0)  # Cap at 1.0


class QCALPredictionValidator:
    """
    Validate QCAL predictions against experimental data.
    
    Implements Section VI & VII falsification tests.
    """
    
    def __init__(self):
        """Initialize validator."""
        self.qcal_harmonics = [
            QCAL_CARRIER_FREQUENCY / n for n in [1, 2, 3, 13, 17]
        ]
        
    def predict_resonance_peaks(
        self,
        frequencies: np.ndarray,
        amplitudes: np.ndarray
    ) -> Dict[str, np.ndarray]:
        """
        Predict resonance peaks according to QCAL.
        
        Implements Section VI Prediction 1:
            ΔF_max occurs when ωₚ/ω₀ = p/q (small integers)
        
        Args:
            frequencies: Frequency sweep array
            amplitudes: Measured response amplitudes
            
        Returns:
            Dictionary with predicted peak locations and amplitudes
        """
        peaks = []
        peak_freqs = []
        
        for harmonic in self.qcal_harmonics:
            # Find closest measured frequency
            idx = np.argmin(np.abs(frequencies - harmonic))
            if idx > 0 and idx < len(frequencies) - 1:
                # Check if it's a local maximum
                if (amplitudes[idx] > amplitudes[idx-1] and 
                    amplitudes[idx] > amplitudes[idx+1]):
                    peaks.append(amplitudes[idx])
                    peak_freqs.append(frequencies[idx])
        
        return {
            'peak_frequencies': np.array(peak_freqs),
            'peak_amplitudes': np.array(peaks),
            'harmonic_predictions': np.array(self.qcal_harmonics)
        }
    
    def fit_lorentzian_structure(
        self,
        frequencies: np.ndarray,
        amplitudes: np.ndarray
    ) -> Dict[str, any]:
        """
        Fit harmonic Lorentzian structure to data.
        
        Implements Section VI Prediction 2:
            ΔF(ω) = Σₖ Aₖ / [(ω - kω₀)² + Γₖ²]
        
        Args:
            frequencies: Frequency array
            amplitudes: Response amplitudes
            
        Returns:
            Fit parameters and quality metrics
        """
        def lorentzian_sum(omega, *params):
            """Sum of Lorentzian peaks."""
            # params = [A1, Gamma1, A2, Gamma2, ...]
            result = np.zeros_like(omega)
            n_peaks = len(self.qcal_harmonics)
            
            for i in range(n_peaks):
                if 2*i + 1 < len(params):
                    A = params[2*i]
                    Gamma = params[2*i + 1]
                    omega_peak = self.qcal_harmonics[i]
                    result += A / ((omega - omega_peak)**2 + Gamma**2)
            
            return result
        
        # Initial guess for parameters
        n_peaks = len(self.qcal_harmonics)
        initial_guess = []
        for _ in range(n_peaks):
            initial_guess.extend([1.0, 5.0])  # [Amplitude, Width]
        
        try:
            # Fit the model
            popt, pcov = curve_fit(
                lorentzian_sum,
                frequencies,
                amplitudes,
                p0=initial_guess,
                maxfev=5000
            )
            
            # Calculate R² (goodness of fit)
            fitted = lorentzian_sum(frequencies, *popt)
            residuals = amplitudes - fitted
            ss_res = np.sum(residuals**2)
            ss_tot = np.sum((amplitudes - np.mean(amplitudes))**2)
            r_squared = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0
            
            return {
                'parameters': popt,
                'covariance': pcov,
                'r_squared': r_squared,
                'fitted_curve': fitted,
                'residuals': residuals
            }
        except RuntimeError:
            warnings.warn("Lorentzian fit did not converge")
            return {
                'parameters': None,
                'r_squared': 0.0
            }
    
    def test_coherence_threshold(
        self,
        amplitude: float
    ) -> Dict[str, any]:
        """
        Test for coherence threshold bifurcation.
        
        Implements Section VI Prediction 3:
            Ψ_crítico = 0.888 → ∂²ΔF/∂ω² changes sign
        
        Args:
            amplitude: Signal amplitude (normalized)
            
        Returns:
            Test results including bifurcation status
        """
        threshold_crossed = amplitude > QCAL_COHERENCE_THRESHOLD
        
        return {
            'amplitude': amplitude,
            'threshold': QCAL_COHERENCE_THRESHOLD,
            'crossed': threshold_crossed,
            'interpretation': (
                'Coherent regime' if threshold_crossed 
                else 'Below coherence threshold'
            )
        }
    
    def anova_spectral_test(
        self,
        frequencies: np.ndarray,
        responses: np.ndarray,
        num_replicates: int = 3
    ) -> Dict[str, float]:
        """
        Perform ANOVA spectral test for falsification.
        
        Implements Section V equations:
            H₀: ΔF(ω) = constant ∀ ω (traditional biology)
            H₁: ΔF varies with frequency (QCAL)
            
            F_stat = [SS_between/df₁] / [SS_within/df₂]
        
        Args:
            frequencies: Frequency array
            responses: Response measurements (assumed multiple replicates)
            num_replicates: Number of replicate measurements per frequency
            
        Returns:
            ANOVA results including F-statistic and p-value
        """
        # Identify resonant vs non-resonant frequencies
        resonant_mask = np.zeros(len(frequencies), dtype=bool)
        for harmonic in self.qcal_harmonics:
            # Mark frequencies within 10 Hz of harmonics as resonant
            resonant_mask |= np.abs(frequencies - harmonic) < 10.0
        
        resonant_responses = responses[resonant_mask]
        non_resonant_responses = responses[~resonant_mask]
        
        if len(resonant_responses) < 2 or len(non_resonant_responses) < 2:
            warnings.warn("Insufficient data for ANOVA test")
            return {
                'F_statistic': 0.0,
                'p_value': 1.0,
                'alpha': 0.001,
                'reject_null': False,
                'interpretation': 'Insufficient data for ANOVA test'
            }
        
        # Perform one-way ANOVA
        F_stat, p_value = stats.f_oneway(resonant_responses, non_resonant_responses)
        
        # Critical threshold at α = 0.001 (Section V requirement)
        alpha = 0.001
        reject_null = p_value < alpha
        
        return {
            'F_statistic': F_stat,
            'p_value': p_value,
            'alpha': alpha,
            'reject_null': reject_null,
            'interpretation': (
                'QCAL supported: significant spectral structure detected' 
                if reject_null 
                else 'Traditional model not rejected'
            )
        }
    
    def calculate_qcal_signature_ratio(
        self,
        frequencies: np.ndarray,
        responses: np.ndarray
    ) -> Dict[str, float]:
        """
        Calculate QCAL signature ratio for decisive test.
        
        Implements Section VIII critical test:
            If ΔF(141.7 Hz) / ΔF(100 Hz) > 1.5 → QCAL supported
            If ΔF(ω) = constant ± error → QCAL falsified
        
        Args:
            frequencies: Frequency array
            responses: Response amplitudes
            
        Returns:
            Signature ratio and interpretation
        """
        # Find response at QCAL frequency (141.7 Hz)
        idx_qcal = np.argmin(np.abs(frequencies - QCAL_CARRIER_FREQUENCY))
        response_qcal = responses[idx_qcal]
        
        # Find response at control frequency (100 Hz)
        idx_control = np.argmin(np.abs(frequencies - 100.0))
        response_control = responses[idx_control]
        
        if response_control > 0:
            ratio = response_qcal / response_control
        else:
            ratio = 0.0
        
        qcal_supported = ratio > QCAL_SIGNATURE_RATIO
        
        return {
            'ratio': ratio,
            'threshold': QCAL_SIGNATURE_RATIO,
            'qcal_frequency_response': response_qcal,
            'control_frequency_response': response_control,
            'qcal_supported': qcal_supported,
            'interpretation': (
                f'QCAL SUPPORTED: Ratio {ratio:.2f} > {QCAL_SIGNATURE_RATIO}' 
                if qcal_supported 
                else f'QCAL NOT SUPPORTED: Ratio {ratio:.2f} ≤ {QCAL_SIGNATURE_RATIO}'
            )
        }


class SignalProcessor:
    """
    Signal processing tools for experimental data analysis.
    
    Implements Section VI signal processing methods.
    """
    
    @staticmethod
    def gaussian_filter(
        signal_array: np.ndarray,
        tau: float,
        dt: float
    ) -> np.ndarray:
        """
        Apply Gaussian temporal filter.
        
        Implements Section VI:
            F_limpieza(t) = F_raw(t) * exp(-t²/2τ²)
        
        Args:
            signal_array: Raw signal
            tau: Filter time constant
            dt: Time step
            
        Returns:
            Filtered signal
        """
        t = np.arange(len(signal_array)) * dt
        gaussian_window = np.exp(-t**2 / (2 * tau**2))
        
        # Convolve with Gaussian
        filtered = signal.fftconvolve(signal_array, gaussian_window, mode='same')
        
        # Normalize
        filtered = filtered / np.sum(gaussian_window)
        
        return filtered
    
    @staticmethod
    def spectral_analysis(
        signal_array: np.ndarray,
        sampling_rate: float
    ) -> Dict[str, np.ndarray]:
        """
        Perform FFT spectral analysis.
        
        Implements Section VI:
            F_espectral(ω) = FFT[F_limpieza(t)]
        
        Args:
            signal_array: Time-domain signal
            sampling_rate: Sampling rate (Hz)
            
        Returns:
            Dictionary with frequencies and spectrum
        """
        # Compute FFT
        spectrum = fft.fft(signal_array)
        frequencies = fft.fftfreq(len(signal_array), d=1/sampling_rate)
        
        # Take positive frequencies only
        positive_mask = frequencies >= 0
        frequencies = frequencies[positive_mask]
        spectrum = spectrum[positive_mask]
        
        return {
            'frequencies': frequencies,
            'spectrum': spectrum,
            'magnitude': np.abs(spectrum),
            'phase': np.angle(spectrum)
        }
    
    @staticmethod
    def calculate_snr(
        spectrum_magnitude: np.ndarray,
        signal_frequency: float,
        frequencies: np.ndarray,
        bandwidth: float = 1.0
    ) -> float:
        """
        Calculate Signal-to-Noise Ratio.
        
        Implements Section VI:
            SNR = |F_espectral(ωₚ)| / rms[F_espectral(ω≠ωₚ)]
        
        Args:
            spectrum_magnitude: Magnitude spectrum
            signal_frequency: Expected signal frequency
            frequencies: Frequency array
            bandwidth: Width around signal_frequency to exclude from noise
            
        Returns:
            SNR value
        """
        # Find signal peak
        idx_signal = np.argmin(np.abs(frequencies - signal_frequency))
        signal_magnitude = spectrum_magnitude[idx_signal]
        
        # Calculate noise (excluding signal region)
        noise_mask = np.abs(frequencies - signal_frequency) > bandwidth
        noise_spectrum = spectrum_magnitude[noise_mask]
        
        if len(noise_spectrum) > 0:
            noise_rms = np.sqrt(np.mean(noise_spectrum**2))
            if noise_rms > 0:
                snr = signal_magnitude / noise_rms
            else:
                snr = np.inf
        else:
            snr = np.inf
        
        return snr
    
    @staticmethod
    def calculate_coherence(
        signal1: np.ndarray,
        signal2: np.ndarray
    ) -> float:
        """
        Calculate coherence between two signals.
        
        Implements Section VI:
            coherence[F(t), Ψ(t)]
        
        Args:
            signal1: First signal (e.g., fluorescence)
            signal2: Second signal (e.g., stimulus)
            
        Returns:
            Coherence value (0 to 1)
        """
        # Normalize signals
        s1 = (signal1 - np.mean(signal1)) / (np.std(signal1) + 1e-10)
        s2 = (signal2 - np.mean(signal2)) / (np.std(signal2) + 1e-10)
        
        # Calculate cross-correlation at zero lag
        coherence = np.abs(np.correlate(s1, s2, mode='valid')[0]) / len(s1)
        
        return min(coherence, 1.0)
    
    @staticmethod
    def detection_criterion(
        snr: float,
        coherence: float,
        snr_threshold: float = 3.0,
        coherence_threshold: float = 0.7
    ) -> bool:
        """
        Apply detection criterion.
        
        Implements Section VI:
            SNR > 3 AND coherence[F(t), Ψ(t)] > 0.7
        
        Args:
            snr: Calculated SNR
            coherence: Calculated coherence
            snr_threshold: Minimum SNR
            coherence_threshold: Minimum coherence
            
        Returns:
            True if detection criteria are met
        """
        return snr > snr_threshold and coherence > coherence_threshold


# Convenience function for running a complete QCAL experiment simulation
def run_qcal_experiment(
    exp_params: Optional[ExperimentalParameters] = None,
    protein_params: Optional[ProteinDynamicsParameters] = None,
    verbose: bool = True
) -> Dict[str, any]:
    """
    Run a complete QCAL vibro-fluorescent experiment simulation.
    
    This function simulates the entire experimental protocol:
    1. Generate modulated QCAL signals at various frequencies
    2. Calculate protein domain responses
    3. Compute fluorescence responses
    4. Perform spectral analysis
    5. Validate QCAL predictions
    
    Args:
        exp_params: Experimental parameters (uses defaults if None)
        protein_params: Protein dynamics parameters (uses defaults if None)
        verbose: Print progress messages
        
    Returns:
        Dictionary containing all experimental results and validation metrics
    """
    # Use default parameters if not provided
    if exp_params is None:
        exp_params = ExperimentalParameters()
    if protein_params is None:
        protein_params = ProteinDynamicsParameters()
    
    if verbose:
        print("=" * 60)
        print("QCAL Vibro-Fluorescent Experiment Simulation")
        print("=" * 60)
        print(f"Carrier frequency: {exp_params.carrier_frequency} Hz")
        print(f"Modulation range: {exp_params.modulation_frequencies[0]:.1f} - "
              f"{exp_params.modulation_frequencies[-1]:.1f} Hz")
        print(f"Number of frequencies: {len(exp_params.modulation_frequencies)}")
        print()
    
    # Initialize models
    signal_gen = QCALSignalGenerator(exp_params)
    protein_model = ProteinOscillatorModel(protein_params)
    fluorescence_model = FluorescenceResponseModel(protein_model)
    validator = QCALPredictionValidator()
    
    # Storage for results
    frequencies = exp_params.modulation_frequencies
    responses = np.zeros(len(frequencies))
    efficiencies = np.zeros(len(frequencies))
    
    # Frequency sweep
    if verbose:
        print("Running frequency sweep...")
    
    for i, freq in enumerate(frequencies):
        # Generate signal
        _, signal = signal_gen.generate_signal(freq, normalize_energy=True)
        
        # Calculate fluorescence response
        response_data = fluorescence_model.calculate_fluorescence_response(freq)
        
        responses[i] = response_data['delta_F']
        efficiencies[i] = response_data['eta']
    
    if verbose:
        print(f"✓ Frequency sweep complete ({len(frequencies)} points)")
        print()
    
    # QCAL validation tests
    if verbose:
        print("Performing QCAL validation tests...")
    
    # 1. Peak detection
    peak_data = validator.predict_resonance_peaks(frequencies, responses)
    
    # 2. Lorentzian fit
    lorentzian_fit = validator.fit_lorentzian_structure(frequencies, responses)
    
    # 3. Coherence threshold test
    max_amplitude = exp_params.amplitude
    threshold_test = validator.test_coherence_threshold(max_amplitude)
    
    # 4. ANOVA spectral test
    anova_results = validator.anova_spectral_test(frequencies, responses)
    
    # 5. QCAL signature ratio
    signature_ratio = validator.calculate_qcal_signature_ratio(frequencies, responses)
    
    if verbose:
        print(f"✓ Peak detection: {len(peak_data['peak_frequencies'])} peaks found")
        print(f"✓ Lorentzian fit: R² = {lorentzian_fit.get('r_squared', 0):.4f}")
        print(f"✓ Coherence threshold: {threshold_test['interpretation']}")
        print(f"✓ ANOVA test: {anova_results['interpretation']}")
        print(f"✓ Signature ratio: {signature_ratio['interpretation']}")
        print()
    
    # Compile results
    results = {
        'frequencies': frequencies,
        'responses': responses,
        'efficiencies': efficiencies,
        'peak_detection': peak_data,
        'lorentzian_fit': lorentzian_fit,
        'coherence_threshold': threshold_test,
        'anova_test': anova_results,
        'signature_ratio': signature_ratio,
        'experimental_parameters': exp_params,
        'protein_parameters': protein_params
    }
    
    if verbose:
        print("=" * 60)
        print("Experiment simulation complete!")
        print("=" * 60)
    
    return results


if __name__ == "__main__":
    """
    Demonstration of QCAL vibro-fluorescent experimental framework.
    """
    print(__doc__)
    
    # Run example experiment
    results = run_qcal_experiment(verbose=True)
    
    # Print key results
    print("\nKey Results:")
    print("-" * 60)
    print(f"QCAL Signature Ratio: {results['signature_ratio']['ratio']:.3f}")
    print(f"QCAL Supported: {results['signature_ratio']['qcal_supported']}")
    print(f"ANOVA p-value: {results['anova_test']['p_value']:.2e}")
    print(f"Number of resonance peaks: {len(results['peak_detection']['peak_frequencies'])}")
    print(f"Lorentzian fit R²: {results['lorentzian_fit'].get('r_squared', 0):.4f}")
    print("-" * 60)
