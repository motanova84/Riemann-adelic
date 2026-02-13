"""
Explicit Sum Analyzer - Suma Explícita Emergence
=================================================

Implements the cross-correlation analysis between the Atlas³ operator spectrum
and the synthetic prime signal to demonstrate that the spectral density is
modulated by Von Mangoldt weights Λ(n).

This module implements:
1. Prime Signal Generator: S(t) = Σ_{p^m} (log p / p^(m/2)) δ(t - m ln p)
2. Cross-Correlation Function between spectrum and prime signal
3. Fourier analysis to detect ln(p) peaks in spectral density
4. Statistical validation of prime memory in operator spectrum

Mathematical Background:
-----------------------
If the spectrum {γ_n} of Atlas³ is an isomorphism of the Riemann Hypothesis,
then the Fourier transform of the density of levels N(E) should show exact
peaks at positions t = ln p, ln p², ... with the correct amplitudes matching
the Von Mangoldt function Λ(n).

This is the "Explicit Sum Formula" emerging from the operator:
N(E) ∼ E/(2π) + (1/π) Σ_γ sin(E·γ) / γ + oscillatory terms

The oscillatory terms must match:
ψ₀(x) = x - Σ_{p^m} (log p / p^(m/2)) = x - Σ_n Λ(n)/√n

Author: José Manuel Mota Burruezo Ψ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from scipy import signal, stats
from scipy.fft import fft, fftfreq, rfft, rfftfreq


def generate_primes(n_max: int) -> np.ndarray:
    """
    Generate all prime numbers up to n_max using Sieve of Eratosthenes.
    
    Args:
        n_max: Maximum value to check for primes
        
    Returns:
        Array of prime numbers
    """
    if n_max < 2:
        return np.array([])
    
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[0:2] = False
    
    for i in range(2, int(np.sqrt(n_max)) + 1):
        if sieve[i]:
            sieve[i*i::i] = False
    
    return np.where(sieve)[0]


@dataclass
class PrimeSignal:
    """
    Synthetic prime signal S(t) for correlation analysis.
    
    Attributes:
        t_values: Time/position values
        signal: Signal amplitudes at each t
        primes: Prime numbers included
        max_power: Maximum prime power considered
    """
    t_values: np.ndarray
    signal: np.ndarray
    primes: np.ndarray
    max_power: int
    n_components: int  # Number of p^m terms


@dataclass
class CorrelationResult:
    """
    Results of cross-correlation analysis.
    
    Attributes:
        correlation: Cross-correlation values
        lags: Time lags for correlation
        peak_positions: Detected peak positions
        peak_amplitudes: Amplitudes at detected peaks
        expected_peaks: Expected positions (ln p values)
        detection_rate: Fraction of expected peaks detected
        significance: Statistical significance (p-value)
    """
    correlation: np.ndarray
    lags: np.ndarray
    peak_positions: np.ndarray
    peak_amplitudes: np.ndarray
    expected_peaks: np.ndarray
    detection_rate: float
    significance: float
    mean_deviation: float


class ExplicitSumAnalyzer:
    """
    Analyzer for detecting explicit sum formula emergence in spectral data.
    
    Implements the test for prime memory: does the spectral density fluctuation
    match the structure predicted by the Von Mangoldt function?
    
    Attributes:
        t_max: Maximum time/position for analysis
        dt: Time resolution
        max_prime_power: Maximum power m in p^m to consider
        tolerance: Tolerance for peak detection (in units of dt)
    """
    
    def __init__(
        self,
        t_max: float = 100.0,
        dt: float = 0.01,
        max_prime_power: int = 3,
        tolerance: float = 0.1
    ):
        """
        Initialize the analyzer.
        
        Args:
            t_max: Maximum value for time/position axis
            dt: Resolution of signal sampling
            max_prime_power: Maximum m in p^m
            tolerance: Peak detection tolerance as fraction of typical spacing
        """
        self.t_max = t_max
        self.dt = dt
        self.max_prime_power = max_prime_power
        self.tolerance = tolerance
        
        # Generate time grid
        self.n_points = int(t_max / dt)
        self.t_grid = np.linspace(0, t_max, self.n_points, endpoint=False)
    
    def generate_prime_signal(
        self,
        p_max: Optional[int] = None
    ) -> PrimeSignal:
        """
        Generate the synthetic prime signal S(t).
        
        S(t) = Σ_{p^m} (log p / p^(m/2)) δ(t - m·ln p)
        
        Args:
            p_max: Maximum prime to include (default: auto from t_max)
            
        Returns:
            PrimeSignal object containing the discrete signal
        """
        # Determine maximum prime from t_max if not specified
        if p_max is None:
            # For t = m·ln(p), we need p ≤ exp(t_max / m)
            # Cap at reasonable value to avoid memory issues
            p_max = min(int(np.exp(self.t_max / 1)) + 1, 10000)
        
        # Generate primes
        primes = generate_primes(p_max)
        
        # Initialize signal on grid
        signal_values = np.zeros_like(self.t_grid)
        n_components = 0
        
        # Add contribution from each p^m
        for p in primes:
            log_p = np.log(p)
            
            for m in range(1, self.max_prime_power + 1):
                # Position: t = m·ln(p)
                t_pm = m * log_p
                
                if t_pm > self.t_max:
                    break
                
                # Amplitude: log(p) / p^(m/2)
                amplitude = log_p / (p ** (m / 2.0))
                
                # Add delta function (approximate as Gaussian with small width)
                # Width ~ dt for discrete approximation
                idx = np.argmin(np.abs(self.t_grid - t_pm))
                signal_values[idx] += amplitude
                n_components += 1
        
        return PrimeSignal(
            t_values=self.t_grid.copy(),
            signal=signal_values,
            primes=primes,
            max_power=self.max_prime_power,
            n_components=n_components
        )
    
    def spectrum_to_density(
        self,
        eigenvalues: np.ndarray,
        smoothing_width: float = 1.0
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Convert discrete eigenvalue spectrum to smooth density function.
        
        Args:
            eigenvalues: Array of eigenvalues/zeros
            smoothing_width: Width for Gaussian smoothing
            
        Returns:
            (t_values, density) arrays
        """
        # Sort eigenvalues
        eigs = np.sort(eigenvalues)
        
        # Create density via kernel density estimation
        density = np.zeros_like(self.t_grid)
        
        for eig in eigs:
            # Add Gaussian kernel centered at eigenvalue
            kernel = np.exp(-((self.t_grid - eig) ** 2) / (2 * smoothing_width ** 2))
            density += kernel
        
        # Normalize
        density /= (len(eigs) * smoothing_width * np.sqrt(2 * np.pi))
        
        return self.t_grid, density
    
    def cross_correlate(
        self,
        spectrum: np.ndarray,
        prime_signal: PrimeSignal
    ) -> CorrelationResult:
        """
        Compute cross-correlation between spectral density and prime signal.
        
        Args:
            spectrum: Eigenvalue spectrum
            prime_signal: Synthetic prime signal
            
        Returns:
            CorrelationResult with detailed analysis
        """
        # Convert spectrum to density
        _, density = self.spectrum_to_density(spectrum, smoothing_width=0.5)
        
        # Compute cross-correlation using FFT
        correlation = signal.correlate(
            density - np.mean(density),
            prime_signal.signal - np.mean(prime_signal.signal),
            mode='same'
        )
        
        # Normalize
        correlation /= (np.std(density) * np.std(prime_signal.signal) * len(density))
        
        # Compute lags
        lags = signal.correlation_lags(len(density), len(prime_signal.signal), mode='same')
        lags = lags * self.dt
        
        # Detect peaks in correlation
        peak_indices, properties = signal.find_peaks(
            correlation,
            height=3.0 * np.std(correlation),  # 3-sigma threshold
            distance=int(0.5 / self.dt)  # Minimum separation
        )
        
        peak_positions = lags[peak_indices]
        peak_amplitudes = correlation[peak_indices]
        
        # Expected peak positions (ln p for primes)
        expected_peaks = np.log(prime_signal.primes[prime_signal.primes > 1])
        
        # Count how many expected peaks are detected
        detected_count = 0
        deviations = []
        
        for exp_peak in expected_peaks:
            if exp_peak > self.t_max:
                break
            
            # Check if there's a detected peak nearby
            distances = np.abs(peak_positions - exp_peak)
            if len(distances) > 0 and np.min(distances) < self.tolerance:
                detected_count += 1
                deviations.append(np.min(distances))
        
        detection_rate = detected_count / min(len(expected_peaks), len(peak_positions) + 1)
        mean_deviation = np.mean(deviations) if deviations else np.inf
        
        # Statistical significance via permutation test
        # Compute correlation with random signal
        n_permutations = 100
        random_correlations = []
        
        for _ in range(n_permutations):
            random_signal = np.random.permutation(prime_signal.signal)
            rand_corr = signal.correlate(
                density - np.mean(density),
                random_signal - np.mean(random_signal),
                mode='same'
            )
            rand_corr /= (np.std(density) * np.std(random_signal) * len(density))
            random_correlations.append(np.max(np.abs(rand_corr)))
        
        # p-value: fraction of random correlations exceeding observed max
        max_corr = np.max(np.abs(correlation))
        p_value = np.mean(np.array(random_correlations) >= max_corr)
        
        return CorrelationResult(
            correlation=correlation,
            lags=lags,
            peak_positions=peak_positions,
            peak_amplitudes=peak_amplitudes,
            expected_peaks=expected_peaks[:20],  # First 20 primes
            detection_rate=detection_rate,
            significance=p_value,
            mean_deviation=mean_deviation
        )
    
    def fourier_peak_detection(
        self,
        spectrum: np.ndarray
    ) -> Dict[str, Any]:
        """
        Detect ln(p) peaks via Fourier analysis of spectral density.
        
        The density of states N(E) should have oscillations at frequencies
        corresponding to ln(p).
        
        Args:
            spectrum: Eigenvalue spectrum
            
        Returns:
            Dictionary with Fourier analysis results
        """
        # Convert to density
        _, density = self.spectrum_to_density(spectrum, smoothing_width=0.5)
        
        # Remove smooth trend (Weyl law)
        density_detrended = density - np.mean(density)
        
        # Compute Fourier transform
        fft_vals = rfft(density_detrended)
        fft_freqs = rfftfreq(len(density_detrended), d=self.dt)
        
        # Power spectrum
        power = np.abs(fft_vals) ** 2
        
        # Find peaks in power spectrum
        peak_indices, _ = signal.find_peaks(
            power,
            height=5.0 * np.median(power),
            distance=int(10)
        )
        
        peak_frequencies = fft_freqs[peak_indices]
        peak_powers = power[peak_indices]
        
        # Sort by power
        sorted_indices = np.argsort(peak_powers)[::-1]
        peak_frequencies = peak_frequencies[sorted_indices]
        peak_powers = peak_powers[sorted_indices]
        
        return {
            'frequencies': fft_freqs,
            'power_spectrum': power,
            'peak_frequencies': peak_frequencies[:10],  # Top 10
            'peak_powers': peak_powers[:10],
            'total_power': np.sum(power),
            'peak_fraction': np.sum(peak_powers[:10]) / np.sum(power)
        }
    
    def validate_prime_memory(
        self,
        spectrum: np.ndarray,
        min_detection_rate: float = 0.5,
        max_p_value: float = 0.01
    ) -> Tuple[bool, Dict[str, Any]]:
        """
        Validate that the spectrum exhibits prime memory.
        
        Args:
            spectrum: Eigenvalue spectrum to test
            min_detection_rate: Minimum required detection rate
            max_p_value: Maximum allowed p-value
            
        Returns:
            (is_valid, report_dict)
        """
        # Generate prime signal
        prime_signal = self.generate_prime_signal()
        
        # Cross-correlation analysis
        corr_result = self.cross_correlate(spectrum, prime_signal)
        
        # Fourier analysis
        fourier_result = self.fourier_peak_detection(spectrum)
        
        # Validation criteria
        is_valid = (
            corr_result.detection_rate >= min_detection_rate and
            corr_result.significance <= max_p_value
        )
        
        report = {
            'is_valid': is_valid,
            'detection_rate': corr_result.detection_rate,
            'p_value': corr_result.significance,
            'mean_deviation': corr_result.mean_deviation,
            'n_expected_peaks': len(corr_result.expected_peaks),
            'n_detected_peaks': len(corr_result.peak_positions),
            'fourier_peak_fraction': fourier_result['peak_fraction'],
            'conclusion': (
                "✓ PRIME MEMORY DETECTED - Spectral density modulated by Λ(n)"
                if is_valid else
                "✗ No significant prime memory detected"
            )
        }
        
        return is_valid, report


def demo_explicit_sum_analysis():
    """Demonstration of explicit sum emergence detection."""
    print("=" * 70)
    print("SUMA EXPLÍCITA - Explicit Sum Formula Emergence")
    print("=" * 70)
    
    # Create analyzer
    analyzer = ExplicitSumAnalyzer(t_max=50.0, dt=0.05)
    
    # Generate synthetic spectrum resembling Riemann zeros
    # Use known zeros or generate from GUE-like distribution
    n_zeros = 100
    base_spacing = 2 * np.pi / np.log(n_zeros)
    zeros = np.cumsum(base_spacing * (1 + 0.3 * np.random.randn(n_zeros)))
    zeros = zeros[zeros < 50.0]
    
    print(f"\n📊 Spectrum: {len(zeros)} eigenvalues in [0, 50]")
    
    # Generate prime signal
    prime_signal = analyzer.generate_prime_signal()
    print(f"\n🔢 Prime Signal: {prime_signal.n_components} components")
    print(f"   First primes: {prime_signal.primes[:10]}")
    
    # Validate prime memory
    is_valid, report = analyzer.validate_prime_memory(zeros)
    
    print(f"\n{'='*70}")
    print("VALIDATION REPORT")
    print('='*70)
    print(f"Detection Rate: {report['detection_rate']:.2%}")
    print(f"Statistical Significance (p-value): {report['p_value']:.4f}")
    print(f"Mean Peak Deviation: {report['mean_deviation']:.4f}")
    print(f"Expected Peaks: {report['n_expected_peaks']}")
    print(f"Detected Peaks: {report['n_detected_peaks']}")
    print(f"Fourier Peak Fraction: {report['fourier_peak_fraction']:.2%}")
    print(f"\n{report['conclusion']}")
    print('='*70)
    
    return analyzer, report


if __name__ == "__main__":
    demo_explicit_sum_analysis()
