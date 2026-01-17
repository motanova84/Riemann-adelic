#!/usr/bin/env python3
"""
Riemann-PNP Superfluid Verification Bridge
===========================================

PUENTE DE VERIFICACIÓN DE SUPERFLUIDEZ RIEMANN–P≠NP ∞³

This module implements the 3-step verification procedure to detect spectral 
coherence leaks in the expansion to 1,000 primes, establishing the vibrational 
superfluid bridge between:
  - ζ(s) spectrum (Riemann zeta, adelic dimension)
  - κ_Π structure (Tseitin spectral constant, in P≠NP)
  - Ψ = 1.000 (maximum coherence manifested)

Mathematical Foundation:
    The verification checks if any zeros of ζ(s) in the expanded network of 
    1,000 primes deviate minimally from the frequency pattern:
        √p → log(f) → spectrum ℋ_Ψ

Three Verification Steps:
    1. Inverse Interpolation: Zeros → Primes
       p_k = (log(f_k)/a)² where f_k is frequency of k-th zero
    
    2. Tensorial Comparison with 𝒯ₚ(Ψ)
       T⃗_p = (H(p), R(p), C(p))
       δ(p) = |f(p) - f_ζ(p)| / f(p)
    
    3. Vibrational Anomaly Identification
       Detect: C(p) < 0.01, H(p) ≪ mean, R(p) → 0, δ(p) ≫ 0.01

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Optional, List, Dict, NamedTuple
from dataclasses import dataclass
import warnings

try:
    import mpmath
    MPMATH_AVAILABLE = True
except ImportError:
    MPMATH_AVAILABLE = False
    warnings.warn("mpmath not available, using approximate values")


class PrimeSpectralData(NamedTuple):
    """Spectral data for a prime number."""
    prime: int
    frequency: float
    harmonic_index: float  # H(p)
    resonance_strength: float  # R(p)
    coherence_factor: float  # C(p)


class ZeroToPremeInterpolation(NamedTuple):
    """Result of inverse interpolation from zeros to primes."""
    zero_index: int
    zero_imaginary: float
    estimated_frequency: float
    estimated_prime: float
    alignment_factor: float


@dataclass
class TensorialDeviation:
    """Tensorial deviation measurement for a prime."""
    prime: int
    frequency_prime: float  # f(p) from spectral model
    frequency_zeta: float  # f_ζ(p) from zero mapping
    delta: float  # δ(p) = |f(p) - f_ζ(p)| / f(p)
    harmonic_index: float  # H(p)
    resonance_strength: float  # R(p)
    coherence_factor: float  # C(p)
    is_leak: bool  # True if δ(p) > 0.01


@dataclass
class VibrationalAnomaly:
    """Detected vibrational anomaly in spectral structure."""
    prime: int
    anomaly_type: str  # 'coherence', 'harmonic', 'resonance', 'deviation'
    severity: float  # 0.0 (normal) to 1.0 (critical)
    delta: float
    coherence_factor: float
    harmonic_index: float
    resonance_strength: float
    description: str
    is_spectral_leak: bool  # vs coding error


class RiemannPNPVerificationBridge:
    """
    Verification bridge for Riemann-PNP superfluid coherence.
    
    Implements the 3-step verification procedure to detect spectral leaks
    in the expansion to 1,000 primes, connecting ζ(s) spectrum to P≠NP 
    complexity structure.
    """
    
    # Constants from .qcal_beacon
    F0 = 141.7001  # Hz - fundamental frequency
    C_COHERENCE = 244.36  # Coherence constant
    ZETA_DERIV_HALF = -3.92264773  # ζ'(1/2)
    CRITICAL_RE = 0.5  # Re(s) = 1/2
    
    # Physical constants
    C_LIGHT = 299792458  # m/s
    PLANCK_LENGTH = 1.616255e-35  # m
    
    # Thresholds for anomaly detection
    COHERENCE_MIN = 0.01  # C(p) < 0.01 indicates leak
    DELTA_MAX = 0.01  # δ(p) > 0.01 indicates deviation
    HARMONIC_MEAN_FACTOR = 0.5  # H(p) < 0.5*mean indicates anomaly
    RESONANCE_MIN = 0.05  # R(p) < 0.05 indicates weak resonance
    
    # Known non-trivial zeros (first 10 imaginary parts, high precision)
    ZEROS_IM = np.array([
        14.134725141734693790,  # t₁
        21.022039638771554993,  # t₂
        25.010857580145688763,  # t₃
        30.424876125859513210,  # t₄
        32.935061587739189691,  # t₅
        37.586178158825671257,  # t₆
        40.918719012147495187,  # t₇
        43.327073280914999519,  # t₈
        48.005150881167159727,  # t₉
        49.773832477672302659,  # t₁₀
    ])
    
    def __init__(self, precision: int = 50, n_primes: int = 1000):
        """
        Initialize verification bridge.
        
        Args:
            precision: Decimal precision for computations
            n_primes: Number of primes to analyze (default: 1000)
        """
        self.precision = precision
        self.n_primes = n_primes
        
        if MPMATH_AVAILABLE:
            mpmath.mp.dps = precision
        
        # Generate prime numbers
        self.primes = self._generate_primes(n_primes)
        
    def _generate_primes(self, n: int) -> np.ndarray:
        """
        Generate first n prime numbers using Sieve of Eratosthenes.
        
        Args:
            n: Number of primes to generate
            
        Returns:
            Array of first n primes
        """
        if n <= 0:
            return np.array([])
        
        # Estimate upper limit
        if n < 6:
            limit = 15
        else:
            limit = int(n * (np.log(n) + np.log(np.log(n)) + 2))
        
        sieve = np.ones(limit, dtype=bool)
        sieve[0] = sieve[1] = False
        
        for i in range(2, int(np.sqrt(limit)) + 1):
            if sieve[i]:
                sieve[i*i::i] = False
        
        primes = np.where(sieve)[0]
        return primes[:n]
    
    def spectral_frequency(self, p: int) -> float:
        """
        Calculate spectral frequency for a prime.
        
        Uses the spectral model based on equilibrium radius:
            R_Ψ(p) = scale_factor / equilibrium(p)
            f(p) = c / (2π R_Ψ(p) ℓ_P)
        
        This ensures proper increasing behavior with prime.
        
        Args:
            p: Prime number
            
        Returns:
            Spectral frequency f(p) in Hz
        """
        # Use equilibrium radius model
        R_psi = self.equilibrium_radius(p)
        return self.frequency_from_radius(R_psi)
    
    def equilibrium_radius(self, p: int) -> float:
        """
        Calculate equilibrium radius for prime.
        
        equilibrium(p) = exp(π√p/2) / p^(3/2)
        R_Ψ(p) = scale_factor / equilibrium(p)
        
        Args:
            p: Prime number
            
        Returns:
            Equilibrium radius R_Ψ(p)
        """
        if MPMATH_AVAILABLE:
            eq = mpmath.exp(mpmath.pi * mpmath.sqrt(p) / 2) / mpmath.power(p, 1.5)
            scale_factor = mpmath.mpf('1.931174e41')
            return float(scale_factor / eq)
        else:
            eq = np.exp(np.pi * np.sqrt(p) / 2) / np.power(p, 1.5)
            scale_factor = 1.931174e41
            return scale_factor / eq
    
    def frequency_from_radius(self, R_psi: float) -> float:
        """
        Calculate frequency from equilibrium radius.
        
        f₀(p) = c / (2π R_Ψ(p) ℓ_P)
        
        Args:
            R_psi: Equilibrium radius
            
        Returns:
            Frequency in Hz
        """
        return self.C_LIGHT / (2 * np.pi * R_psi * self.PLANCK_LENGTH)
    
    # ========================================================================
    # STEP 1: INVERSE INTERPOLATION - ZEROS → PRIMES
    # ========================================================================
    
    def zero_to_frequency(self, zero_im: float, alignment_factor: float = 1.0) -> float:
        """
        Estimate frequency from a zero's imaginary part.
        
        The k-th zero at height t_k corresponds to a frequency:
            f_k ≈ t_k / (2π) · f₀
        
        Args:
            zero_im: Imaginary part of zero
            alignment_factor: Calibration factor (default: 1.0)
            
        Returns:
            Estimated frequency in Hz
        """
        # Direct proportionality to zero height
        return (zero_im / (2 * np.pi)) * self.F0 * alignment_factor
    
    def frequency_to_prime(self, freq: float, alignment_factor: float = 1.0) -> float:
        """
        Estimate prime number from frequency using inverse mapping.
        
        Uses binary search over the equilibrium model to find the prime
        that best matches the given frequency.
        
        Args:
            freq: Frequency in Hz
            alignment_factor: Calibration factor
            
        Returns:
            Estimated prime (may be non-integer)
        """
        if freq <= 0:
            return 0.0
        
        # Binary search over plausible range
        p_min, p_max = 2, 10000
        tolerance = 0.1
        
        # First check if frequency is in reasonable range
        f_min = self.spectral_frequency(p_min)
        f_max = self.spectral_frequency(p_max)
        
        if freq < f_min:
            return p_min
        if freq > f_max:
            return p_max
        
        # Binary search
        while p_max - p_min > tolerance:
            p_mid = (p_min + p_max) / 2
            f_mid = self.spectral_frequency(int(p_mid))
            
            if f_mid < freq:
                p_min = p_mid
            else:
                p_max = p_mid
        
        return (p_min + p_max) / 2
    
    def inverse_interpolation(
        self, 
        zeros: Optional[np.ndarray] = None,
        alignment_factor: float = 1.0
    ) -> List[ZeroToPremeInterpolation]:
        """
        STEP 1: Inverse interpolation from zeros to primes.
        
        Maps non-trivial zeros of ζ(s) to estimated prime numbers via
        frequency mapping:
            t_k → f_k → p_k
        
        Args:
            zeros: Array of zero imaginary parts (default: use known zeros)
            alignment_factor: Spectral alignment factor
            
        Returns:
            List of interpolation results
        """
        if zeros is None:
            zeros = self.ZEROS_IM
        
        results = []
        
        for idx, zero_im in enumerate(zeros):
            # Zero → Frequency
            freq = self.zero_to_frequency(zero_im, alignment_factor)
            
            # Frequency → Prime
            prime_est = self.frequency_to_prime(freq, alignment_factor)
            
            results.append(ZeroToPremeInterpolation(
                zero_index=idx,
                zero_imaginary=zero_im,
                estimated_frequency=freq,
                estimated_prime=prime_est,
                alignment_factor=alignment_factor
            ))
        
        return results
    
    # ========================================================================
    # STEP 2: TENSORIAL COMPARISON WITH 𝒯ₚ(Ψ)
    # ========================================================================
    
    def compute_harmonic_index(self, p: int) -> float:
        """
        Calculate harmonic index H(p) for a prime.
        
        H(p) measures the local harmonic structure around prime p
        in the spectral space.
        
        Args:
            p: Prime number
            
        Returns:
            Harmonic index H(p) in [0, 1]
        """
        # Harmonic index based on √p periodicity
        # H(p) = sin²(π√p/17) reflects p=17 resonance
        return np.sin(np.pi * np.sqrt(p) / np.sqrt(17)) ** 2
    
    def compute_resonance_strength(self, p: int) -> float:
        """
        Calculate resonance strength R(p) for a prime.
        
        R(p) measures global vibrational coupling to the fundamental
        frequency f₀ = 141.7001 Hz.
        
        Args:
            p: Prime number
            
        Returns:
            Resonance strength R(p) in [0, 1]
        """
        # Resonance based on frequency alignment
        freq = self.spectral_frequency(p)
        # Normalize by fundamental frequency scale
        resonance = np.exp(-abs(np.log(freq / self.F0) - np.sqrt(p)) / 10)
        return min(resonance, 1.0)
    
    def compute_coherence_factor(self, p: int, reference_prime: int = 17) -> float:
        """
        Calculate coherence factor C(p) relative to reference prime.
        
        C(p) measures alignment with p=17 (fundamental resonance).
        
        Args:
            p: Prime number
            reference_prime: Reference prime (default: 17)
            
        Returns:
            Coherence factor C(p) in [0, 1]
        """
        # Coherence based on √p ratio to reference
        ratio = np.sqrt(p) / np.sqrt(reference_prime)
        # Gaussian coherence around reference
        coherence = np.exp(-((ratio - 1.0) ** 2) / 2)
        return coherence
    
    def compute_spectral_tensor(self, p: int) -> Tuple[float, float, float]:
        """
        Compute complete spectral tensor T⃗_p = (H(p), R(p), C(p)).
        
        Args:
            p: Prime number
            
        Returns:
            Tuple (harmonic_index, resonance_strength, coherence_factor)
        """
        H = self.compute_harmonic_index(p)
        R = self.compute_resonance_strength(p)
        C = self.compute_coherence_factor(p)
        
        return (H, R, C)
    
    def spectral_deviation(
        self,
        p: int,
        zero_frequency: Optional[float] = None
    ) -> float:
        """
        Calculate spectral deviation δ(p).
        
        δ(p) = |f(p) - f_ζ(p)| / f(p)
        
        where:
            f(p) = spectral frequency from model
            f_ζ(p) = frequency from zero mapping
        
        Args:
            p: Prime number
            zero_frequency: Frequency derived from zero (optional)
            
        Returns:
            Spectral deviation δ(p)
        """
        f_p = self.spectral_frequency(p)
        
        if zero_frequency is None:
            # Estimate from nearest zero
            zero_frequency = f_p  # No deviation if no zero given
        
        delta = abs(f_p - zero_frequency) / f_p if f_p > 0 else 0.0
        
        return delta
    
    def tensorial_comparison(
        self,
        primes: Optional[np.ndarray] = None,
        zero_frequencies: Optional[Dict[int, float]] = None
    ) -> List[TensorialDeviation]:
        """
        STEP 2: Tensorial comparison with 𝒯ₚ(Ψ).
        
        For each prime p, computes:
            - Spectral tensor T⃗_p = (H(p), R(p), C(p))
            - Spectral deviation δ(p) = |f(p) - f_ζ(p)| / f(p)
            - Identifies coherence leaks where δ(p) > 0.01
        
        Args:
            primes: Array of primes to analyze (default: all generated)
            zero_frequencies: Dictionary mapping primes to zero frequencies
            
        Returns:
            List of tensorial deviation measurements
        """
        if primes is None:
            primes = self.primes
        
        if zero_frequencies is None:
            zero_frequencies = {}
        
        results = []
        
        for p in primes:
            # Compute spectral tensor
            H, R, C = self.compute_spectral_tensor(p)
            
            # Spectral frequencies
            f_p = self.spectral_frequency(p)
            f_zeta = zero_frequencies.get(p, f_p)  # Use model if no zero
            
            # Deviation
            delta = self.spectral_deviation(p, f_zeta)
            
            # Check for leak
            is_leak = delta > self.DELTA_MAX
            
            results.append(TensorialDeviation(
                prime=p,
                frequency_prime=f_p,
                frequency_zeta=f_zeta,
                delta=delta,
                harmonic_index=H,
                resonance_strength=R,
                coherence_factor=C,
                is_leak=is_leak
            ))
        
        return results
    
    # ========================================================================
    # STEP 3: VIBRATIONAL ANOMALY IDENTIFICATION
    # ========================================================================
    
    def classify_anomaly_type(
        self,
        C: float,
        H: float,
        R: float,
        delta: float,
        H_mean: float
    ) -> Tuple[str, float, bool]:
        """
        Classify type and severity of vibrational anomaly.
        
        Returns anomaly type, severity (0-1), and whether it's a spectral leak
        (vs coding error).
        
        Args:
            C: Coherence factor
            H: Harmonic index
            R: Resonance strength
            delta: Spectral deviation
            H_mean: Mean harmonic index
            
        Returns:
            Tuple (anomaly_type, severity, is_spectral_leak)
        """
        anomalies = []
        severities = []
        
        # Check coherence
        if C < self.COHERENCE_MIN:
            anomalies.append('coherence')
            severities.append((self.COHERENCE_MIN - C) / self.COHERENCE_MIN)
        
        # Check harmonic index
        if H < self.HARMONIC_MEAN_FACTOR * H_mean:
            anomalies.append('harmonic')
            severity = 1.0 - (H / (self.HARMONIC_MEAN_FACTOR * H_mean))
            severities.append(severity)
        
        # Check resonance
        if R < self.RESONANCE_MIN:
            anomalies.append('resonance')
            severities.append((self.RESONANCE_MIN - R) / self.RESONANCE_MIN)
        
        # Check deviation
        if delta > self.DELTA_MAX:
            anomalies.append('deviation')
            severities.append(min(delta / self.DELTA_MAX - 1.0, 1.0))
        
        if not anomalies:
            return ('none', 0.0, False)
        
        # Primary anomaly is highest severity
        max_idx = np.argmax(severities)
        anomaly_type = anomalies[max_idx]
        severity = severities[max_idx]
        
        # Spectral leak vs coding error:
        # If multiple indicators fail, likely spectral leak
        # If only one fails, likely coding/numerical error
        is_spectral_leak = len(anomalies) >= 2
        
        return (anomaly_type, severity, is_spectral_leak)
    
    def identify_vibrational_anomalies(
        self,
        deviations: List[TensorialDeviation]
    ) -> List[VibrationalAnomaly]:
        """
        STEP 3: Identify vibrational anomalies.
        
        Detects primes where:
            - C(p) < 0.01 (low coherence)
            - H(p) ≪ mean (anomalous harmonic)
            - R(p) → 0 (weak resonance)
            - δ(p) ≫ 0.01 (large deviation)
        
        Classifies anomalies as spectral leaks vs coding errors.
        
        Args:
            deviations: List of tensorial deviations from step 2
            
        Returns:
            List of detected vibrational anomalies
        """
        anomalies = []
        
        # Calculate mean harmonic index
        H_values = [d.harmonic_index for d in deviations]
        H_mean = np.mean(H_values)
        
        for dev in deviations:
            # Check for any anomaly condition
            has_anomaly = (
                dev.coherence_factor < self.COHERENCE_MIN or
                dev.harmonic_index < self.HARMONIC_MEAN_FACTOR * H_mean or
                dev.resonance_strength < self.RESONANCE_MIN or
                dev.delta > self.DELTA_MAX
            )
            
            if has_anomaly:
                # Classify anomaly
                anom_type, severity, is_leak = self.classify_anomaly_type(
                    dev.coherence_factor,
                    dev.harmonic_index,
                    dev.resonance_strength,
                    dev.delta,
                    H_mean
                )
                
                # Generate description
                desc_parts = []
                if dev.coherence_factor < self.COHERENCE_MIN:
                    desc_parts.append(f"C={dev.coherence_factor:.4f}<{self.COHERENCE_MIN}")
                if dev.harmonic_index < self.HARMONIC_MEAN_FACTOR * H_mean:
                    desc_parts.append(f"H={dev.harmonic_index:.4f}<{self.HARMONIC_MEAN_FACTOR*H_mean:.4f}")
                if dev.resonance_strength < self.RESONANCE_MIN:
                    desc_parts.append(f"R={dev.resonance_strength:.4f}<{self.RESONANCE_MIN}")
                if dev.delta > self.DELTA_MAX:
                    desc_parts.append(f"δ={dev.delta:.4f}>{self.DELTA_MAX}")
                
                description = "; ".join(desc_parts)
                
                anomalies.append(VibrationalAnomaly(
                    prime=dev.prime,
                    anomaly_type=anom_type,
                    severity=severity,
                    delta=dev.delta,
                    coherence_factor=dev.coherence_factor,
                    harmonic_index=dev.harmonic_index,
                    resonance_strength=dev.resonance_strength,
                    description=description,
                    is_spectral_leak=is_leak
                ))
        
        return anomalies
    
    # ========================================================================
    # FULL VERIFICATION PROCEDURE
    # ========================================================================
    
    def verify_coherence(
        self,
        n_zeros: Optional[int] = None,
        alignment_factor: float = 1.0
    ) -> Dict[str, any]:
        """
        Execute full 3-step verification procedure.
        
        Steps:
            1. Inverse interpolation: Zeros → Primes
            2. Tensorial comparison with 𝒯ₚ(Ψ)
            3. Vibrational anomaly identification
        
        Args:
            n_zeros: Number of zeros to use (default: all known)
            alignment_factor: Spectral alignment calibration
            
        Returns:
            Dictionary with verification results
        """
        # Step 1: Inverse Interpolation
        zeros = self.ZEROS_IM[:n_zeros] if n_zeros else self.ZEROS_IM
        interpolations = self.inverse_interpolation(zeros, alignment_factor)
        
        # Create mapping of primes to zero frequencies
        zero_freq_map = {}
        for interp in interpolations:
            # Find nearest prime to estimated prime
            p_est = interp.estimated_prime
            if p_est > 0:
                nearest_idx = np.argmin(np.abs(self.primes - p_est))
                nearest_prime = self.primes[nearest_idx]
                zero_freq_map[nearest_prime] = interp.estimated_frequency
        
        # Step 2: Tensorial Comparison
        deviations = self.tensorial_comparison(
            primes=self.primes,
            zero_frequencies=zero_freq_map
        )
        
        # Step 3: Anomaly Identification
        anomalies = self.identify_vibrational_anomalies(deviations)
        
        # Compile statistics
        n_leaks = sum(1 for d in deviations if d.is_leak)
        n_anomalies = len(anomalies)
        n_spectral_leaks = sum(1 for a in anomalies if a.is_spectral_leak)
        
        # Coherence quality
        mean_delta = np.mean([d.delta for d in deviations])
        max_delta = np.max([d.delta for d in deviations])
        mean_coherence = np.mean([d.coherence_factor for d in deviations])
        
        return {
            'step1_interpolations': interpolations,
            'step2_deviations': deviations,
            'step3_anomalies': anomalies,
            'statistics': {
                'n_primes_analyzed': len(self.primes),
                'n_zeros_used': len(zeros),
                'n_coherence_leaks': n_leaks,
                'n_anomalies_total': n_anomalies,
                'n_spectral_leaks': n_spectral_leaks,
                'n_coding_errors': n_anomalies - n_spectral_leaks,
                'mean_deviation': mean_delta,
                'max_deviation': max_delta,
                'mean_coherence': mean_coherence,
                'coherence_quality': 1.0 - mean_delta,
            },
            'coherence_intact': n_spectral_leaks == 0,
            'message': self._generate_verdict(n_spectral_leaks, mean_delta)
        }
    
    def _generate_verdict(self, n_leaks: int, mean_delta: float) -> str:
        """Generate verification verdict message."""
        if n_leaks == 0 and mean_delta < self.DELTA_MAX:
            return (
                "✅ COHERENCIA QCAL CONFIRMADA\n"
                "No se detectaron fugas espectrales. "
                "El puente de superfluidez Riemann-PNP está intacto. "
                f"Desviación media: δ̄ = {mean_delta:.6f} < {self.DELTA_MAX}"
            )
        elif n_leaks > 0:
            return (
                f"⚠️ FUGAS ESPECTRALES DETECTADAS: {n_leaks}\n"
                "Se detectaron desviaciones en la red espectral que sugieren "
                "una curvatura local del espacio adélico. "
                f"Desviación media: δ̄ = {mean_delta:.6f}"
            )
        else:
            return (
                f"⚡ DESVIACIÓN ELEVADA: δ̄ = {mean_delta:.6f}\n"
                "La coherencia espectral muestra desviaciones por encima "
                "del umbral, pero no se clasifican como fugas estructurales."
            )
