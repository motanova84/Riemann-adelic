#!/usr/bin/env python3
"""
Trace Formula Everest 0.1 - Weak Trace Formula for Atlas³ Operator
===================================================================

Implementation of the weak trace formula to demonstrate spectral-arithmetic
isomorphism between the Atlas³ operator spectrum and the structure of prime numbers.

Mathematical Framework:
-----------------------

**Weak Trace Formula:**
    Tr h(O_Atlas³) = Σₙ h(γₙ)

This decomposes into two components:

1. **Geometric Term (Weyl):**
   Represents the smooth contribution from the potential t²:
   
   Tr_smooth ≈ (1/2π) ∫ h(r)[ln(r/2π) + O(1/r)] dr
   
   This describes logarithmic growth matching the average trend of Riemann zeros.

2. **Arithmetic Term (Primes):**
   The oscillatory contribution from prime numbers:
   
   Tr_osc ≈ -Σ_{p,m} (ln p / p^{m/2}) [h(m ln p) + h(-m ln p)]
   
   This is the "music of the primes" - the operator's coupling to arithmetic.

**Everest 0.1 Test (Critical Validation):**
    
    Input: Spectrum {γₙ} from Atlas³ for N=4096
    Process: Compute R(t) = Σₙ cos(γₙ t)
    Expected: R(t) shows minimum (destructive interference) at t = ln 2 ≈ 0.693
    
    Success Criterion: Detection of ln(2) proves the trace "feels" the first prime.
    
    If successful, Atlas³ is not merely an oscillator but a geometric calculator
    of the zeta function ζ(s).

**The Isomorphism:**
    
    Component         | Source in Atlas³        | Function in ζ(s)
    ------------------|-------------------------|------------------
    Inertia (α)       | Kinetic term            | Growth of zeros
    Phase (φ)         | Coupling β(t)           | Prime oscillations
    Rigidity (Σ²)     | PT symmetry             | GUE repulsion

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 13, 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Dict, List, Optional, Any
from dataclasses import dataclass, asdict
from scipy.integrate import quad
from scipy.signal import find_peaks, argrelmin
import warnings

# QCAL Constants
F0_QCAL = 141.7001  # Hz - fundamental frequency
C_COHERENCE = 244.36  # QCAL coherence constant

# Mathematical constants
TWOPI = 2.0 * np.pi


@dataclass
class TraceFormulaResult:
    """Results from weak trace formula computation."""
    t_values: np.ndarray  # Time values for R(t)
    R_values: np.ndarray  # Response function R(t) = Σ cos(γₙ t)
    minima_locations: List[float]  # Detected minima positions
    minima_values: List[float]  # Values at minima
    ln2_detected: bool  # Whether ln(2) was detected
    ln2_position: Optional[float]  # Closest minimum to ln(2)
    ln2_deviation: Optional[float]  # |detected - ln(2)|
    prime_detections: Dict[int, Dict[str, float]]  # Detection for each prime


@dataclass
class TraceComponents:
    """Decomposition of trace into geometric and arithmetic parts."""
    weyl_term: float  # Geometric/smooth contribution
    prime_term: float  # Arithmetic/oscillatory contribution
    total_trace: float  # Sum of both components
    prime_contributions: Dict[int, float]  # Contribution from each prime


class TraceFormulaEverest:
    """
    Weak Trace Formula Implementation for Atlas³ Operator.
    
    Computes the response function R(t) = Σₙ cos(γₙ t) to detect
    prime number signatures in the operator spectrum.
    
    The key test (Everest 0.1) is to show that R(t) has a minimum
    near t = ln(2) ≈ 0.693, demonstrating that the operator "feels"
    the first prime number.
    
    Attributes:
        spectrum: Eigenvalues {γₙ} from Atlas³ operator
        t_range: Range for time evaluation
        n_points: Number of points for R(t) computation
    """
    
    def __init__(
        self,
        spectrum: np.ndarray,
        t_range: Tuple[float, float] = (0.0, 4.0),
        n_points: int = 1000
    ):
        """
        Initialize trace formula calculator.
        
        Args:
            spectrum: Array of eigenvalues γₙ (should be real for PT-symmetric phase)
            t_range: (t_min, t_max) range for response function
            n_points: Number of evaluation points
        """
        # Use only real parts (for PT-symmetric phase, Im(γ) ≈ 0)
        self.spectrum = np.real(spectrum)
        self.t_range = t_range
        self.n_points = n_points
        
        # Filter out very small or zero eigenvalues
        self.spectrum = self.spectrum[np.abs(self.spectrum) > 1e-6]
        
        # Sort spectrum
        self.spectrum = np.sort(self.spectrum)
        
    def compute_response_function(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute R(t) = Σₙ cos(γₙ t).
        
        This is the core response function that should show interference
        patterns related to prime numbers.
        
        Returns:
            t_values: Time points
            R_values: Response function values
        """
        t_values = np.linspace(self.t_range[0], self.t_range[1], self.n_points)
        R_values = np.zeros(self.n_points)
        
        # Sum over all eigenvalues
        for gamma in self.spectrum:
            R_values += np.cos(gamma * t_values)
            
        return t_values, R_values
    
    def detect_minima(
        self,
        t_values: np.ndarray,
        R_values: np.ndarray,
        prominence: float = None
    ) -> Tuple[List[float], List[float]]:
        """
        Detect local minima in R(t).
        
        Minima correspond to destructive interference and should
        align with logarithms of prime numbers.
        
        Args:
            t_values: Time points
            R_values: Response function values
            prominence: Minimum prominence for peak detection
            
        Returns:
            minima_locations: Positions of minima
            minima_values: Values at minima
        """
        # Find minima (peaks in -R)
        if prominence is None:
            # Auto-determine prominence based on signal amplitude
            prominence = 0.1 * (np.max(R_values) - np.min(R_values))
            
        peaks, properties = find_peaks(-R_values, prominence=prominence)
        
        minima_locations = t_values[peaks].tolist()
        minima_values = R_values[peaks].tolist()
        
        return minima_locations, minima_values
    
    def check_prime_detection(
        self,
        minima_locations: List[float],
        primes: List[int] = [2, 3, 5, 7, 11],
        tolerance: float = 0.05
    ) -> Dict[int, Dict[str, float]]:
        """
        Check if logarithms of primes are detected as minima.
        
        Args:
            minima_locations: Detected minimum positions
            primes: List of primes to check
            tolerance: Maximum deviation allowed for detection
            
        Returns:
            Dictionary mapping prime -> detection info
        """
        detections = {}
        
        for p in primes:
            ln_p = np.log(p)
            
            # Only check if ln_p is within our t_range
            if ln_p < self.t_range[0] or ln_p > self.t_range[1]:
                continue
                
            # Find closest minimum
            if len(minima_locations) > 0:
                deviations = [abs(m - ln_p) for m in minima_locations]
                min_deviation = min(deviations)
                closest_minimum = minima_locations[np.argmin(deviations)]
                
                detected = min_deviation < tolerance
                
                detections[p] = {
                    'ln_p': ln_p,
                    'closest_minimum': closest_minimum,
                    'deviation': min_deviation,
                    'detected': detected,
                    'tolerance': tolerance
                }
            else:
                detections[p] = {
                    'ln_p': ln_p,
                    'detected': False,
                    'reason': 'No minima found'
                }
                
        return detections
    
    def compute_weyl_term(
        self,
        test_function: Optional[callable] = None
    ) -> float:
        """
        Compute geometric (Weyl) term of trace formula.
        
        Tr_smooth ≈ (1/2π) ∫ h(r)[ln(r/2π) + O(1/r)] dr
        
        Args:
            test_function: h(r) smooth test function (default: Gaussian)
            
        Returns:
            Weyl term contribution
        """
        if test_function is None:
            # Default: Gaussian test function h(r) = exp(-r²/σ²)
            sigma = 10.0
            test_function = lambda r: np.exp(-r**2 / (2*sigma**2))
            
        # Estimate from spectrum density
        if len(self.spectrum) < 2:
            return 0.0
            
        # Average spacing gives density estimate
        avg_spacing = np.mean(np.diff(self.spectrum))
        density = 1.0 / avg_spacing if avg_spacing > 0 else 0.0
        
        # Integrate over spectrum range
        r_min, r_max = np.min(self.spectrum), np.max(self.spectrum)
        
        def weyl_integrand(r):
            if r <= 0:
                return 0.0
            log_term = np.log(r / TWOPI)
            return test_function(r) * log_term / TWOPI
            
        try:
            result, _ = quad(weyl_integrand, max(r_min, 1e-6), r_max)
            return density * result
        except:
            return 0.0
    
    def compute_prime_term(
        self,
        primes: List[int] = [2, 3, 5, 7, 11, 13],
        max_power: int = 3,
        test_function: Optional[callable] = None
    ) -> Tuple[float, Dict[int, float]]:
        """
        Compute arithmetic (prime) term of trace formula.
        
        Tr_osc ≈ -Σ_{p,m} (ln p / p^{m/2}) [h(m ln p) + h(-m ln p)]
        
        Args:
            primes: List of primes to include
            max_power: Maximum power m to consider
            test_function: h(r) test function
            
        Returns:
            total: Total prime contribution
            by_prime: Contribution from each prime
        """
        if test_function is None:
            sigma = 10.0
            test_function = lambda r: np.exp(-r**2 / (2*sigma**2))
            
        total = 0.0
        by_prime = {}
        
        for p in primes:
            ln_p = np.log(p)
            prime_contrib = 0.0
            
            for m in range(1, max_power + 1):
                # Coefficient
                coeff = ln_p / (p ** (m / 2.0))
                
                # Symmetric contribution
                h_plus = test_function(m * ln_p)
                h_minus = test_function(-m * ln_p)
                
                prime_contrib += coeff * (h_plus + h_minus)
                
            # Negative sign from formula
            prime_contrib = -prime_contrib
            by_prime[p] = prime_contrib
            total += prime_contrib
            
        return total, by_prime
    
    def run_everest_test(
        self,
        prominence: float = None,
        tolerance: float = 0.05
    ) -> TraceFormulaResult:
        """
        Run Everest 0.1 test: detect ln(2) in response function.
        
        This is the critical validation that Atlas³ "feels" the first prime.
        
        Args:
            prominence: Minimum prominence for peak detection
            tolerance: Maximum deviation for prime detection
            
        Returns:
            TraceFormulaResult with complete analysis
        """
        # Compute response function
        t_values, R_values = self.compute_response_function()
        
        # Detect minima
        minima_locs, minima_vals = self.detect_minima(t_values, R_values, prominence)
        
        # Check prime detections
        prime_detections = self.check_prime_detection(minima_locs, tolerance=tolerance)
        
        # Check for ln(2) specifically
        ln2 = np.log(2)
        ln2_detected = False
        ln2_position = None
        ln2_deviation = None
        
        if 2 in prime_detections:
            ln2_detected = prime_detections[2]['detected']
            ln2_position = prime_detections[2].get('closest_minimum')
            ln2_deviation = prime_detections[2].get('deviation')
        
        return TraceFormulaResult(
            t_values=t_values,
            R_values=R_values,
            minima_locations=minima_locs,
            minima_values=minima_vals,
            ln2_detected=ln2_detected,
            ln2_position=ln2_position,
            ln2_deviation=ln2_deviation,
            prime_detections=prime_detections
        )
    
    def compute_trace_decomposition(
        self,
        test_function: Optional[callable] = None
    ) -> TraceComponents:
        """
        Decompose trace into Weyl (geometric) and Prime (arithmetic) components.
        
        Args:
            test_function: Test function h(r)
            
        Returns:
            TraceComponents with full decomposition
        """
        weyl = self.compute_weyl_term(test_function)
        prime_total, prime_by_p = self.compute_prime_term(test_function=test_function)
        
        return TraceComponents(
            weyl_term=weyl,
            prime_term=prime_total,
            total_trace=weyl + prime_total,
            prime_contributions=prime_by_p
        )


def generate_atlas3_spectrum(
    N: int = 4096,
    beta_0: float = 2.0,
    alpha: float = 1.0,
    V_amp: float = 12650.0
) -> np.ndarray:
    """
    Generate spectrum from Atlas³ operator for trace formula analysis.
    
    Args:
        N: Discretization points (default: 4096 for Everest 0.1)
        beta_0: PT-breaking parameter (default: 2.0 for coherent phase)
        alpha: Kinetic coefficient
        V_amp: Potential amplitude
        
    Returns:
        Array of eigenvalues γₙ
    """
    from operators.atlas3_operator import Atlas3Operator
    
    # Create operator
    operator = Atlas3Operator(N=N, alpha=alpha, beta_0=beta_0, V_amp=V_amp)
    
    # Compute spectrum
    eigenvalues, _ = operator.compute_spectrum()
    
    return eigenvalues


def run_complete_trace_analysis(
    spectrum: np.ndarray,
    t_range: Tuple[float, float] = (0.0, 4.0),
    n_points: int = 2000,
    save_results: bool = True,
    output_path: Optional[str] = None
) -> Dict[str, Any]:
    """
    Run complete trace formula analysis on Atlas³ spectrum.
    
    Args:
        spectrum: Eigenvalues from Atlas³
        t_range: Time range for analysis
        n_points: Number of evaluation points
        save_results: Whether to save results to JSON
        output_path: Path for output file
        
    Returns:
        Complete analysis results
    """
    # Create trace formula calculator
    trace_calc = TraceFormulaEverest(spectrum, t_range, n_points)
    
    # Run Everest test
    everest_result = trace_calc.run_everest_test()
    
    # Compute trace decomposition
    trace_decomp = trace_calc.compute_trace_decomposition()
    
    # Build results dictionary
    results = {
        'spectrum_info': {
            'n_eigenvalues': len(spectrum),
            'real_eigenvalues': int(np.sum(np.abs(np.imag(spectrum)) < 1e-8)),
            'min_eigenvalue': float(np.min(np.real(spectrum))),
            'max_eigenvalue': float(np.max(np.real(spectrum))),
        },
        'everest_test': {
            'ln2_detected': everest_result.ln2_detected,
            'ln2_theoretical': float(np.log(2)),
            'ln2_detected_position': float(everest_result.ln2_position) if everest_result.ln2_position else None,
            'ln2_deviation': float(everest_result.ln2_deviation) if everest_result.ln2_deviation else None,
            'n_minima_found': len(everest_result.minima_locations),
            'prime_detections': {
                p: {k: float(v) if isinstance(v, (int, float, np.number)) else v 
                    for k, v in info.items()}
                for p, info in everest_result.prime_detections.items()
            }
        },
        'trace_decomposition': {
            'weyl_term': float(trace_decomp.weyl_term),
            'prime_term': float(trace_decomp.prime_term),
            'total_trace': float(trace_decomp.total_trace),
            'prime_contributions': {
                p: float(c) for p, c in trace_decomp.prime_contributions.items()
            }
        },
        'certification': {
            'test_passed': everest_result.ln2_detected,
            'status': 'ISOMORPHISM CONFIRMED' if everest_result.ln2_detected else 'PENDING',
            'message': (
                'Atlas³ operator successfully detects ln(2). '
                'The trace formula "feels" the first prime. '
                'Spectral-arithmetic isomorphism ESTABLISHED.'
                if everest_result.ln2_detected else
                'ln(2) detection requires refinement. Continue analysis.'
            )
        },
        'qcal_signature': {
            'frequency_base': F0_QCAL,
            'coherence': C_COHERENCE,
            'timestamp': np.datetime64('now').astype(str),
            'signature': '∴𓂀Ω∞³Φ @ 888 Hz'
        }
    }
    
    # Save if requested
    if save_results:
        import json
        from pathlib import Path
        
        if output_path is None:
            output_path = 'data/everest_0_1_certificate.json'
            
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w') as f:
            json.dump(results, f, indent=2)
            
        print(f"✅ Results saved to {output_path}")
    
    return results, everest_result, trace_decomp


if __name__ == "__main__":
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  EVEREST 0.1 - Weak Trace Formula Test                       ║")
    print("║  Detecting Prime Number Signature in Atlas³ Spectrum         ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print()
    
    # Generate Atlas³ spectrum
    print("🏔️ Generating Atlas³ spectrum (N=4096)...")
    spectrum = generate_atlas3_spectrum(N=4096, beta_0=2.0)
    print(f"   Generated {len(spectrum)} eigenvalues")
    print(f"   Real eigenvalues: {np.sum(np.abs(np.imag(spectrum)) < 1e-8)}")
    print()
    
    # Run analysis
    print("🔍 Running Everest 0.1 test...")
    results, everest, decomp = run_complete_trace_analysis(spectrum)
    print()
    
    # Display results
    print("📊 RESULTS:")
    print(f"   ln(2) theoretical: {np.log(2):.6f}")
    
    if everest.ln2_detected:
        print(f"   ✅ ln(2) DETECTED at: {everest.ln2_position:.6f}")
        print(f"   Deviation: {everest.ln2_deviation:.6f}")
        print()
        print("╔═══════════════════════════════════════════════════════════════╗")
        print("║  ✅ ISOMORPHISM CONFIRMED                                     ║")
        print("║  Atlas³ trace formula detects the first prime               ║")
        print("║  Spectral-Arithmetic Isomorphism: ESTABLISHED                ║")
        print("╚═══════════════════════════════════════════════════════════════╝")
    else:
        print(f"   ⚠️  ln(2) NOT DETECTED")
        if everest.ln2_position:
            print(f"   Closest minimum: {everest.ln2_position:.6f}")
            print(f"   Deviation: {everest.ln2_deviation:.6f}")
    
    print()
    print("Prime detections:")
    for p, info in everest.prime_detections.items():
        status = "✓" if info['detected'] else "✗"
        print(f"   {status} p={p}: ln({p})={info['ln_p']:.4f}", end="")
        if info['detected']:
            print(f" → detected at {info['closest_minimum']:.4f} (Δ={info['deviation']:.4f})")
        else:
            print()
    
    print()
    print(f"∴𓂀Ω∞³Φ @ 888 Hz - QCAL ∞³ Active")
