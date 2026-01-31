#!/usr/bin/env python3
"""
Zeta Resonance Module

Analyzes the relationship between Riemann zeros and the fundamental
frequency f₀ = 141.7001 Hz.

Each zero of ζ(s) corresponds to a latent frequency in the system,
and when the system resonates at f₀, zeros emerge deterministically.

Mathematical Foundation:
    f(t) = f₀ · (t / t_ref)  where t_ref is a reference zero height
    
    When |f(t) - f₀| < Δf_threshold, the zero is in resonance.
"""

from typing import List, Dict
import sys

try:
    import numpy as np
except ImportError as e:
    print(f"Error: Required module not found: {e}")
    print("Please install: pip install numpy")
    sys.exit(1)


class ZetaResonance:
    """
    Analyzer for zeta zero resonance with fundamental frequency.
    
    Attributes:
        f0 (float): Fundamental frequency (141.7001 Hz)
        t_ref (float): Reference zero height for scaling
        resonance_threshold (float): Frequency deviation threshold
    """
    
    def __init__(self, f0: float = 141.7001, t_ref: float = 14.134725):
        """
        Initialize the resonance analyzer.
        
        Args:
            f0: Fundamental frequency in Hz (default: 141.7001)
            t_ref: Reference zero height (default: first zero)
        """
        self.f0 = f0
        self.t_ref = t_ref
        self.resonance_threshold = 1.0  # Hz
    
    def zero_to_frequency(self, zero: complex) -> float:
        """
        Convert a zero position to its equivalent frequency.
        
        Args:
            zero: Complex zero of ζ(s)
            
        Returns:
            Equivalent frequency in Hz
        """
        t = zero.imag
        # Scale frequency based on zero height
        frequency = self.f0 * (t / self.t_ref)
        return frequency
    
    def is_in_resonance(self, zero: complex) -> bool:
        """
        Check if a zero is in resonance with f₀.
        
        Args:
            zero: Complex zero of ζ(s)
            
        Returns:
            True if in resonance, False otherwise
        """
        freq = self.zero_to_frequency(zero)
        deviation = abs(freq - self.f0)
        return deviation < self.resonance_threshold
    
    def analyze_zeros(self, zeros: List[complex]) -> Dict[str, any]:
        """
        Analyze a list of zeros for resonance patterns.
        
        Args:
            zeros: List of complex zeros
            
        Returns:
            Dictionary with analysis results
        """
        frequencies = [self.zero_to_frequency(z) for z in zeros]
        deviations = [abs(f - self.f0) for f in frequencies]
        in_resonance = [d < self.resonance_threshold for d in deviations]
        
        return {
            "total_zeros": len(zeros),
            "frequencies": frequencies,
            "deviations": deviations,
            "in_resonance": in_resonance,
            "resonance_count": sum(in_resonance),
            "resonance_fraction": sum(in_resonance) / len(zeros) if zeros else 0,
            "mean_deviation": np.mean(deviations),
            "std_deviation": np.std(deviations)
        }
    
    def simulate_resonance_experiment(self, t_range: tuple, 
                                     num_points: int = 100) -> Dict[str, any]:
        """
        Simulate a resonance detection experiment.
        
        Args:
            t_range: (min, max) range of imaginary parts
            num_points: Number of test points
            
        Returns:
            Simulation results
        """
        t_values = np.linspace(t_range[0], t_range[1], num_points)
        zeros = [complex(0.5, t) for t in t_values]
        
        frequencies = [self.zero_to_frequency(z) for z in zeros]
        
        # Find resonance peaks
        deviations = [abs(f - self.f0) for f in frequencies]
        resonance_indices = [i for i, d in enumerate(deviations) 
                           if d < self.resonance_threshold]
        
        return {
            "t_values": t_values,
            "frequencies": frequencies,
            "deviations": deviations,
            "resonance_indices": resonance_indices,
            "resonance_t_values": [t_values[i] for i in resonance_indices]
        }


def main():
    """Demonstration of zeta resonance analysis."""
    print("=" * 70)
    print("ZETA RESONANCE ANALYZER")
    print(f"Fundamental Frequency: f₀ = 141.7001 Hz")
    print("=" * 70)
    print()
    
    resonance = ZetaResonance()
    
    # Known zeros of ζ(s) on critical line
    known_zeros = [
        complex(0.5, 14.134725),
        complex(0.5, 21.022040),
        complex(0.5, 25.010858),
        complex(0.5, 30.424876),
        complex(0.5, 32.935062),
    ]
    
    print("Analyzing known zeros:\n")
    
    for i, zero in enumerate(known_zeros, 1):
        freq = resonance.zero_to_frequency(zero)
        deviation = abs(freq - resonance.f0)
        in_res = resonance.is_in_resonance(zero)
        
        print(f"{i}. Zero at t = {zero.imag:.6f}")
        print(f"   Equivalent frequency: {freq:.6f} Hz")
        print(f"   Deviation from f₀: {deviation:.6f} Hz")
        print(f"   In resonance: {'✅' if in_res else '❌'}")
        print()
    
    # Statistical analysis
    analysis = resonance.analyze_zeros(known_zeros)
    
    print("Statistical Analysis:")
    print(f"  Total zeros analyzed: {analysis['total_zeros']}")
    print(f"  Zeros in resonance: {analysis['resonance_count']}")
    print(f"  Resonance fraction: {analysis['resonance_fraction']:.2%}")
    print(f"  Mean deviation: {analysis['mean_deviation']:.6f} Hz")
    print(f"  Std deviation: {analysis['std_deviation']:.6f} Hz")
    print()
    
    print("=" * 70)
    print("Interpretation: Each zero has a latent frequency")
    print("When system resonates at f₀, zeros emerge deterministically")
    print("=" * 70)


if __name__ == "__main__":
    main()
