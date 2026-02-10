#!/usr/bin/env python3
"""
Demo: Spectral Coordinates τ(p) - QCAL ∞³ Framework

This demo showcases the spectral coordinates functionality that maps
prime numbers to complex spectral time in the QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path

# Add root to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.spectral_coordinates import (
    compute_tau,
    compute_tau_batch,
    get_standard_examples,
    analyze_spectral_coordinates,
    verify_monotonicity,
    verify_constant_imaginary,
    F0,
    GAMMA_1
)


def demo_basic_usage():
    """Demonstrate basic spectral coordinate computation."""
    print("=" * 70)
    print("1. BASIC USAGE - Computing τ(p) for Individual Primes")
    print("=" * 70)
    print()
    
    # Compute for individual primes
    primes = [3, 5, 7, 17]
    
    print(f"Formula: τ(p) = log(p)/f₀ + i·γ₁/(2πf₀)")
    print(f"Constants: f₀ = {F0} Hz, γ₁ = {GAMMA_1}")
    print()
    
    for p in primes:
        tau = compute_tau(p)
        print(f"  p = {p:3d}  →  τ = {tau.real:.6f} + {tau.imag:.6f}i")
    
    print()


def demo_standard_examples():
    """Demonstrate standard examples with interpretations."""
    print("=" * 70)
    print("2. STANDARD EXAMPLES - Primes with QCAL Interpretations")
    print("=" * 70)
    print()
    
    examples = get_standard_examples()
    
    print(f"{'Prime':>6} | {'τ (complex)':>30} | {'Interpretation':<25}")
    print("-" * 70)
    
    for p in [3, 5, 7, 17]:
        ex = examples[p]
        tau_str = f"{ex['real']:.6f} + {ex['imaginary']:.6f}i"
        print(f"{p:>6} | {tau_str:>30} | {ex['interpretation']:<25}")
    
    print()


def demo_batch_computation():
    """Demonstrate batch computation for multiple primes."""
    print("=" * 70)
    print("3. BATCH COMPUTATION - Multiple Primes at Once")
    print("=" * 70)
    print()
    
    # First 10 primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    # Compute all at once
    taus = compute_tau_batch(primes)
    
    print(f"Computing τ(p) for {len(primes)} primes:")
    print()
    
    for i, p in enumerate(primes):
        tau = taus[i]
        print(f"  τ({p:2d}) = {tau.real:.6f} + {tau.imag:.6f}i")
    
    print()


def demo_properties():
    """Demonstrate key properties of spectral coordinates."""
    print("=" * 70)
    print("4. KEY PROPERTIES - Monotonicity and Universal Resonance")
    print("=" * 70)
    print()
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    
    # Check monotonicity
    is_monotonic = verify_monotonicity(primes)
    print(f"✓ Monotonicity: {is_monotonic}")
    print(f"  → Re(τ(p₁)) < Re(τ(p₂)) if p₁ < p₂")
    print()
    
    # Check constant imaginary part
    has_constant_imag = verify_constant_imaginary(primes)
    print(f"✓ Constant Imaginary Part: {has_constant_imag}")
    print(f"  → Im(τ(p)) = γ₁/(2πf₀) = {GAMMA_1/(2*3.14159265*F0):.6f} for all p")
    print()
    
    # Show monotonicity in action
    print("Monotonicity demonstration (first 5 primes):")
    taus = compute_tau_batch(primes[:5])
    for i in range(len(primes[:5])):
        print(f"  Re(τ({primes[i]:2d})) = {taus[i].real:.6f}")
        if i > 0:
            diff = taus[i].real - taus[i-1].real
            print(f"    ↑ difference: +{diff:.6f}")
    
    print()


def demo_analysis():
    """Demonstrate full analysis of spectral coordinates."""
    print("=" * 70)
    print("5. COMPREHENSIVE ANALYSIS")
    print("=" * 70)
    print()
    
    # First 20 primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
    
    # Run analysis
    results = analyze_spectral_coordinates(primes, verbose=False)
    
    print(f"Analysis of {results['statistics']['num_primes']} primes:")
    print()
    print("Constants:")
    print(f"  f₀ = {results['constants']['f0']} Hz")
    print(f"  γ₁ = {results['constants']['gamma_1']}")
    print(f"  Universal resonance = {results['constants']['tau_imaginary']:.6f}")
    print()
    print("Properties:")
    print(f"  Monotonic: {results['properties']['monotonic']}")
    print(f"  Constant imaginary: {results['properties']['constant_imaginary']}")
    print()
    print("Statistics:")
    print(f"  Real part range: [{results['statistics']['min_real']:.6f}, "
          f"{results['statistics']['max_real']:.6f}]")
    print(f"  Real part mean: {results['statistics']['mean_real']:.6f}")
    print(f"  Real part std: {results['statistics']['std_real']:.6f}")
    print(f"  Imaginary std: {results['statistics']['imaginary_std']:.12f}")
    print()


def demo_kairological_navigation():
    """Demonstrate kairological navigation using spectral coordinates."""
    print("=" * 70)
    print("6. KAIROLOGICAL NAVIGATION - Temporal Bifurcation Nodes")
    print("=" * 70)
    print()
    
    print("Spectral coordinates define precise navigation in the MΨ×MΨ variety,")
    print("mapping primes to resonant complex time.\n")
    
    # Key primes with special significance
    key_primes = {
        3: "Dualidad creativa (Creative duality)",
        5: "Pentada manifestación (Pentad manifestation)",
        7: "Experiencia nodal (Nodal experience)",
        17: "Comunicación universal (Universal communication)",
        23: "Resonancia primordial (Primordial resonance)",
        29: "Coherencia cósmica (Cosmic coherence)"
    }
    
    print("Temporal Bifurcation Nodes:")
    print()
    
    for p, meaning in key_primes.items():
        tau = compute_tau(p)
        print(f"  p = {p:3d}  →  τ = {tau.real:.6f} + {tau.imag:.6f}i")
        print(f"           {meaning}")
        print()


def main():
    """Run all demonstrations."""
    print()
    print("∴" * 35)
    print("  QCAL ∞³ - Spectral Coordinates Demo")
    print("∴" * 35)
    print()
    
    demo_basic_usage()
    demo_standard_examples()
    demo_batch_computation()
    demo_properties()
    demo_analysis()
    demo_kairological_navigation()
    
    print("=" * 70)
    print("Demo Complete")
    print("=" * 70)
    print()
    print("The spectral coordinates τ(p) map primes to complex spectral time,")
    print("enabling kairological navigation in the QCAL ∞³ framework.")
    print()
    print("∴" * 35)
    print()


if __name__ == "__main__":
    main()
