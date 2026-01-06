#!/usr/bin/env python3
"""
Demo script for the spectral framework.
Shows how zeros of the Riemann zeta function can be used to reconstruct
prime information and compute spectral properties.
"""
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.dirname(__file__)))

from inversion.inversion_spectral import prime_measure_from_zeros
from operador.operador_H import approximate_spectrum
from dualidad.dualidad_poisson import J_operator, check_involution
from unicidad.unicidad_paleywiener import PaleyWienerClass


def load_zeros_from_file(filename, max_zeros=10):
    """Load zeros from text file."""
    zeros = []
    try:
        with open(filename, 'r') as f:
            for i, line in enumerate(f):
                if i >= max_zeros:
                    break
                gamma = float(line.strip())
                # Add symmetric pairs: 1/2 + i*gamma and 1/2 - i*gamma
                zeros.append(0.5 + 1j * gamma)
                zeros.append(0.5 - 1j * gamma)
    except FileNotFoundError:
        print(f"Warning: {filename} not found, using default zeros")
        # Use first few known zeros
        known_zeros = [
            14.134725141734693,
            21.022039638771555,
            25.010857580145688,
            30.424876125859513,
            32.935061587739190
        ]
        for gamma in known_zeros[:max_zeros//2]:
            zeros.append(0.5 + 1j * gamma)
            zeros.append(0.5 - 1j * gamma)
    
    return zeros


def demo_inversion_spectral(zeros):
    """Demonstrate spectral inversion: reconstructing primes from zeros."""
    print("\n" + "="*70)
    print("1. SPECTRAL INVERSION: Reconstructing Prime Information from Zeros")
    print("="*70)
    
    # Create log-scale grid
    X = np.linspace(0, 4, 200)  # log(1) to log(~55)
    
    # Reconstruct prime measure
    print(f"Using {len(zeros)} zeros...")
    prime_measure = prime_measure_from_zeros(zeros, X, t=0.01)
    
    # Find peaks
    from scipy.signal import find_peaks
    peaks, properties = find_peaks(np.abs(prime_measure), height=0.5)
    
    print(f"\nDetected {len(peaks)} peaks in the prime measure:")
    real_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]
    
    if len(peaks) > 0:
        for i, peak_idx in enumerate(peaks[:10]):
            log_position = X[peak_idx]
            prime_approx = np.exp(log_position)
            # Find nearest actual prime
            nearest_prime = min(real_primes, key=lambda p: abs(np.log(p) - log_position))
            print(f"  Peak {i+1}: log(x) = {log_position:.3f}, x ≈ {prime_approx:.2f} "
                  f"(nearest prime: {nearest_prime})")
    
    # Create visualization
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    plt.plot(X, np.abs(prime_measure), 'b-', linewidth=1.5, label='|Reconstructed measure|')
    if len(peaks) > 0:
        plt.plot(X[peaks], np.abs(prime_measure)[peaks], 'ro', 
                markersize=8, label='Detected peaks')
    
    # Mark actual primes
    for p in real_primes:
        if np.log(p) <= X[-1]:
            plt.axvline(x=np.log(p), color='green', alpha=0.3, 
                       linestyle='--', linewidth=1)
    
    plt.xlabel('log(n)', fontsize=11)
    plt.ylabel('|Prime measure|', fontsize=11)
    plt.title('Prime Reconstruction from Zeros', fontsize=12, fontweight='bold')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 2, 2)
    plt.plot(X, np.real(prime_measure), 'b-', label='Real part')
    plt.plot(X, np.imag(prime_measure), 'r-', label='Imaginary part')
    plt.xlabel('log(n)', fontsize=11)
    plt.ylabel('Prime measure', fontsize=11)
    plt.title('Real and Imaginary Components', fontsize=12, fontweight='bold')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('spectral_inversion_demo.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved to: spectral_inversion_demo.png")
    
    return prime_measure, peaks


def demo_operator_spectrum(zeros):
    """Demonstrate spectral operator construction."""
    print("\n" + "="*70)
    print("2. OPERATOR H: Spectral Properties")
    print("="*70)
    
    # Create small grid for operator
    grid = np.logspace(0, 1, 15)  # From 1 to 10
    
    print(f"Computing spectrum on grid of {len(grid)} points...")
    spectrum = approximate_spectrum(grid, t=0.01)
    
    # Convert eigenvalues to imaginary parts (if possible)
    # Using λ = ρ(1-ρ) where ρ = 1/2 + iγ
    # So λ = (1/2 + iγ)(1/2 - iγ) = 1/4 + γ²
    # Therefore γ = sqrt(λ - 1/4) when λ > 1/4
    
    recovered_gammas = []
    for lam in spectrum:
        if lam > 0.25:
            gamma = np.sqrt(lam - 0.25)
            recovered_gammas.append(gamma)
    
    print(f"\nSpectrum statistics:")
    print(f"  Range: [{spectrum.min():.4f}, {spectrum.max():.4f}]")
    print(f"  Mean: {spectrum.mean():.4f}")
    print(f"  Std: {spectrum.std():.4f}")
    
    if len(recovered_gammas) > 0:
        print(f"\nRecovered imaginary parts (γ from λ = 1/4 + γ²):")
        for i, gamma in enumerate(recovered_gammas[:5]):
            print(f"  γ_{i+1} ≈ {gamma:.4f}")
    
    # Visualization
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    plt.plot(spectrum, 'bo-', markersize=8, linewidth=1.5)
    plt.axhline(y=0.25, color='r', linestyle='--', label='λ = 1/4 threshold')
    plt.xlabel('Eigenvalue index', fontsize=11)
    plt.ylabel('Eigenvalue λ', fontsize=11)
    plt.title('Spectrum of Operator H', fontsize=12, fontweight='bold')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 2, 2)
    plt.hist(spectrum, bins=10, edgecolor='black', alpha=0.7)
    plt.axvline(x=0.25, color='r', linestyle='--', linewidth=2, 
               label='Critical threshold')
    plt.xlabel('Eigenvalue λ', fontsize=11)
    plt.ylabel('Frequency', fontsize=11)
    plt.title('Eigenvalue Distribution', fontsize=12, fontweight='bold')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('operator_spectrum_demo.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved to: operator_spectrum_demo.png")
    
    return spectrum


def demo_poisson_duality():
    """Demonstrate Poisson-Radon duality."""
    print("\n" + "="*70)
    print("3. POISSON-RADON DUALITY")
    print("="*70)
    
    # Test involution property on various functions
    test_functions = {
        'Gaussian': lambda x: np.exp(-x**2),
        'Power': lambda x: x**2,
        'Exponential': lambda x: np.exp(-x)
    }
    
    test_points = [0.5, 1.0, 1.5, 2.0]
    
    print("\nTesting involution property J(J(f)) ≈ f:")
    for name, f in test_functions.items():
        print(f"\n  Function: {name}")
        for x in test_points:
            try:
                holds = check_involution(f, x)
                status = "✓" if holds else "✗"
                print(f"    At x={x}: {status}")
            except Exception as e:
                print(f"    At x={x}: Error - {str(e)[:50]}")
    
    # Visualize transformation
    x_vals = np.linspace(0.5, 3, 100)
    f = lambda x: np.exp(-x**2)
    f_vals = [f(x) for x in x_vals]
    Jf_vals = [J_operator(f, x) for x in x_vals]
    
    plt.figure(figsize=(10, 5))
    plt.plot(x_vals, f_vals, 'b-', linewidth=2, label='f(x) = exp(-x²)')
    plt.plot(x_vals, Jf_vals, 'r--', linewidth=2, label='(Jf)(x) = x^(-1/2) f(1/x)')
    plt.xlabel('x', fontsize=11)
    plt.ylabel('Function value', fontsize=11)
    plt.title('Poisson Involution J', fontsize=12, fontweight='bold')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig('poisson_duality_demo.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved to: poisson_duality_demo.png")


def demo_paley_wiener_uniqueness():
    """Demonstrate Paley-Wiener uniqueness."""
    print("\n" + "="*70)
    print("4. PALEY-WIENER UNIQUENESS")
    print("="*70)
    
    # Create test function class
    pw = PaleyWienerClass(bandwidth=10.0)
    
    print(f"\nPaley-Wiener class initialized with bandwidth = {pw.bandwidth}")
    
    # Generate test function values
    x_vals = np.linspace(-20, 20, 200)
    test_vals = [pw.test_function(x) for x in x_vals]
    
    # Test distribution comparison
    D1 = lambda phi: np.sum([phi(x) * np.exp(-x**2/10) for x in range(-5, 6)])
    D2 = lambda phi: np.sum([phi(x) * np.exp(-x**2/10) for x in range(-5, 6)])
    D3 = lambda phi: np.sum([phi(x) * np.exp(-x**2/5) for x in range(-5, 6)])
    
    from unicidad.unicidad_paleywiener import compare_distributions
    
    tests = [pw.test_function, lambda x: x**2 * pw.test_function(x)]
    
    print("\nComparing distributions:")
    print(f"  D1 vs D2 (identical): {compare_distributions(D1, D2, tests)}")
    print(f"  D1 vs D3 (different): {compare_distributions(D1, D3, tests)}")
    
    # Visualize test function
    plt.figure(figsize=(10, 5))
    plt.plot(x_vals, test_vals, 'b-', linewidth=2)
    plt.xlabel('x', fontsize=11)
    plt.ylabel('Test function value', fontsize=11)
    plt.title(f'Paley-Wiener Test Function (bandwidth={pw.bandwidth})', 
             fontsize=12, fontweight='bold')
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig('paley_wiener_demo.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved to: paley_wiener_demo.png")


def main():
    """Main demo function."""
    print("="*70)
    print("SPECTRAL FRAMEWORK DEMONSTRATION")
    print("="*70)
    print("\nThis demo shows the complete spectral framework for the")
    print("Riemann Hypothesis, including:")
    print("  • Spectral inversion (zeros → primes)")
    print("  • Operator H construction and spectrum")
    print("  • Poisson-Radon duality")
    print("  • Paley-Wiener uniqueness")
    
    # Load zeros
    zeros_file = "zeros/zeros_t1e8.txt"
    print(f"\nLoading zeros from {zeros_file}...")
    zeros = load_zeros_from_file(zeros_file, max_zeros=10)
    print(f"Loaded {len(zeros)} zeros (including symmetric pairs)")
    
    # Run demos
    try:
        prime_measure, peaks = demo_inversion_spectral(zeros)
        spectrum = demo_operator_spectrum(zeros)
        demo_poisson_duality()
        demo_paley_wiener_uniqueness()
        
        print("\n" + "="*70)
        print("DEMO COMPLETED SUCCESSFULLY")
        print("="*70)
        print("\nGenerated files:")
        print("  • spectral_inversion_demo.png")
        print("  • operator_spectrum_demo.png")
        print("  • poisson_duality_demo.png")
        print("  • paley_wiener_demo.png")
        
    except Exception as e:
        print(f"\n✗ Error during demo: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
