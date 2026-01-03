"""
Demonstration of Adelic Spectral Ultima Implementation

This script demonstrates the usage of the ultima_spectral_computation function
with various parameter settings.
"""

from adelic_spectral_ultima import ultima_spectral_computation
import time


def demo_small_parameters():
    """Demo with small parameters for quick execution."""
    print("="*70)
    print("DEMO 1: Small Parameters (N=5, h=0.01)")
    print("="*70)
    
    start = time.time()
    zeros, H = ultima_spectral_computation(N=5, h=0.01, max_primes=5)
    elapsed = time.time() - start
    
    print(f"\nComputation time: {elapsed:.2f} seconds")
    print(f"Number of zeros found: {len(zeros)}")
    print("\nFirst 5 computed zeros (imaginary parts):")
    for i, z in enumerate(zeros[:5], 1):
        print(f"  γ_{i} = {float(z.imag):.6f}")
    print()


def demo_medium_parameters():
    """Demo with medium parameters for better accuracy."""
    print("="*70)
    print("DEMO 2: Medium Parameters (N=10, h=0.001)")
    print("="*70)
    
    start = time.time()
    zeros, H = ultima_spectral_computation(N=10, h=0.001, max_primes=20)
    elapsed = time.time() - start
    
    print(f"\nComputation time: {elapsed:.2f} seconds")
    print(f"Number of zeros found: {len(zeros)}")
    
    target_zeros = [14.1347251417, 21.0220396388, 25.0108575801, 30.4248761259, 32.9350615877]
    
    print("\nComparison with known Riemann zeros:")
    print(f"{'n':<5} {'Computed γ':<15} {'Target γ':<15} {'Error':<12}")
    print("-"*50)
    
    for i, z in enumerate(zeros[:5], 1):
        computed = float(z.imag)
        if i <= len(target_zeros):
            target = target_zeros[i-1]
            error = abs(computed - target)
            print(f"{i:<5} {computed:<15.6f} {target:<15.6f} {error:<12.6f}")
        else:
            print(f"{i:<5} {computed:<15.6f} {'N/A':<15} {'N/A':<12}")
    print()


def demo_theoretical_note():
    """Print note about theoretical parameters."""
    print("="*70)
    print("NOTE: Theoretical Parameters")
    print("="*70)
    print()
    print("The full theoretical implementation uses:")
    print("  N = 100 (Hermite basis functions)")
    print("  h = 0.0001 (thermal parameter)")
    print("  max_primes ~ 1000")
    print()
    print("These parameters provide the highest accuracy but require")
    print("significant computational resources:")
    print("  - Computation time: hours to days")
    print("  - Memory: several GB")
    print("  - High-precision arithmetic (mp.dps=500)")
    print()
    print("To run the full validation, execute:")
    print("  python adelic_spectral_ultima.py")
    print()
    print("Or in Python:")
    print("  from adelic_spectral_ultima import validatio_ultima")
    print("  zeros = validatio_ultima()")
    print()


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print("ADELIC SPECTRAL ULTIMA - DEMONSTRATION")
    print("="*70)
    print()
    
    # Demo 1: Small parameters
    demo_small_parameters()
    
    # Demo 2: Medium parameters
    demo_medium_parameters()
    
    # Theoretical note
    demo_theoretical_note()
    
    print("="*70)
    print("Demonstration complete!")
    print("="*70)
    print()


if __name__ == "__main__":
    main()
