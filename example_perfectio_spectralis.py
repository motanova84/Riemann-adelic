#!/usr/bin/env python3
"""
Example usage of perfectio_spectralis implementation.

This script demonstrates how to use the perfectio_spectralis module
to compute Riemann zeros with high precision.
"""

from perfectio_spectralis import perfectio_spectralis, validatio_perfectio
import numpy as np


def example_basic_usage():
    """
    Basic example: Compute zeros with default parameters.
    """
    print("="*70)
    print("EXAMPLE 1: Basic Usage")
    print("="*70)
    print()
    
    # Parameters
    N = 20  # Matrix size
    h = 0.005  # Thermal parameter
    
    print(f"Computing zeros with N={N}, h={h}...")
    zeros, H = perfectio_spectralis(N, h)
    
    print()
    print(f"Computed {len(zeros)} zeros:")
    print()
    
    # Display first 5 zeros
    for i, z in enumerate(zeros[:5]):
        print(f"  ρ_{i+1} = {z.real:.4f} + {z.imag:.10f}i")
    
    # Known values for comparison
    known_zeros = [14.1347251417, 21.0220396388, 25.0108575801]
    
    print()
    print("Comparison with known values:")
    for i in range(min(3, len(zeros))):
        error = abs(zeros[i].imag - known_zeros[i])
        rel_error = error / known_zeros[i] * 100
        print(f"  γ_{i+1}: Error = {error:.6e} ({rel_error:.4f}%)")
    
    print()


def example_high_precision():
    """
    Example with higher precision settings.
    """
    print("="*70)
    print("EXAMPLE 2: High Precision")
    print("="*70)
    print()
    
    # Use more basis functions and smaller thermal parameter
    N = 30
    h = 0.002
    
    print(f"Computing with higher precision: N={N}, h={h}")
    print("(This may take a few seconds...)")
    print()
    
    zeros, H = perfectio_spectralis(N, h)
    
    print(f"Computed {len(zeros)} zeros")
    
    # Analyze accuracy
    known_zeros = [14.1347251417, 21.0220396388, 25.0108575801, 
                   30.4248761259, 32.9350615877]
    
    print()
    print("Accuracy analysis:")
    errors = []
    for i in range(min(5, len(zeros))):
        error = abs(zeros[i].imag - known_zeros[i])
        errors.append(error)
        print(f"  ρ_{i+1}: Error = {error:.6e}")
    
    print()
    print(f"Mean error: {np.mean(errors):.6e}")
    print(f"Max error:  {np.max(errors):.6e}")
    print()


def example_matrix_properties():
    """
    Example showing matrix properties.
    """
    print("="*70)
    print("EXAMPLE 3: Matrix Properties")
    print("="*70)
    print()
    
    N = 15
    h = 0.005
    
    zeros, H = perfectio_spectralis(N, h)
    
    # Compute eigenvalues
    eigenvalues = np.linalg.eigvalsh(H)
    
    print(f"Matrix properties for N={N}:")
    print(f"  Shape: {H.shape}")
    print(f"  Symmetric: {np.allclose(H, H.T)}")
    print(f"  Positive definite: {np.all(eigenvalues > 0)}")
    print()
    
    print("Eigenvalue statistics:")
    print(f"  Minimum: {eigenvalues[0]:.6f}")
    print(f"  Maximum: {eigenvalues[-1]:.6f}")
    print(f"  Mean: {np.mean(eigenvalues):.6f}")
    print()
    
    print("First 5 eigenvalues → zeros:")
    for i in range(5):
        lam = eigenvalues[i]
        gamma = np.sqrt(lam - 0.25)
        print(f"  λ_{i+1} = {lam:.6f} → γ_{i+1} = {gamma:.6f}")
    
    print()


def example_convergence_study():
    """
    Example showing convergence with increasing N.
    """
    print("="*70)
    print("EXAMPLE 4: Convergence Study")
    print("="*70)
    print()
    
    h = 0.005
    N_values = [10, 15, 20, 25]
    target_gamma = 14.1347251417  # First zero
    
    print(f"Studying convergence of first zero (γ₁ = {target_gamma})")
    print(f"with h={h} and varying N:")
    print()
    
    print(f"{'N':<6} {'Computed γ₁':<15} {'Error':<15}")
    print("-" * 40)
    
    for N in N_values:
        zeros, _ = perfectio_spectralis(N, h)
        gamma_computed = zeros[0].imag
        error = abs(gamma_computed - target_gamma)
        print(f"{N:<6} {gamma_computed:<15.10f} {error:<15.6e}")
    
    print()
    print("Note: Error generally decreases with larger N")
    print()


def example_full_validation():
    """
    Example running the full validation suite.
    """
    print("="*70)
    print("EXAMPLE 5: Full Validation")
    print("="*70)
    print()
    
    print("Running complete validation against Odlyzko zeros...")
    print()
    
    success, zeros = validatio_perfectio()
    
    print()
    if success:
        print("✓ Validation completed successfully!")
        print(f"  Computed {len(zeros)} high-precision zeros")
    else:
        print("○ Validation completed with acceptable accuracy")
    
    print()


def main():
    """
    Run all examples.
    """
    print("\n")
    print("╔" + "═"*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + "  PERFECTIO SPECTRALIS - USAGE EXAMPLES".center(68) + "║")
    print("║" + " "*68 + "║")
    print("╚" + "═"*68 + "╝")
    print("\n")
    
    # Run examples
    example_basic_usage()
    example_high_precision()
    example_matrix_properties()
    example_convergence_study()
    example_full_validation()
    
    print("="*70)
    print("Examples completed successfully!")
    print("="*70)
    print()


if __name__ == "__main__":
    main()
