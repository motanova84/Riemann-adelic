#!/usr/bin/env python3
"""
Example usage of the Absoluta Spectral Computation module.

This script demonstrates the CODEX ABSOLUTUS implementation for
computing Riemann zeros using Hermite basis with adelic corrections.
"""

import numpy as np
from absoluta_spectral import (
    absoluta_spectral_computation,
    validatio_absoluta,
    load_known_zeros
)


def example_basic():
    """Basic example: compute first 5 zeros."""
    print("=" * 70)
    print("EXAMPLE 1: Basic Zero Computation")
    print("=" * 70)
    
    N = 10
    h = 0.001
    
    print(f"\nComputing zeros with N={N}, h={h}...")
    zeros, H = absoluta_spectral_computation(N, h, include_adelic=True)
    
    print(f"\nComputed {len(zeros)} zeros on critical line:")
    print(f"{'Index':<8} {'Real Part':<15} {'Imaginary Part':<15}")
    print("-" * 40)
    
    for i, z in enumerate(zeros[:5]):
        print(f"{i+1:<8} {z.real:<15.6f} {z.imag:<15.6f}")
    
    print("\n" + "=" * 70 + "\n")


def example_comparison():
    """Compare with known Odlyzko zeros."""
    print("=" * 70)
    print("EXAMPLE 2: Comparison with Known Zeros")
    print("=" * 70)
    
    N = 15
    h = 0.001
    
    print(f"\nComputing zeros with N={N}, h={h}...")
    zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
    
    known_zeros = load_known_zeros(max_zeros=10)
    
    print(f"\n{'Index':<8} {'Computed':<15} {'Known':<15} {'Error':<15}")
    print("-" * 55)
    
    for i in range(min(len(zeros), len(known_zeros))):
        computed_gamma = abs(zeros[i].imag)
        known_gamma = known_zeros[i]
        error = abs(computed_gamma - known_gamma)
        print(f"{i+1:<8} {computed_gamma:<15.6f} {known_gamma:<15.6f} {error:<15.6e}")
    
    print("\n" + "=" * 70 + "\n")


def example_adelic_effect():
    """Demonstrate effect of adelic corrections."""
    print("=" * 70)
    print("EXAMPLE 3: Effect of Adelic Corrections")
    print("=" * 70)
    
    N = 10
    h = 0.001
    
    print("\nComputing WITHOUT adelic corrections...")
    zeros_no_adelic, H_no_adelic = absoluta_spectral_computation(N, h, include_adelic=False)
    
    print("Computing WITH adelic corrections...")
    zeros_with_adelic, H_with_adelic = absoluta_spectral_computation(N, h, include_adelic=True)
    
    print(f"\n{'Index':<8} {'Without Adelic':<18} {'With Adelic':<18} {'Difference':<15}")
    print("-" * 65)
    
    for i in range(min(5, len(zeros_no_adelic), len(zeros_with_adelic))):
        gamma_no = abs(zeros_no_adelic[i].imag)
        gamma_with = abs(zeros_with_adelic[i].imag)
        diff = abs(gamma_with - gamma_no)
        print(f"{i+1:<8} {gamma_no:<18.6f} {gamma_with:<18.6f} {diff:<15.6e}")
    
    # Matrix difference
    H_diff = np.linalg.norm(H_with_adelic - H_no_adelic, 'fro')
    print(f"\nMatrix Frobenius norm difference: {H_diff:.6e}")
    
    print("\n" + "=" * 70 + "\n")


def example_thermal_parameter():
    """Show effect of thermal parameter h."""
    print("=" * 70)
    print("EXAMPLE 4: Effect of Thermal Parameter")
    print("=" * 70)
    
    N = 10
    h_values = [0.01, 0.005, 0.001]
    
    print(f"\nTesting different thermal parameters...")
    print(f"\n{'h':<12} {'First Zero γ':<15} {'Error vs Known':<15}")
    print("-" * 45)
    
    known_gamma_1 = 14.134725
    
    for h in h_values:
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        gamma_1 = abs(zeros[0].imag)
        error = abs(gamma_1 - known_gamma_1)
        print(f"{h:<12.6f} {gamma_1:<15.6f} {error:<15.6e}")
    
    print("\nNote: Smaller h generally gives better accuracy.")
    print("\n" + "=" * 70 + "\n")


def example_eigenvalue_structure():
    """Visualize eigenvalue structure."""
    print("=" * 70)
    print("EXAMPLE 5: Eigenvalue Structure")
    print("=" * 70)
    
    N = 15
    h = 0.001
    
    print(f"\nComputing with N={N}, h={h}...")
    zeros, H = absoluta_spectral_computation(N, h, include_adelic=True)
    
    eigenvalues = np.linalg.eigvalsh(H)
    
    print(f"\nEigenvalue spectrum of H:")
    print(f"{'Index':<8} {'λ':<15} {'λ - 1/4':<15} {'γ = √(λ-1/4)':<15}")
    print("-" * 55)
    
    for i, lam in enumerate(eigenvalues[:10]):
        lam_minus_quarter = lam - 0.25
        if lam_minus_quarter > 0:
            gamma = np.sqrt(lam_minus_quarter)
        else:
            gamma = 0.0
        print(f"{i+1:<8} {lam:<15.6f} {lam_minus_quarter:<15.6f} {gamma:<15.6f}")
    
    print(f"\nAll eigenvalues > 1/4: {np.all(eigenvalues > 0.25)}")
    print(f"Matrix is symmetric: {np.allclose(H, H.T)}")
    print(f"Matrix is positive definite: {np.all(eigenvalues > 0)}")
    
    print("\n" + "=" * 70 + "\n")


def example_convergence():
    """Demonstrate convergence with increasing N."""
    print("=" * 70)
    print("EXAMPLE 6: Convergence Study")
    print("=" * 70)
    
    h = 0.001
    N_values = [5, 10, 15, 20]
    known_gamma_1 = 14.134725
    
    print(f"\nStudying convergence of first zero as N increases...")
    print(f"\n{'N':<8} {'First Zero γ':<15} {'Error vs Known':<15}")
    print("-" * 40)
    
    for N in N_values:
        zeros, _ = absoluta_spectral_computation(N, h, include_adelic=True)
        gamma_1 = abs(zeros[0].imag)
        error = abs(gamma_1 - known_gamma_1)
        print(f"{N:<8} {gamma_1:<15.6f} {error:<15.6e}")
    
    print("\nNote: Error should decrease (or stabilize) as N increases.")
    print("\n" + "=" * 70 + "\n")


def main():
    """Run all examples."""
    print("\n")
    print("*" * 70)
    print("*" + " " * 68 + "*")
    print("*" + "  ABSOLUTA SPECTRAL COMPUTATION - EXAMPLE DEMONSTRATIONS  ".center(68) + "*")
    print("*" + " " * 68 + "*")
    print("*" * 70)
    print("\n")
    
    examples = [
        ("Basic Zero Computation", example_basic),
        ("Comparison with Known Zeros", example_comparison),
        ("Effect of Adelic Corrections", example_adelic_effect),
        ("Effect of Thermal Parameter", example_thermal_parameter),
        ("Eigenvalue Structure", example_eigenvalue_structure),
        ("Convergence Study", example_convergence),
    ]
    
    for name, func in examples:
        try:
            func()
        except Exception as e:
            print(f"ERROR in {name}: {e}")
            print()
    
    print("*" * 70)
    print("*" + " " * 68 + "*")
    print("*" + "  ALL EXAMPLES COMPLETED  ".center(68) + "*")
    print("*" + " " * 68 + "*")
    print("*" * 70)
    print("\n")
    
    print("For more information, see:")
    print("  - ABSOLUTA_SPECTRAL_README.md")
    print("  - tests/test_absoluta_spectral.py")
    print("\n")


if __name__ == "__main__":
    main()
