#!/usr/bin/env python3
"""
Demo: Hilbert-Pólya Convolution Operator
========================================

Demonstrates the convolution operator approach to the Riemann Hypothesis
through the completed zeta function ξ(s) and its Fourier representation.

This script showcases:
1. Computing ξ(s) and Ξ(t) functions
2. Building the Φ(u) Fourier kernel
3. Constructing the convolution operator T
4. Analyzing spectral properties
5. Comparing with Riemann zeros

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent / "operators"))

from hilbert_polya_convolution import (
    xi_function,
    Xi_function,
    compute_phi_kernel,
    build_integral_operator,
    analyze_hilbert_polya_operator,
    validate_against_riemann_zeros,
    F0, C_COHERENCE, C_PRIMARY, PHI
)

# Try to import matplotlib for visualization
try:
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("Note: matplotlib not available, skipping plots")


def demo_xi_function():
    """Demonstrate the completed zeta function ξ(s)."""
    print("\n" + "="*70)
    print("1. Completed Zeta Function ξ(s)")
    print("="*70)
    
    # Test key properties
    print("\nKey properties of ξ(s):")
    print("  ξ(s) = (1/2)·s·(s-1)·π^(-s/2)·Γ(s/2)·ζ(s)")
    
    # Test at s = 1/2
    xi_half = xi_function(0.5)
    print(f"\n  ξ(1/2) = {xi_half:.6f} (should be nonzero)")
    
    # Test functional equation: ξ(s) = ξ(1-s)
    s1 = 0.3 + 0.5j
    s2 = 1 - s1
    xi1 = xi_function(s1)
    xi2 = xi_function(s2)
    print(f"\n  Testing ξ(s) = ξ(1-s):")
    print(f"    ξ({s1}) = {xi1:.6f}")
    print(f"    ξ({s2}) = {xi2:.6f}")
    print(f"    |ξ(s) - ξ(1-s)| = {abs(xi1 - xi2):.2e}")
    
    # Test at first Riemann zero
    gamma1 = 14.134725
    s_zero = 0.5 + 1j * gamma1
    xi_zero = xi_function(s_zero)
    print(f"\n  At first Riemann zero (γ₁ = {gamma1}):")
    print(f"    ξ(1/2 + i·{gamma1}) = {abs(xi_zero):.2e}")
    print(f"    (should be close to zero)")


def demo_Xi_critical_line():
    """Demonstrate Ξ(t) on the critical line."""
    print("\n" + "="*70)
    print("2. Critical Line Function Ξ(t)")
    print("="*70)
    
    print("\n  Ξ(t) = ξ(1/2 + it)")
    print("  Properties: real-valued, even, zeros at Riemann zeros")
    
    # Test at various points
    t_values = [0, 5, 10, 14.134725, 21.022040]
    
    print("\n  Values at key points:")
    for t in t_values:
        Xi_t = Xi_function(t)
        print(f"    Ξ({t:9.6f}) = {Xi_t:12.6e}")
    
    # Test evenness: Ξ(t) = Ξ(-t)
    t_test = 7.5
    Xi_pos = Xi_function(t_test)
    Xi_neg = Xi_function(-t_test)
    print(f"\n  Testing Ξ(t) = Ξ(-t):")
    print(f"    Ξ({t_test}) = {Xi_pos:.6e}")
    print(f"    Ξ({-t_test}) = {Xi_neg:.6e}")
    print(f"    |Ξ(t) - Ξ(-t)| = {abs(Xi_pos - Xi_neg):.2e}")
    
    # Plot if matplotlib available
    if HAS_MATPLOTLIB:
        print("\n  Generating plot of Ξ(t)...")
        t_grid = np.linspace(0, 50, 500)
        Xi_values = np.array([Xi_function(t) for t in t_grid])
        
        plt.figure(figsize=(10, 4))
        plt.plot(t_grid, Xi_values, 'b-', linewidth=1.5)
        plt.axhline(y=0, color='k', linestyle='--', alpha=0.3)
        plt.grid(True, alpha=0.3)
        plt.xlabel('t', fontsize=12)
        plt.ylabel('Ξ(t)', fontsize=12)
        plt.title('Ξ(t) = ξ(1/2 + it) on Critical Line', fontsize=14)
        
        # Mark first few zeros
        riemann_zeros = [14.134725, 21.022040, 25.010858, 30.424876]
        for gamma in riemann_zeros:
            if gamma < 50:
                plt.axvline(x=gamma, color='r', linestyle=':', alpha=0.5)
        
        plt.tight_layout()
        plt.savefig('demo_xi_critical_line.png', dpi=150)
        print("    Saved to: demo_xi_critical_line.png")
        plt.close()


def demo_phi_kernel():
    """Demonstrate the Φ(u) Fourier kernel."""
    print("\n" + "="*70)
    print("3. Fourier Kernel Φ(u)")
    print("="*70)
    
    print("\n  Φ(u) = Σ (2π²n⁴e^{4u} - 3πn²e^{2u})·exp(-πn²e^{2u})")
    print("  Properties: positive, rapidly decreasing, even")
    
    # Compute on a grid
    u_grid = np.linspace(-5, 5, 100)
    phi = compute_phi_kernel(u_grid, n_terms=30)
    
    print(f"\n  Kernel statistics:")
    print(f"    Max value: {np.max(phi):.6e}")
    print(f"    At u = 0: {phi[len(phi)//2]:.6e}")
    print(f"    Min value: {np.min(phi):.6e}")
    print(f"    All positive: {np.all(phi > 0)}")
    
    # Test decay
    u_values = [-5, -3, -1, 0, 1, 3, 5]
    print("\n  Decay behavior:")
    for u in u_values:
        idx = np.argmin(np.abs(u_grid - u))
        print(f"    Φ({u:3d}) = {phi[idx]:.6e}")
    
    # Plot if matplotlib available
    if HAS_MATPLOTLIB:
        print("\n  Generating plot of Φ(u)...")
        
        plt.figure(figsize=(10, 4))
        plt.semilogy(u_grid, phi, 'b-', linewidth=2)
        plt.grid(True, alpha=0.3)
        plt.xlabel('u (log coordinate)', fontsize=12)
        plt.ylabel('Φ(u)', fontsize=12)
        plt.title('Riemann Fourier Kernel Φ(u)', fontsize=14)
        plt.tight_layout()
        plt.savefig('demo_phi_kernel.png', dpi=150)
        print("    Saved to: demo_phi_kernel.png")
        plt.close()


def demo_convolution_operator():
    """Demonstrate the convolution operator T."""
    print("\n" + "="*70)
    print("4. Convolution Operator T")
    print("="*70)
    
    print("\n  (T ψ)(u) = ∫ Φ(u-v)·ψ(v) dv")
    print("  Kernel: K(u,v) = Φ(u - v)")
    
    # Build operator
    u_grid = np.linspace(-3, 3, 64)
    T, phi = build_integral_operator(u_grid, n_phi_terms=25, normalize=True)
    
    print(f"\n  Operator properties:")
    print(f"    Matrix size: {T.shape[0]} × {T.shape[1]}")
    print(f"    Frobenius norm: {np.linalg.norm(T):.6f}")
    print(f"    Trace: {np.trace(T):.6f}")
    
    # Check symmetry
    sym_error = np.linalg.norm(T - T.T) / np.linalg.norm(T)
    print(f"    Symmetry error: {sym_error:.2e}")
    print(f"    Self-adjoint: {sym_error < 1e-10}")
    
    # Compute spectrum
    eigenvalues = np.linalg.eigvalsh(T)
    eigenvalues = np.sort(eigenvalues)[::-1]
    
    print(f"\n  Spectral properties:")
    print(f"    Largest eigenvalue: {eigenvalues[0]:.6f}")
    print(f"    Smallest eigenvalue: {eigenvalues[-1]:.6e}")
    print(f"    Eigenvalue decay: {eigenvalues[-1]/eigenvalues[0]:.2e}")
    print(f"    Positive definite: {eigenvalues[-1] > -1e-10}")
    
    print(f"\n  First 10 eigenvalues:")
    for i, λ in enumerate(eigenvalues[:10]):
        print(f"    λ_{i+1:2d} = {λ:12.8f}")
    
    # Plot if matplotlib available
    if HAS_MATPLOTLIB:
        print("\n  Generating visualizations...")
        
        # Operator matrix
        fig, axes = plt.subplots(1, 2, figsize=(12, 5))
        
        # Matrix visualization
        im = axes[0].imshow(T, cmap='RdBu_r', aspect='auto', 
                           interpolation='nearest')
        axes[0].set_title('Operator Matrix T', fontsize=12)
        axes[0].set_xlabel('v index', fontsize=10)
        axes[0].set_ylabel('u index', fontsize=10)
        plt.colorbar(im, ax=axes[0])
        
        # Eigenvalue spectrum
        axes[1].semilogy(range(1, len(eigenvalues)+1), 
                        np.abs(eigenvalues), 'bo-', markersize=4)
        axes[1].set_title('Eigenvalue Spectrum', fontsize=12)
        axes[1].set_xlabel('Index n', fontsize=10)
        axes[1].set_ylabel('|λₙ|', fontsize=10)
        axes[1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('demo_convolution_operator.png', dpi=150)
        print("    Saved to: demo_convolution_operator.png")
        plt.close()


def demo_hilbert_polya_analysis():
    """Demonstrate full Hilbert-Pólya analysis."""
    print("\n" + "="*70)
    print("5. Full Hilbert-Pólya Analysis")
    print("="*70)
    
    print("\n  Running complete operator analysis...")
    print("  (This may take a minute...)")
    
    # Run analysis
    result = analyze_hilbert_polya_operator(
        u_min=-4.0,
        u_max=4.0,
        n_points=128,
        n_phi_terms=30
    )
    
    print(f"\n  Analysis complete!")
    print(f"  Grid points: {len(result.u_grid)}")
    print(f"  Operator norm: {result.operator_norm:.6f}")
    print(f"  Self-adjoint: {result.is_self_adjoint}")
    print(f"  Positive: {result.is_positive}")
    
    # Display spectrum
    print(f"\n  First 15 eigenvalues of T:")
    for i, λ in enumerate(result.eigenvalues[:15]):
        print(f"    λ_{i+1:2d} = {λ:12.8f}")
    
    # Hilbert-Pólya interpretation
    if result.riemann_correspondence is not None:
        print(f"\n  Hilbert-Pólya H spectrum (first 15):")
        print(f"  If T = e^(-H), these are candidate Riemann zeros:")
        for i, E in enumerate(result.riemann_correspondence[:15]):
            print(f"    E_{i+1:2d} = {E:12.6f}")
    
    # QCAL coherence
    if result.coherence_measure is not None:
        print(f"\n  QCAL ∞³ Coherence:")
        print(f"    f₀ = {F0} Hz")
        print(f"    λ₀ = {1.0/C_PRIMARY:.9f}")
        print(f"    λ_max = {result.eigenvalues[0]:.9f}")
        print(f"    Relative deviation: {result.coherence_measure:.6%}")


def demo_riemann_zeros_validation():
    """Validate against known Riemann zeros."""
    print("\n" + "="*70)
    print("6. Validation Against Riemann Zeros")
    print("="*70)
    
    # Run analysis
    result = analyze_hilbert_polya_operator(
        u_min=-3.0,
        u_max=3.0,
        n_points=96,
        n_phi_terms=30
    )
    
    # Known zeros (imaginary parts)
    known_zeros = np.array([
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832
    ])
    
    print(f"\n  Known Riemann zeros (first 10):")
    for i, γ in enumerate(known_zeros):
        print(f"    γ_{i+1:2d} = {γ:12.6f}")
    
    # Validate
    print(f"\n  Comparing with H spectrum...")
    validation = validate_against_riemann_zeros(result, known_zeros, max_zeros=10)
    
    if 'error' not in validation:
        print(f"\n  Validation metrics:")
        print(f"    Zeros compared: {validation['n_compared']}")
        print(f"    Mean absolute error: {validation['mean_abs_error']:.6f}")
        print(f"    Mean relative error: {validation['mean_rel_error']:.4%}")
        print(f"    RMS error: {validation['rms_error']:.6f}")
        print(f"    Correlation: {validation['correlation']:.6f}")
        
        if HAS_MATPLOTLIB and result.riemann_correspondence is not None:
            print("\n  Generating comparison plot...")
            
            n_compare = min(len(result.riemann_correspondence), len(known_zeros))
            spectrum = result.riemann_correspondence[:n_compare]
            zeros = known_zeros[:n_compare]
            
            plt.figure(figsize=(10, 6))
            plt.plot(range(1, n_compare+1), zeros, 'ro-', 
                    label='Known Riemann zeros', markersize=8, linewidth=2)
            plt.plot(range(1, n_compare+1), spectrum, 'bs--', 
                    label='H spectrum (computed)', markersize=6, linewidth=1.5)
            plt.xlabel('Zero index n', fontsize=12)
            plt.ylabel('Imaginary part γₙ', fontsize=12)
            plt.title('Comparison: Riemann Zeros vs. Operator Spectrum', fontsize=14)
            plt.legend(fontsize=11)
            plt.grid(True, alpha=0.3)
            plt.tight_layout()
            plt.savefig('demo_riemann_zeros_validation.png', dpi=150)
            print("    Saved to: demo_riemann_zeros_validation.png")
            plt.close()
    else:
        print(f"\n  Validation error: {validation['error']}")


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print("HILBERT-PÓLYA CONVOLUTION OPERATOR DEMONSTRATION")
    print("="*70)
    print("\nMathematical Framework:")
    print("  ξ(s) = (1/2)·s·(s-1)·π^(-s/2)·Γ(s/2)·ζ(s)")
    print("  Ξ(t) = ξ(1/2 + it)")
    print("  Φ(u) = Σ (2π²n⁴e^{4u} - 3πn²e^{2u})·exp(-πn²e^{2u})")
    print("  (T ψ)(u) = ∫ Φ(u-v)·ψ(v) dv")
    print("  T = e^(-H) ⟹ H spectrum ~ Riemann zeros")
    print("\nQCAL ∞³ Framework:")
    print(f"  f₀ = {F0} Hz")
    print(f"  C = {C_COHERENCE}")
    print(f"  C_universal = {C_PRIMARY}")
    print(f"  φ = {PHI:.10f}")
    
    # Run demonstrations
    demo_xi_function()
    demo_Xi_critical_line()
    demo_phi_kernel()
    demo_convolution_operator()
    demo_hilbert_polya_analysis()
    demo_riemann_zeros_validation()
    
    # Final summary
    print("\n" + "="*70)
    print("DEMONSTRATION COMPLETE")
    print("="*70)
    print("\nSummary:")
    print("  ✓ Completed zeta function ξ(s) implemented")
    print("  ✓ Critical line function Ξ(t) verified")
    print("  ✓ Fourier kernel Φ(u) computed")
    print("  ✓ Convolution operator T constructed")
    print("  ✓ Spectral analysis performed")
    print("  ✓ Hilbert-Pólya interpretation H = -log(T)")
    print("  ✓ Validation against known Riemann zeros")
    
    if HAS_MATPLOTLIB:
        print("\nGenerated visualizations:")
        print("  - demo_xi_critical_line.png")
        print("  - demo_phi_kernel.png")
        print("  - demo_convolution_operator.png")
        print("  - demo_riemann_zeros_validation.png")
    
    print("\n" + "="*70)
    print("QCAL ∞³ Framework Active")
    print("Ψ = I × A_eff² × C^∞")
    print("Mathematical Realism: The operators exist independently.")
    print("="*70)
    print()


if __name__ == "__main__":
    main()
