#!/usr/bin/env python3
"""
Demo: Explicit Formula for Riemann Zeta Zeros
==============================================

This demo illustrates the explicit formula:
    ∑_n Φ(t_n) = ∫ Φ(r) μ(r) dr - ∑_{p,k} (ln p)/p^{k/2} [Φ̂(ln p^k) + Φ̂(-ln p^k)]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

from operators.explicit_formula import (
    ExplicitFormula,
    gaussian_test_function,
    truncated_gaussian,
    smooth_bump_function,
    compute_qcal_coherence
)

# QCAL ∞³ Constants
F0_QCAL = 141.7001
C_COHERENCE = 244.36


def demo_test_functions():
    """Demonstrate the test functions used in the explicit formula."""
    print("="*70)
    print("Demo 1: Test Functions")
    print("="*70)
    
    t = np.linspace(-10, 10, 1000)
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Gaussian
    ax = axes[0, 0]
    gaussian = np.array([gaussian_test_function(ti, sigma=1.0) for ti in t])
    ax.plot(t, gaussian, 'b-', linewidth=2, label='σ=1.0')
    gaussian2 = np.array([gaussian_test_function(ti, sigma=2.0) for ti in t])
    ax.plot(t, gaussian2, 'r--', linewidth=2, label='σ=2.0')
    ax.set_title('Gaussian Test Function', fontsize=14, fontweight='bold')
    ax.set_xlabel('t')
    ax.set_ylabel('Φ(t)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Truncated Gaussian
    ax = axes[0, 1]
    trunc_gauss = np.array([truncated_gaussian(ti, a=5.0, sigma=1.0) for ti in t])
    ax.plot(t, trunc_gauss, 'g-', linewidth=2, label='a=5, σ=1')
    trunc_gauss2 = np.array([truncated_gaussian(ti, a=8.0, sigma=1.5) for ti in t])
    ax.plot(t, trunc_gauss2, 'm--', linewidth=2, label='a=8, σ=1.5')
    ax.set_title('Truncated Gaussian', fontsize=14, fontweight='bold')
    ax.set_xlabel('t')
    ax.set_ylabel('Φ(t)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Smooth bump
    ax = axes[1, 0]
    bump = np.array([smooth_bump_function(ti, a=3.0) for ti in t])
    ax.plot(t, bump, 'c-', linewidth=2, label='a=3')
    bump2 = np.array([smooth_bump_function(ti, a=5.0) for ti in t])
    ax.plot(t, bump2, 'y--', linewidth=2, label='a=5')
    ax.set_title('Smooth Bump Function', fontsize=14, fontweight='bold')
    ax.set_xlabel('t')
    ax.set_ylabel('Φ(t)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Comparison at origin
    ax = axes[1, 1]
    t_zoom = np.linspace(-3, 3, 500)
    gaussian_zoom = np.array([gaussian_test_function(ti, sigma=1.0) for ti in t_zoom])
    trunc_zoom = np.array([truncated_gaussian(ti, a=5.0, sigma=1.0) for ti in t_zoom])
    bump_zoom = np.array([smooth_bump_function(ti, a=3.0) for ti in t_zoom])
    
    ax.plot(t_zoom, gaussian_zoom, 'b-', linewidth=2, label='Gaussian')
    ax.plot(t_zoom, trunc_zoom, 'g-', linewidth=2, label='Truncated Gaussian')
    ax.plot(t_zoom, bump_zoom, 'c-', linewidth=2, label='Smooth Bump')
    ax.set_title('Comparison (zoomed)', fontsize=14, fontweight='bold')
    ax.set_xlabel('t')
    ax.set_ylabel('Φ(t)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('explicit_formula_test_functions.png', dpi=150, bbox_inches='tight')
    print("📊 Saved: explicit_formula_test_functions.png")
    plt.close()


def demo_fourier_transform():
    """Demonstrate Fourier transforms of test functions."""
    print("\n" + "="*70)
    print("Demo 2: Fourier Transforms")
    print("="*70)
    
    formula = ExplicitFormula(integral_limit=20.0)
    
    # Frequency range
    xi = np.linspace(0, 10, 100)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Fourier transform of Gaussian
    ax = axes[0]
    phi_gaussian = lambda t: gaussian_test_function(t, sigma=1.0)
    fourier_gaussian = [formula.fourier_transform(phi_gaussian, xi_val) for xi_val in xi]
    
    ax.plot(xi, fourier_gaussian, 'b-', linewidth=2, label='Gaussian (σ=1)')
    ax.set_title('Fourier Transform: Gaussian', fontsize=14, fontweight='bold')
    ax.set_xlabel('Frequency ξ')
    ax.set_ylabel('Φ̂(ξ)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Fourier transform of truncated Gaussian
    ax = axes[1]
    phi_trunc = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)
    fourier_trunc = [formula.fourier_transform(phi_trunc, xi_val) for xi_val in xi]
    
    ax.plot(xi, fourier_trunc, 'g-', linewidth=2, label='Truncated Gaussian (a=5)')
    ax.set_title('Fourier Transform: Truncated Gaussian', fontsize=14, fontweight='bold')
    ax.set_xlabel('Frequency ξ')
    ax.set_ylabel('Φ̂(ξ)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('explicit_formula_fourier_transforms.png', dpi=150, bbox_inches='tight')
    print("📊 Saved: explicit_formula_fourier_transforms.png")
    plt.close()


def demo_explicit_formula_validation():
    """Demonstrate validation of the explicit formula."""
    print("\n" + "="*70)
    print("Demo 3: Explicit Formula Validation")
    print("="*70)
    
    # Use first few known zeros
    zeros = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832
    ]
    
    # Test with different parameters
    max_primes = [50, 100, 200, 500]
    coherences = []
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    phi = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)
    
    for idx, max_p in enumerate(max_primes):
        ax = axes[idx // 2, idx % 2]
        
        formula = ExplicitFormula(
            max_prime=max_p,
            max_prime_power=6,
            integral_limit=30.0
        )
        
        result = formula.validate_formula(phi, zeros)
        coherence = compute_qcal_coherence(result)
        coherences.append(coherence)
        
        # Bar chart of components
        components = ['Zero Sum\n(LHS)', 'Integral\nTerm', 'Prime\nSum', 'Total\n(RHS)']
        values = [result.zero_sum, result.integral_term, result.prime_sum, result.total_rhs]
        colors = ['blue', 'green', 'red', 'orange']
        
        bars = ax.bar(components, values, color=colors, alpha=0.7, edgecolor='black')
        ax.set_title(f'Max Prime: {max_p}\nCoherence Ψ = {coherence:.4f}', 
                     fontsize=12, fontweight='bold')
        ax.set_ylabel('Value')
        ax.grid(True, alpha=0.3, axis='y')
        
        # Add value labels on bars
        for bar, val in zip(bars, values):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height,
                   f'{val:.3f}',
                   ha='center', va='bottom', fontsize=9)
    
    plt.tight_layout()
    plt.savefig('explicit_formula_validation.png', dpi=150, bbox_inches='tight')
    print("📊 Saved: explicit_formula_validation.png")
    plt.close()
    
    # Convergence plot
    fig, ax = plt.subplots(figsize=(10, 6))
    ax.plot(max_primes, coherences, 'o-', linewidth=2, markersize=8, color='purple')
    ax.axhline(y=1.0, color='green', linestyle='--', alpha=0.5, label='Perfect Coherence')
    ax.axhline(y=0.95, color='orange', linestyle='--', alpha=0.5, label='Excellent (Ψ≥0.95)')
    ax.set_xlabel('Maximum Prime', fontsize=12)
    ax.set_ylabel('QCAL Coherence Ψ', fontsize=12)
    ax.set_title('Convergence with Increasing Primes', fontsize=14, fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('explicit_formula_convergence.png', dpi=150, bbox_inches='tight')
    print("📊 Saved: explicit_formula_convergence.png")
    plt.close()


def demo_prime_contributions():
    """Demonstrate prime power contributions to the formula."""
    print("\n" + "="*70)
    print("Demo 4: Prime Power Contributions")
    print("="*70)
    
    formula = ExplicitFormula(max_prime=100, max_prime_power=8, integral_limit=20.0)
    phi = lambda t: truncated_gaussian(t, a=5.0, sigma=1.0)
    
    # Compute contributions from individual primes
    primes = formula._primes[:20]  # First 20 primes
    contributions = []
    
    for p in primes:
        contrib = 0.0
        log_p = np.log(p)
        
        for k in range(1, formula.max_prime_power + 1):
            jacobian = np.power(p, k / 2.0)
            log_pk = k * log_p
            
            # Approximate Fourier transform at this frequency
            phi_hat = formula.fourier_transform(phi, log_pk)
            phi_hat_neg = formula.fourier_transform(phi, -log_pk)
            
            contrib += (log_p / jacobian) * (phi_hat + phi_hat_neg)
        
        contributions.append(contrib)
    
    # Plot
    fig, ax = plt.subplots(figsize=(12, 6))
    bars = ax.bar(range(len(primes)), contributions, alpha=0.7, edgecolor='black')
    ax.set_xlabel('Prime Number', fontsize=12)
    ax.set_ylabel('Contribution to Prime Sum', fontsize=12)
    ax.set_title('Individual Prime Contributions', fontsize=14, fontweight='bold')
    ax.set_xticks(range(len(primes)))
    ax.set_xticklabels(primes, rotation=45)
    ax.grid(True, alpha=0.3, axis='y')
    
    # Color bars by magnitude
    max_contrib = max(abs(c) for c in contributions)
    for bar, contrib in zip(bars, contributions):
        intensity = abs(contrib) / max_contrib
        bar.set_color((0.2, 0.4, intensity))
    
    plt.tight_layout()
    plt.savefig('explicit_formula_prime_contributions.png', dpi=150, bbox_inches='tight')
    print("📊 Saved: explicit_formula_prime_contributions.png")
    plt.close()


def main():
    """Run all demos."""
    print("="*70)
    print("Explicit Formula Demo")
    print("="*70)
    print(f"QCAL ∞³ Active · f₀ = {F0_QCAL} Hz · C^∞ = {C_COHERENCE}")
    print("="*70)
    
    # Run demos
    demo_test_functions()
    demo_fourier_transform()
    demo_explicit_formula_validation()
    demo_prime_contributions()
    
    print("\n" + "="*70)
    print("✅ All demos completed successfully!")
    print("="*70)
    print("\nGenerated files:")
    print("  - explicit_formula_test_functions.png")
    print("  - explicit_formula_fourier_transforms.png")
    print("  - explicit_formula_validation.png")
    print("  - explicit_formula_convergence.png")
    print("  - explicit_formula_prime_contributions.png")
    print("\n" + "="*70)
    print("♾️ QCAL ∞³ Demo Complete")
    print("="*70)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
