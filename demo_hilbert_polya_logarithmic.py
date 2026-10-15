#!/usr/bin/env python3
"""
Demonstration of Hilbert-Pólya Logarithmic Operator
===================================================

This script demonstrates the complete Hilbert-Pólya operator with
visualizations and analysis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path

import numpy as np

# Add operators to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from hilbert_polya_logarithmic import (
    F0_QCAL,
    C_COHERENCE,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    LogarithmicHilbertSpace,
    HyperbolicDilationOperator,
    ArithmeticPotentialOperator,
    HilbertPolyaOperator,
    demonstrate_hilbert_polya,
    verificar_geometria_logaritmica,
    activar_hilbert_polya,
)

try:
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("Warning: matplotlib not available, skipping plots")


def demo_1_logarithmic_space():
    """Demonstrate logarithmic Hilbert space with scale symmetry"""
    print("=" * 80)
    print("DEMO 1: Logarithmic Hilbert Space L²(ℝ, du)")
    print("=" * 80)
    print()
    
    space = LogarithmicHilbertSpace(n_points=256, u_max=10.0)
    result = space.compute()
    
    print(f"Grid points: {space.n_points}")
    print(f"Range: u ∈ [-{space.u_max}, {space.u_max}]")
    print(f"Grid spacing: du = {space.du:.6f}")
    print()
    print(f"Symmetry error: {result.symmetry_error:.2e}")
    print(f"L² norm: {result.l2_norm:.6f}")
    print(f"Coherence Ψ: {result.psi:.6f}")
    print()
    
    if HAS_MATPLOTLIB:
        fig, axes = plt.subplots(1, 2, figsize=(12, 4))
        
        # Plot wavefunction
        axes[0].plot(result.u_grid, np.real(result.psi_even), 'b-', linewidth=2)
        axes[0].axvline(0, color='r', linestyle='--', alpha=0.5, label='u=0 (Nodo Zero)')
        axes[0].set_xlabel('u = ln(x)')
        axes[0].set_ylabel('ψ(u)')
        axes[0].set_title('Even Wavefunction in Log Space')
        axes[0].grid(True, alpha=0.3)
        axes[0].legend()
        
        # Plot symmetry check
        psi_rev = result.psi_even[::-1]
        axes[1].plot(result.u_grid, np.real(result.psi_even), 'b-', label='ψ(u)', linewidth=2)
        axes[1].plot(result.u_grid, np.real(psi_rev), 'r--', label='ψ(-u)', linewidth=2, alpha=0.7)
        axes[1].set_xlabel('u = ln(x)')
        axes[1].set_ylabel('ψ(u)')
        axes[1].set_title('Scale-Inversion Symmetry Check')
        axes[1].grid(True, alpha=0.3)
        axes[1].legend()
        
        plt.tight_layout()
        plt.savefig('demo_hilbert_polya_log_space.png', dpi=150)
        print("Saved: demo_hilbert_polya_log_space.png")
        plt.close()
    
    print()
    return result


def demo_2_dilation_operator():
    """Demonstrate hyperbolic dilation operator"""
    print("=" * 80)
    print("DEMO 2: Hyperbolic Dilation Operator H₀")
    print("=" * 80)
    print()
    
    op = HyperbolicDilationOperator(n_points=256, u_max=10.0)
    result = op.compute()
    
    print("Operator: H₀ = -i(d/du + (1/2)tanh(u))")
    print()
    print(f"Hermiticity error: {result.hermiticity_error:.2e}")
    print(f"Tanh correction norm: {result.tanh_correction_norm:.6f}")
    print(f"Coherence Ψ: {result.psi:.6f}")
    print()
    print(f"Eigenvalue range: [{result.eigenvalues[0]:.4f}, {result.eigenvalues[-1]:.4f}]")
    print(f"Number of eigenvalues: {len(result.eigenvalues)}")
    print()
    
    if HAS_MATPLOTLIB:
        fig, axes = plt.subplots(1, 2, figsize=(12, 4))
        
        # Plot tanh correction
        tanh_corr = 0.5 * np.tanh(op.u_grid)
        axes[0].plot(op.u_grid, tanh_corr, 'g-', linewidth=2)
        axes[0].axvline(0, color='r', linestyle='--', alpha=0.5)
        axes[0].axhline(0, color='k', linestyle='-', alpha=0.3)
        axes[0].set_xlabel('u')
        axes[0].set_ylabel('(1/2) tanh(u)')
        axes[0].set_title('Hyperbolic Curvature Correction')
        axes[0].grid(True, alpha=0.3)
        
        # Plot eigenvalue spectrum
        axes[1].plot(result.eigenvalues, 'b.', markersize=4)
        axes[1].set_xlabel('Index')
        axes[1].set_ylabel('Eigenvalue')
        axes[1].set_title('Dilation Operator Spectrum')
        axes[1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('demo_hilbert_polya_dilation.png', dpi=150)
        print("Saved: demo_hilbert_polya_dilation.png")
        plt.close()
    
    print()
    return result


def demo_3_arithmetic_potential():
    """Demonstrate arithmetic potential"""
    print("=" * 80)
    print("DEMO 3: Arithmetic Potential V(u)")
    print("=" * 80)
    print()
    
    op = ArithmeticPotentialOperator(n_points=256, u_max=10.0, n_primes=30)
    result = op.compute()
    
    print("Potential: V(u) = Σₚ (log p / √p) cos(u log p)")
    print()
    print(f"Number of primes: {op.n_primes}")
    print(f"Prime range: {op.primes[0]} to {op.primes[-1]}")
    print(f"Evenness error: {result.evenness_error:.2e}")
    print(f"Coherence Ψ: {result.psi:.6f}")
    print()
    print("Top 5 prime contributions (by norm):")
    top_indices = np.argsort(result.prime_contributions)[-5:][::-1]
    for idx in top_indices:
        p = op.primes[idx]
        contrib = result.prime_contributions[idx]
        print(f"  p = {p:3d}: contribution norm = {contrib:.6f}")
    print()
    
    if HAS_MATPLOTLIB:
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        
        # Plot potential V(u)
        axes[0, 0].plot(op.u_grid, result.potential_values, 'b-', linewidth=1)
        axes[0, 0].axvline(0, color='r', linestyle='--', alpha=0.5)
        axes[0, 0].axhline(0, color='k', linestyle='-', alpha=0.3)
        axes[0, 0].set_xlabel('u')
        axes[0, 0].set_ylabel('V(u)')
        axes[0, 0].set_title('Arithmetic Potential')
        axes[0, 0].grid(True, alpha=0.3)
        
        # Plot Fourier spectrum
        freqs = np.fft.fftshift(np.fft.fftfreq(len(result.fourier_spectrum), op.du))
        amplitudes = np.abs(result.fourier_spectrum)
        axes[0, 1].plot(freqs, amplitudes, 'g-', linewidth=1)
        axes[0, 1].set_xlabel('Frequency')
        axes[0, 1].set_ylabel('|V̂(ω)|')
        axes[0, 1].set_title('Fourier Spectrum (Prime Peaks)')
        axes[0, 1].set_xlim(-5, 5)
        axes[0, 1].grid(True, alpha=0.3)
        
        # Plot prime contributions
        axes[1, 0].bar(range(len(result.prime_contributions)), result.prime_contributions)
        axes[1, 0].set_xlabel('Prime index')
        axes[1, 0].set_ylabel('Contribution norm')
        axes[1, 0].set_title('Individual Prime Contributions')
        axes[1, 0].grid(True, alpha=0.3)
        
        # Plot a few prime contributions individually
        axes[1, 1].axhline(0, color='k', linestyle='-', alpha=0.3)
        for i, p in enumerate([2, 3, 5, 7]):
            contrib = op.prime_contribution(p, op.u_grid)
            axes[1, 1].plot(op.u_grid, contrib, label=f'p={p}', alpha=0.7, linewidth=1)
        axes[1, 1].set_xlabel('u')
        axes[1, 1].set_ylabel('Contribution')
        axes[1, 1].set_title('First Few Prime Contributions')
        axes[1, 1].legend()
        axes[1, 1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('demo_hilbert_polya_potential.png', dpi=150)
        print("Saved: demo_hilbert_polya_potential.png")
        plt.close()
    
    print()
    return result


def demo_4_complete_operator():
    """Demonstrate complete Hilbert-Pólya operator"""
    print("=" * 80)
    print("DEMO 4: Complete Hilbert-Pólya Operator H_Ω")
    print("=" * 80)
    print()
    
    op = HilbertPolyaOperator(n_points=256, u_max=10.0, n_primes=30, n_zeros=10)
    result = op.compute()
    
    print("Operator: H_Ω = H₀ + V")
    print()
    print("Coherence Metrics:")
    print(f"  Ψ_Hermiticity   = {result.psi_hermiticity:.6f}")
    print(f"  Ψ_Spectral      = {result.psi_spectral:.6f}")
    print(f"  Ψ_GUE           = {result.psi_gue:.6f}")
    print(f"  Ψ_Global        = {result.psi:.6f}")
    print()
    print("Error Metrics:")
    print(f"  Hermiticity error:      {result.hermiticity_error:.2e}")
    print(f"  Spectral error (RMS):   {result.spectral_error:.4f}")
    print(f"  GUE KS statistic:       {result.gue_spacing_ks:.4f}")
    print(f"  Explicit formula error: {result.explicit_formula_error:.4f}")
    print()
    print("Comparison with Riemann Zeros:")
    print(f"  {'Eigenvalue':>12}  {'Zero γ_n':>12}  {'Difference':>12}")
    for i in range(min(5, len(result.zeros_comparison))):
        eig, zero = result.zeros_comparison[i]
        diff = eig - zero
        print(f"  {eig:12.6f}  {zero:12.6f}  {diff:+12.6f}")
    print()
    
    if HAS_MATPLOTLIB:
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        
        # Plot full spectrum
        axes[0, 0].plot(result.eigenvalues, 'b.', markersize=3)
        axes[0, 0].set_xlabel('Index')
        axes[0, 0].set_ylabel('Eigenvalue')
        axes[0, 0].set_title('Complete Operator Spectrum')
        axes[0, 0].grid(True, alpha=0.3)
        
        # Plot comparison with zeros
        central_eigs = result.zeros_comparison[:, 0]
        zeros = result.zeros_comparison[:, 1]
        indices = np.arange(len(central_eigs))
        
        axes[0, 1].plot(indices, central_eigs, 'b.-', label='Eigenvalues', markersize=8)
        axes[0, 1].plot(indices, zeros, 'r.--', label='Riemann Zeros', markersize=8)
        axes[0, 1].set_xlabel('Index')
        axes[0, 1].set_ylabel('Value')
        axes[0, 1].set_title('Eigenvalue vs. Zero Comparison')
        axes[0, 1].legend()
        axes[0, 1].grid(True, alpha=0.3)
        
        # Plot level spacings
        spacings = np.diff(result.eigenvalues)
        spacings = spacings[spacings > 0.01]  # Filter out near-degeneracies
        mean_spacing = np.mean(spacings)
        normalized_spacings = spacings / mean_spacing if mean_spacing > 0 else spacings
        
        axes[1, 0].hist(normalized_spacings, bins=30, density=True, alpha=0.7, 
                        edgecolor='black', label='Observed')
        
        # GUE prediction
        s_theory = np.linspace(0, 3, 100)
        gue_pdf = (np.pi / 2) * s_theory * np.exp(-np.pi * s_theory**2 / 4)
        axes[1, 0].plot(s_theory, gue_pdf, 'r-', linewidth=2, label='GUE (Wigner)')
        
        axes[1, 0].set_xlabel('Normalized spacing s')
        axes[1, 0].set_ylabel('Density p(s)')
        axes[1, 0].set_title('Level Spacing Distribution')
        axes[1, 0].legend()
        axes[1, 0].grid(True, alpha=0.3)
        
        # Plot coherence metrics
        metrics = [result.psi_hermiticity, result.psi_spectral, 
                  result.psi_gue, result.psi]
        labels = ['Hermiticity', 'Spectral', 'GUE', 'Global']
        colors = ['green', 'blue', 'orange', 'red']
        
        bars = axes[1, 1].bar(labels, metrics, color=colors, alpha=0.7, edgecolor='black')
        axes[1, 1].axhline(PSI_THRESHOLD, color='red', linestyle='--', 
                          linewidth=2, label=f'Threshold ({PSI_THRESHOLD})')
        axes[1, 1].set_ylabel('Coherence Ψ')
        axes[1, 1].set_title('Coherence Metrics')
        axes[1, 1].set_ylim(0, 1.1)
        axes[1, 1].legend()
        axes[1, 1].grid(True, alpha=0.3, axis='y')
        
        # Add values on bars
        for bar, metric in zip(bars, metrics):
            height = bar.get_height()
            axes[1, 1].text(bar.get_x() + bar.get_width()/2., height,
                          f'{metric:.3f}', ha='center', va='bottom')
        
        plt.tight_layout()
        plt.savefig('demo_hilbert_polya_complete.png', dpi=150)
        print("Saved: demo_hilbert_polya_complete.png")
        plt.close()
    
    print()
    return result


def demo_5_qcal_integration():
    """Demonstrate QCAL ∞³ integration"""
    print("=" * 80)
    print("DEMO 5: QCAL ∞³ Integration")
    print("=" * 80)
    print()
    
    print("QCAL Constants:")
    print(f"  f₀ = {F0_QCAL} Hz (fundamental frequency)")
    print(f"  C_coherence = {C_COHERENCE} (coherence constant)")
    print(f"  Ψ_threshold = {PSI_THRESHOLD} (minimum coherence)")
    print()
    
    print("Geometric Validation:")
    checks = verificar_geometria_logaritmica()
    for key, value in checks.items():
        status = "✅" if value else "❌"
        print(f"  {status} {key}")
    print()
    
    print("Activation Certificate:")
    cert = activar_hilbert_polya()
    print(f"  SHA-256: {cert}")
    print()
    
    print("Theoretical Interpretation:")
    print("  • u = 0 → Nodo Zero (Zero Node)")
    print("  • Flow xp → Dilation motor")
    print("  • Primes → Logarithmic field resonances")
    print("  • Zeros → Eigenlevels of H_Ω")
    print("  • Chaotic dynamics → GUE statistics")
    print()


def main():
    """Run all demonstrations"""
    print("\n")
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 20 + "Hilbert-Pólya Logarithmic Operator" + " " * 24 + "║")
    print("║" + " " * 22 + "Complete Demonstration Suite" + " " * 28 + "║")
    print("║" + " " * 78 + "║")
    print("║" + " " * 12 + "QCAL ∞³ · 141.7001 Hz · José Manuel Mota Burruezo" + " " * 16 + "║")
    print("╚" + "═" * 78 + "╝")
    print("\n")
    
    # Run demonstrations
    demo_1_logarithmic_space()
    demo_2_dilation_operator()
    demo_3_arithmetic_potential()
    demo_4_complete_operator()
    demo_5_qcal_integration()
    
    print("=" * 80)
    print("DEMONSTRATION COMPLETE")
    print("=" * 80)
    print()
    print("This operator implements a candidate for the Hilbert-Pólya conjecture:")
    print("A self-adjoint operator whose eigenvalues are the nontrivial zeros")
    print("of the Riemann zeta function.")
    print()
    print("Key features:")
    print("  • Logarithmic Hilbert space with scale-inversion symmetry")
    print("  • Hyperbolic geometry near the origin (Nodo Zero)")
    print("  • Arithmetic potential via prime oscillations")
    print("  • Chaotic dynamics compatible with GUE statistics")
    print("  • Self-adjoint (Hermitian) construction")
    print()
    print("Status: Implementation complete. Theory under development.")
    print("The spectral alignment with zeros requires further parameter tuning")
    print("and theoretical refinement.")
    print()


if __name__ == "__main__":
    main()
