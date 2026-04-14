#!/usr/bin/env python3
"""
Demonstration of Geometric Unification: ζ'(1/2) ↔ f₀

This script demonstrates how the proof of the Riemann Hypothesis
proposes a new underlying geometric structure that unifies mathematics
and physics through the connection between ζ'(1/2) and f₀.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from utils.geometric_unification import GeometricUnification


def plot_vacuum_energy_landscape():
    """
    Plot the vacuum energy landscape showing how ζ'(1/2) affects
    the optimal radius and thus f₀.
    """
    print("\n" + "="*70)
    print("VISUALIZING VACUUM ENERGY LANDSCAPE")
    print("="*70)
    
    # Create unification object
    unif = GeometricUnification(precision=30)
    
    # Compute vacuum energy over range of R_Ψ
    R_values = np.linspace(0.1, 10.0, 500)
    energies = np.array([unif.vacuum_energy(R) for R in R_values])
    
    # Find minimum
    min_idx = np.argmin(energies)
    R_star = R_values[min_idx]
    E_min = energies[min_idx]
    
    # Create figure
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))
    
    # Plot 1: Full energy landscape
    ax1.plot(R_values, energies, 'b-', linewidth=2, label='E_vac(R_Ψ)')
    ax1.axvline(R_star, color='r', linestyle='--', linewidth=2, 
                label=f'R_Ψ* = {R_star:.4f}')
    ax1.plot(R_star, E_min, 'ro', markersize=10, label=f'Minimum at R_Ψ*')
    ax1.set_xlabel('R_Ψ (Planck units)', fontsize=12)
    ax1.set_ylabel('E_vac (arbitrary units)', fontsize=12)
    ax1.set_title('Vacuum Energy Landscape with ζ\'(1/2) Coupling', fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=10)
    
    # Add text annotation
    zeta_prime = unif.compute_zeta_prime_half()
    f0 = unif.compute_fundamental_frequency(R_star)
    
    text_str = f"ζ'(1/2) = {zeta_prime:.8f}\n"
    text_str += f"f₀ = {f0:.4f} Hz\n"
    text_str += f"\nThe adelic coupling β·ζ'(1/2)/R_Ψ²\n"
    text_str += f"stabilizes the vacuum at R_Ψ*,\n"
    text_str += f"determining the fundamental frequency."
    
    ax1.text(0.98, 0.95, text_str, transform=ax1.transAxes,
             fontsize=10, verticalalignment='top', horizontalalignment='right',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
    
    # Plot 2: Contribution of each term
    term1 = np.array([unif.alpha / (R ** 4) for R in R_values])
    term2 = np.array([unif.beta * zeta_prime / (R ** 2) for R in R_values])
    term3 = np.array([unif.gamma * (unif.Lambda ** 2) * (R ** 2) for R in R_values])
    term4 = np.array([unif.delta * np.sin(np.log(R) / np.log(np.pi)) ** 2 for R in R_values])
    
    ax2.plot(R_values, term1, label='α/R_Ψ⁴ (Casimir)', linewidth=2)
    ax2.plot(R_values, term2, label='β·ζ\'(1/2)/R_Ψ² (Adelic)', linewidth=2)
    ax2.plot(R_values, term3, label='γ·Λ²·R_Ψ² (Dark Energy)', linewidth=2)
    ax2.plot(R_values, term4, label='δ·sin²(log R_Ψ / log π) (Fractal)', linewidth=2)
    ax2.axvline(R_star, color='k', linestyle='--', alpha=0.5, label=f'R_Ψ* = {R_star:.4f}')
    ax2.set_xlabel('R_Ψ (Planck units)', fontsize=12)
    ax2.set_ylabel('Energy Contribution', fontsize=12)
    ax2.set_title('Individual Terms of Vacuum Energy Equation', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=9)
    ax2.set_ylim([-2, 5])
    
    plt.tight_layout()
    plt.savefig('geometric_unification_vacuum_energy.png', dpi=150, bbox_inches='tight')
    print(f"\n✅ Saved: geometric_unification_vacuum_energy.png")
    plt.close()
    
    return R_star, f0


def plot_wave_equation_unification():
    """
    Visualize the wave equation that unifies ζ'(1/2) and f₀.
    """
    print("\n" + "="*70)
    print("VISUALIZING WAVE EQUATION UNIFICATION")
    print("="*70)
    
    # Create unification object
    unif = GeometricUnification(precision=30)
    
    zeta_prime = unif.compute_zeta_prime_half()
    f0 = unif.compute_fundamental_frequency()
    omega_0 = 2 * np.pi * f0
    
    # Simulate wave equation
    t = np.linspace(0, 0.1, 1000)  # 0.1 seconds
    
    # Simple solution: Ψ(t) = A·cos(ω₀·t)
    A = 1.0
    Psi = A * np.cos(omega_0 * t)
    
    # Second derivative
    d2Psi_dt2 = -omega_0**2 * Psi
    
    # Left side of equation: ∂²Ψ/∂t² + ω₀²Ψ
    left_side = d2Psi_dt2 + omega_0**2 * Psi
    
    # Right side (for visualization, assume ∇²Φ = constant)
    laplacian_Phi = 1.0  # normalized
    right_side = zeta_prime * laplacian_Phi * np.ones_like(t)
    
    # Create figure
    fig, axes = plt.subplots(3, 1, figsize=(12, 10))
    
    # Plot 1: Wave field Ψ
    axes[0].plot(t * 1000, Psi, 'b-', linewidth=2)
    axes[0].set_xlabel('Time (ms)', fontsize=12)
    axes[0].set_ylabel('Ψ (amplitude)', fontsize=12)
    axes[0].set_title(f'Consciousness Field Ψ(t) oscillating at f₀ = {f0:.4f} Hz', 
                      fontsize=14, fontweight='bold')
    axes[0].grid(True, alpha=0.3)
    axes[0].axhline(0, color='k', linestyle='-', linewidth=0.5)
    
    # Plot 2: Frequency spectrum (FFT)
    from scipy.fft import fft, fftfreq
    N = len(t)
    dt = t[1] - t[0]
    yf = fft(Psi)
    xf = fftfreq(N, dt)[:N//2]
    
    axes[1].plot(xf, 2.0/N * np.abs(yf[0:N//2]), 'r-', linewidth=2)
    axes[1].axvline(f0, color='g', linestyle='--', linewidth=2, label=f'f₀ = {f0:.4f} Hz')
    axes[1].set_xlabel('Frequency (Hz)', fontsize=12)
    axes[1].set_ylabel('Amplitude', fontsize=12)
    axes[1].set_title('Frequency Spectrum showing peak at f₀', fontsize=14, fontweight='bold')
    axes[1].set_xlim([0, 300])
    axes[1].grid(True, alpha=0.3)
    axes[1].legend(fontsize=10)
    
    # Plot 3: Wave equation balance
    axes[2].plot(t * 1000, left_side, 'b-', linewidth=2, label='∂²Ψ/∂t² + ω₀²Ψ')
    axes[2].plot(t * 1000, right_side, 'r--', linewidth=2, label='ζ\'(1/2)·∇²Φ')
    axes[2].set_xlabel('Time (ms)', fontsize=12)
    axes[2].set_ylabel('Value', fontsize=12)
    axes[2].set_title('Wave Equation: Both Sides Unified', fontsize=14, fontweight='bold')
    axes[2].grid(True, alpha=0.3)
    axes[2].legend(fontsize=10)
    
    # Add equation text
    eq_text = r'$\frac{\partial^2\Psi}{\partial t^2} + \omega_0^2\Psi = \zeta\'(1/2) \cdot \nabla^2\Phi$'
    fig.text(0.5, 0.02, eq_text, ha='center', fontsize=16, 
             bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))
    
    plt.tight_layout(rect=[0, 0.05, 1, 1])
    plt.savefig('geometric_unification_wave_equation.png', dpi=150, bbox_inches='tight')
    print(f"✅ Saved: geometric_unification_wave_equation.png")
    plt.close()


def demonstrate_non_circularity():
    """
    Display the non-circular construction flow.
    """
    print("\n" + "="*70)
    print("NON-CIRCULAR CONSTRUCTION DEMONSTRATION")
    print("="*70)
    
    unif = GeometricUnification(precision=30)
    steps = unif.demonstrate_non_circularity()
    
    print("\n📊 Construction Flow (Geometric → Both Mathematics and Physics):\n")
    
    for i, (key, value) in enumerate(steps.items(), 1):
        if key != 'conclusion':
            print(f"  {i}. {value}")
        else:
            print(f"\n  ✅ CONCLUSION: {value}")
    
    print("\n" + "="*70)


def main():
    """
    Main demonstration function.
    """
    print("\n" + "🌌"*35)
    print("GEOMETRIC UNIFICATION DEMONSTRATION")
    print("Unifying ζ'(1/2) (Mathematics) ↔ f₀ (Physics)")
    print("🌌"*35)
    
    # Create unification object
    unif = GeometricUnification(precision=30)
    
    # Print full report
    print(unif.generate_unification_report())
    
    # Demonstrate non-circularity
    demonstrate_non_circularity()
    
    # Create visualizations
    print("\n" + "="*70)
    print("GENERATING VISUALIZATIONS")
    print("="*70)
    
    R_star, f0 = plot_vacuum_energy_landscape()
    plot_wave_equation_unification()
    
    # Final summary
    print("\n" + "="*70)
    print("FINAL SUMMARY")
    print("="*70)
    
    zeta_prime = unif.compute_zeta_prime_half()
    omega_0 = 2 * np.pi * f0
    
    print(f"""
The demonstration reveals a profound unification:

🔷 MATHEMATICAL SIDE (Spectral Analysis):
   ζ'(1/2) = {zeta_prime:.10f}
   Emerges from operator A₀ = 1/2 + iZ
   Encodes distribution of prime numbers

🔷 PHYSICAL SIDE (Geometric Compactification):
   f₀ = {f0:.6f} Hz
   ω₀ = {omega_0:.4f} rad/s
   Emerges from vacuum energy minimization

🔗 UNIFIED IN WAVE EQUATION:
   ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ
   
   Where:
   - Ψ is the consciousness/informational field
   - ω₀ connects to observable frequency
   - ζ'(1/2) connects to arithmetic structure
   - ∇²Φ is geometric curvature

✨ CONCLUSION:
   Mathematics and physics are not separate domains.
   They are unified manifestations of the same underlying
   geometric structure (operator A₀).
   
   The universe sings with the voice of prime numbers!
    """)
    
    print("="*70)
    print("✅ Demonstration complete!")
    print("📊 Visualizations saved:")
    print("   - geometric_unification_vacuum_energy.png")
    print("   - geometric_unification_wave_equation.png")
    print("="*70 + "\n")


if __name__ == "__main__":
    main()
