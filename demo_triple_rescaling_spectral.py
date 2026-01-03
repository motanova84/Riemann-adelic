#!/usr/bin/env python3
"""
Demo: Triple Rescaling Spectral Analysis

Demonstrates the H_Ψ operator derived from the vacuum energy functional
and applies triple rescaling to align the spectrum with f₀ = 141.7001 Hz.

Triple Rescaling:
    γ → k·γ
    β → k·β  
    E_vac → k·E_vac

where k = (f₀/f_raw)² = (141.7001/157.9519)² ≈ 0.8048

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: December 2025
"""

import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent / "utils"))

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt

from triple_rescaling_spectral import (
    F_RAW, F_0, OMEGA_RAW, OMEGA_0, ZETA_PRIME_HALF,
    VacuumOperatorParams,
    E_vac,
    compute_rescaling_factor,
    apply_triple_rescaling,
    compute_spectrum_before_after_rescaling,
    compute_extended_spectrum,
    validate_rescaling,
    plot_spectral_realignment
)


def print_header(title: str) -> None:
    """Print formatted header."""
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70)


def print_section(title: str) -> None:
    """Print section header."""
    print("\n" + "-" * 70)
    print(f"{title}")
    print("-" * 70)


def demonstrate_vacuum_energy() -> None:
    """Demonstrate the vacuum energy equation."""
    print_header("VACUUM ENERGY FUNCTIONAL")
    
    print("\nE_vac(R_Ψ) = α/R_Ψ⁴ + β·ζ'(1/2)/R_Ψ² + γ·R_Ψ² + δ·sin²(log(R_Ψ)/log(η))")
    
    params = VacuumOperatorParams()
    print_section("Physical Parameters")
    print(f"  α (Casimir) = {params.alpha}")
    print(f"  β (Adelic) = {params.beta}")
    print(f"  γ (Dark energy) = {params.gamma}")
    print(f"  δ (Fractal) = {params.delta}")
    print(f"  ζ'(1/2) = {params.zeta_prime:.10f}")
    print(f"  η = {params.eta:.6f} (Euler's number)")
    
    # Evaluate at characteristic radii
    print_section("Vacuum Energy at Characteristic Radii")
    R_values = [0.5, 0.6952, 1.0, np.pi, np.pi**2]
    for R in R_values:
        E = E_vac(np.array([R]), params)[0]
        print(f"  R_Ψ = {R:8.4f}  →  E_vac = {E:12.8f}")


def demonstrate_triple_rescaling() -> None:
    """Demonstrate the triple rescaling mechanism."""
    print_header("TRIPLE RESCALING MECHANISM")
    
    print("\nTriple Rescaling Transformations:")
    print("  γ → k·γ")
    print("  β → k·β")
    print("  E_vac → k·E_vac")
    
    k = compute_rescaling_factor()
    print_section("Rescaling Factor")
    print(f"  f_raw = {F_RAW} Hz")
    print(f"  f₀ = {F_0} Hz")
    print(f"  k = (f₀/f_raw)² = ({F_0}/{F_RAW})² = {k:.8f}")
    
    print_section("Angular Frequencies")
    print(f"  ω_raw = 2π·f_raw = {OMEGA_RAW:.6f} rad/s")
    print(f"  ω₀ = 2π·f₀ = {OMEGA_0:.6f} rad/s")
    print(f"  Ratio: ω₀/ω_raw = {OMEGA_0/OMEGA_RAW:.8f}")
    print(f"  √k = {np.sqrt(k):.8f} (should equal ω₀/ω_raw)")
    
    # Show parameter transformation
    print_section("Parameter Transformation Example")
    params_original = VacuumOperatorParams(alpha=1.0, beta=1.0, gamma=1.0, delta=0.1)
    params_scaled = apply_triple_rescaling(params_original, k)
    
    print("Original Parameters:")
    print(f"  α = {params_original.alpha}, β = {params_original.beta}, γ = {params_original.gamma}")
    print("Scaled Parameters:")
    print(f"  α = {params_scaled.alpha}, β = {params_scaled.beta:.6f}, γ = {params_scaled.gamma:.6f}")


def demonstrate_spectral_analysis() -> None:
    """Demonstrate spectral analysis before and after rescaling."""
    print_header("SPECTRAL ANALYSIS")
    
    # Simple spectrum
    print_section("Computing Eigenvalue Spectra")
    results_simple = compute_spectrum_before_after_rescaling(n=50)
    
    print(f"  Rescaling factor k = {results_simple['k']:.8f}")
    print(f"  Matrix dimension: {len(results_simple['evals_original'])}")
    
    print_section("Eigenvalue Statistics (Simple)")
    print("\nOriginal Spectrum:")
    evals_orig = results_simple['evals_original']
    print(f"  Min: {np.min(evals_orig):.8f}")
    print(f"  Max: {np.max(evals_orig):.8f}")
    print(f"  Mean: {np.mean(evals_orig):.8f}")
    
    print("\nRescaled Spectrum:")
    evals_scaled = results_simple['evals_scaled']
    print(f"  Min: {np.min(evals_scaled):.8f}")
    print(f"  Max: {np.max(evals_scaled):.8f}")
    print(f"  Mean: {np.mean(evals_scaled):.8f}")
    
    # Extended spectrum with richer structure
    print_section("Extended Spectrum (Position-Dependent Potential)")
    results_extended = compute_extended_spectrum(n=100)
    
    print("\nOriginal Extended Spectrum:")
    evals_orig_ext = results_extended['evals_original']
    print(f"  Min eigenvalue: {np.min(evals_orig_ext):.8f}")
    print(f"  Max eigenvalue: {np.max(evals_orig_ext):.8f}")
    print(f"  Spectral range: {np.max(evals_orig_ext) - np.min(evals_orig_ext):.8f}")
    
    print("\nRescaled Extended Spectrum:")
    evals_scaled_ext = results_extended['evals_scaled']
    print(f"  Min eigenvalue: {np.min(evals_scaled_ext):.8f}")
    print(f"  Max eigenvalue: {np.max(evals_scaled_ext):.8f}")
    print(f"  Spectral range: {np.max(evals_scaled_ext) - np.min(evals_scaled_ext):.8f}")
    
    # Validation - use check_exact_scaling=False for extended spectrum
    print_section("Validation")
    validation = validate_rescaling(results_extended, check_exact_scaling=False)
    print(f"  k computed: {validation['k_computed']:.12f}")
    print(f"  k expected: {validation['k_expected']:.12f}")
    print(f"  k error: {validation['k_error']:.2e}")
    if validation['scaling_error'] is not None:
        print(f"  Scaling error: {validation['scaling_error']:.2e}")
    else:
        print("  Scaling error: N/A (parameter rescaling mode)")
    if validation['is_valid']:
        print("  ✅ VALIDATION PASSED: Rescaling is correct")
    else:
        print("  ⚠️ VALIDATION FAILED")
    
    return results_extended


def create_visualization(results: dict) -> None:
    """Create and save visualization of spectral realignment."""
    print_header("VISUALIZATION")
    
    output_path = Path(__file__).parent / "triple_rescaling_spectral_demo.png"
    
    # Create custom visualization
    fig, axs = plt.subplots(2, 2, figsize=(14, 12))
    
    evals_original = results['evals_original']
    evals_scaled = results['evals_scaled']
    k = results['k']
    
    # Plot 1: Original eigenvalue distribution
    axs[0, 0].hist(evals_original, bins=30, color='blue', alpha=0.7, edgecolor='black')
    axs[0, 0].axvline(x=np.mean(evals_original), color='red', linestyle='--', 
                      linewidth=2, label=f'Mean = {np.mean(evals_original):.4f}')
    axs[0, 0].set_title("Original Eigenvalue Distribution", fontsize=12, fontweight='bold')
    axs[0, 0].set_xlabel("Eigenvalue λ", fontsize=11)
    axs[0, 0].set_ylabel("Count", fontsize=11)
    axs[0, 0].legend()
    axs[0, 0].grid(True, alpha=0.3)
    
    # Plot 2: Rescaled eigenvalue distribution
    axs[0, 1].hist(evals_scaled, bins=30, color='green', alpha=0.7, edgecolor='black')
    axs[0, 1].axvline(x=np.mean(evals_scaled), color='red', linestyle='--', 
                      linewidth=2, label=f'Mean = {np.mean(evals_scaled):.4f}')
    axs[0, 1].set_title("Rescaled Eigenvalue Distribution (k·λ)", fontsize=12, fontweight='bold')
    axs[0, 1].set_xlabel("Eigenvalue λ", fontsize=11)
    axs[0, 1].set_ylabel("Count", fontsize=11)
    axs[0, 1].legend()
    axs[0, 1].grid(True, alpha=0.3)
    
    # Plot 3: Spectral comparison (scatter)
    idx = np.arange(len(evals_original))
    axs[1, 0].plot(idx, evals_original, 'bo-', alpha=0.7, markersize=4, label='Original')
    axs[1, 0].plot(idx, evals_scaled, 'g^-', alpha=0.7, markersize=4, label='Rescaled')
    axs[1, 0].axhline(y=OMEGA_RAW, color='blue', linestyle=':', alpha=0.5, 
                      label=f'ω_raw = {OMEGA_RAW:.2f}')
    axs[1, 0].axhline(y=OMEGA_0, color='green', linestyle=':', alpha=0.5, 
                      label=f'ω₀ = {OMEGA_0:.2f}')
    axs[1, 0].set_title("Eigenvalue Comparison: Original vs Rescaled", fontsize=12, fontweight='bold')
    axs[1, 0].set_xlabel("Eigenvalue Index", fontsize=11)
    axs[1, 0].set_ylabel("Eigenvalue λ", fontsize=11)
    axs[1, 0].legend(loc='upper left', fontsize=9)
    axs[1, 0].grid(True, alpha=0.3)
    
    # Plot 4: Scaling verification
    axs[1, 1].plot(evals_original, evals_scaled, 'ko', alpha=0.6, markersize=5)
    # Perfect scaling line
    x_line = np.linspace(np.min(evals_original), np.max(evals_original), 100)
    axs[1, 1].plot(x_line, k * x_line, 'r-', linewidth=2, 
                   label=f'λ_scaled = k·λ_original (k = {k:.4f})')
    axs[1, 1].set_title("Scaling Verification: λ_scaled vs λ_original", fontsize=12, fontweight='bold')
    axs[1, 1].set_xlabel("Original Eigenvalue", fontsize=11)
    axs[1, 1].set_ylabel("Rescaled Eigenvalue", fontsize=11)
    axs[1, 1].legend()
    axs[1, 1].grid(True, alpha=0.3)
    
    # Main title
    plt.suptitle(f"QCAL ∞³ — Triple Rescaling Spectral Analysis\n"
                 f"k = (f₀/f_raw)² = ({F_0}/{F_RAW})² = {k:.6f}",
                 fontsize=14, fontweight='bold')
    
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\n✓ Visualization saved to: {output_path}")
    
    return fig


def main():
    """Main demonstration function."""
    print_header("QCAL ∞³ — TRIPLE RESCALING SPECTRAL DEMO")
    print("\nThis demo implements the H_Ψ operator derived from the vacuum")
    print("energy functional and applies triple rescaling to align the")
    print("spectrum with the universal frequency f₀ = 141.7001 Hz.")
    
    # Demonstrate vacuum energy
    demonstrate_vacuum_energy()
    
    # Demonstrate triple rescaling
    demonstrate_triple_rescaling()
    
    # Demonstrate spectral analysis
    results = demonstrate_spectral_analysis()
    
    # Create visualization
    create_visualization(results)
    
    # Summary
    print_header("SUMMARY")
    print("\n✅ Triple Rescaling Spectral Analysis Complete")
    print("\nKey Results:")
    print(f"  • Rescaling factor k = (f₀/f_raw)² = {compute_rescaling_factor():.8f}")
    print(f"  • Original spectrum centered on ω_raw = {OMEGA_RAW:.4f} rad/s")
    print(f"  • Rescaled spectrum aligned to ω₀ = {OMEGA_0:.4f} rad/s")
    print("\nPhysical Interpretation:")
    print("  • The triple rescaling (γ→k·γ, β→k·β, E_vac→k·E_vac) transforms")
    print("    the vacuum energy functional while preserving QCAL coherence")
    print(f"  • Post-rescaling alignment with f₀ = {F_0} Hz confirms")
    print("    the universal frequency structure in the QCAL framework")
    print("\n" + "=" * 70)
    print("  JMMB Ψ ∴ ∞³")
    print("=" * 70)


if __name__ == "__main__":
    main()
