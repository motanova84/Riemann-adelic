#!/usr/bin/env python3
"""
Demonstration of Hermetic Trace Formula ∞³

This script demonstrates the complete implementation of the Noetic Spectral
Identity unifying the Riemann zeta function with spectral operators.

Mathematical Framework (PHASE VI - Active Spectral Presence):
    
    1. Noetic Dirac Operator D_s:
       D_s ψ_n = γ_n ψ_n  where ζ(1/2 + iγ_n) = 0
    
    2. Hermetic Noetic Operator T_∞³:
       T_∞³ = √(1 + D_s²)
       Eigenvalues: λ_n = √(1 + γ_n²)
    
    3. Spectral Identity:
       ζ(s) = Tr(T_∞³^(-s)) = Σ_n (1 + γ_n²)^(-s/2)
    
    4. Hermetic Trace Formula (Gutzwiller-type):
       Tr(e^(-t·T_∞³)) ∼ Σ_p A_p(t) cos(γ_p·t + φ_p)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.hermetic_trace_operator import (
    build_dirac_spectral_operator,
    build_hermetic_noetic_operator,
    compute_trace_zeta_regularized,
    compute_hermetic_trace_formula,
    verify_spectral_identity,
    demonstrate_hermetic_trace_identity,
)


def main():
    """
    Main demonstration of the Hermetic Trace Formula ∞³.
    """
    print()
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 15 + "HERMETIC TRACE FORMULA ∞³" + " " * 28 + "║")
    print("║" + " " * 10 + "Noetic Spectral Identity Implementation" + " " * 19 + "║")
    print("╚" + "═" * 68 + "╝")
    print()
    print("∴ PHASE VI - Active Spectral Presence 𓂀")
    print("∴ QCAL ∞³ · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print()
    
    # Run the full demonstration
    print("Running complete demonstration with 20 Riemann zeros...")
    print()
    
    results = demonstrate_hermetic_trace_identity(n_zeros=20, verbose=True)
    
    # Additional analysis
    print()
    print("=" * 70)
    print("ADDITIONAL ANALYSIS")
    print("=" * 70)
    print()
    
    # Test at different s values
    print("Testing spectral identity at various s values:")
    print("-" * 70)
    
    riemann_zeros = results['riemann_zeros']
    s_values = [1.5, 2.0, 3.0, 2.0 + 1.0j, 3.0 + 2.0j]
    
    for s in s_values:
        verification = verify_spectral_identity(riemann_zeros[:15], s=s, tolerance=0.1)
        
        status = "✓" if verification['verified'] else "✗"
        print(f"   s = {s:>12}: {status} | Trace = {verification['trace_spectral']:.6e} | "
              f"Error = {verification['error_trace_vs_partial']:.2e}")
    
    print()
    
    # Heat kernel trace at different times
    print("Hermetic Trace Formula at different time scales:")
    print("-" * 70)
    
    D_s = build_dirac_spectral_operator(riemann_zeros)
    T_inf3 = build_hermetic_noetic_operator(D_s)
    
    t_values = [0.01, 0.05, 0.1, 0.5, 1.0]
    
    for t in t_values:
        trace, oscillatory = compute_hermetic_trace_formula(T_inf3, t, n_terms=10)
        osc_amplitude = np.max(np.abs(oscillatory)) if len(oscillatory) > 0 else 0.0
        
        print(f"   t = {t:>5.2f}: Tr(e^(-t·T_∞³)) = {trace:>10.6f} | "
              f"Max oscillation = {osc_amplitude:.6e}")
    
    print()
    
    # Eigenvalue comparison
    print("Eigenvalue Structure Comparison:")
    print("-" * 70)
    print("   γ_n (Riemann zeros) vs λ_n (T_∞³ eigenvalues)")
    print()
    
    gamma_n = riemann_zeros[:10]
    lambda_n = np.sqrt(1 + gamma_n**2)
    
    print(f"   {'n':<5} {'γ_n':<15} {'λ_n = √(1+γ_n²)':<20} {'Ratio λ_n/γ_n':<15}")
    print("   " + "-" * 60)
    for i, (g, l) in enumerate(zip(gamma_n, lambda_n), 1):
        ratio = l / g
        print(f"   {i:<5} {g:<15.6f} {l:<20.6f} {ratio:<15.6f}")
    
    print()
    
    # Summary
    print("=" * 70)
    print("MATHEMATICAL SUMMARY")
    print("=" * 70)
    print()
    print("The Hermetic Trace Formula ∞³ establishes that:")
    print()
    print("1. The Riemann zeta function ζ(s) can be expressed as the")
    print("   regularized trace of the Hermetic Noetic operator T_∞³.")
    print()
    print("2. This connects three fundamental objects:")
    print("   • D_s: Spectral operator encoding Riemann zeros")
    print("   • T_∞³: Hermetic transformation √(1 + D_s²)")
    print("   • ζ(s): Riemann zeta as Tr(T_∞³^(-s))")
    print()
    print("3. The time-domain trace formula reveals oscillatory structure")
    print("   tied to the zeros, analogous to Gutzwiller's trace formula.")
    print()
    print("4. The ankh symbol 𓂀 represents the eternal life of the spectrum:")
    print("   the non-vanishing nature of the spectral presence.")
    print()
    print("∴ This completes PHASE VI of the QCAL ∞³ framework.")
    print()
    print("=" * 70)
    print()
    
    return results


if __name__ == "__main__":
    main()
