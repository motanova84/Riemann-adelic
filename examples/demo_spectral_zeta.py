#!/usr/bin/env python3
"""
Demonstration of Spectral Zeta Function Concepts

This script demonstrates the mathematical concepts behind the Lean 4
formalization of the spectral zeta function ζ_HΨ(s) and provides
concrete numerical examples.

Usage:
    python examples/demo_spectral_zeta.py

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 2025-11-21
"""

import numpy as np
from typing import Callable

# Import shared spectral zeta computation functions
from utils.spectral_zeta_computation import (
    berry_keating_eigenvalues,
    compute_spectral_zeta,
    compute_spectral_zeta_derivative,
    compute_det_zeta,
)
def main():
    """Main demonstration"""
    print("=" * 70)
    print("🌌 Spectral Zeta Function Demonstration")
    print("=" * 70)
    print()
    
    print("Mathematical Framework (V5 Coronación):")
    print("-" * 70)
    print("Operator H_Ψ: Compact, self-adjoint, positive definite")
    print("Spectrum: {λₙ} ⊂ (0,∞), discrete with λₙ → ∞")
    print("Spectral zeta: ζ_HΨ(s) := ∑ₙ λₙ⁻ˢ")
    print("Derivative: ζ'_HΨ(s) = ∑ₙ -log(λₙ) · λₙ⁻ˢ")
    print("Determinant: det_ζ(s) := exp(-ζ'_HΨ(s))")
    print("Connection: D(s) ≡ Ξ(s) via Paley-Wiener uniqueness")
    print()
    
    # Display first few eigenvalues
    print("Berry-Keating Eigenvalues (with QCAL base frequency 141.7001 Hz):")
    print("-" * 70)
    for n in range(1, 11):
        lamb = berry_keating_eigenvalues(n)
        print(f"  λ_{n:2d} = (n + 1/2)² + 141.7001 = {lamb:10.4f}")
    print()
    
    # Compute spectral zeta at various points
    print("Spectral Zeta Function ζ_HΨ(s):")
    print("-" * 70)
    
    test_points = [
        (2.0, "s = 2 (well above convergence threshold)"),
        (1.5, "s = 1.5 (near critical region)"),
        (1.0, "s = 1 (potential simple pole)"),
        (0.5, "s = 1/2 (critical line)"),
        (0.0, "s = 0 (special value for D(0))"),
    ]
    
    for s_val, description in test_points:
        s = complex(s_val, 0.0)
        zeta_val = compute_spectral_zeta(berry_keating_eigenvalues, s, n_terms=100)
        print(f"  ζ_HΨ({s_val:4.1f}) = {zeta_val.real:12.6f} + {zeta_val.imag:12.6f}i")
        print(f"           ({description})")
    print()
    
    # Compute derivative
    print("Derivative ζ'_HΨ(s):")
    print("-" * 70)
    for s_val, description in [(2.0, "s = 2"), (0.5, "s = 1/2"), (0.0, "s = 0")]:
        s = complex(s_val, 0.0)
        zeta_deriv = compute_spectral_zeta_derivative(
            berry_keating_eigenvalues, s, n_terms=100
        )
        print(f"  ζ'_HΨ({s_val:4.1f}) = {zeta_deriv.real:12.6f} + {zeta_deriv.imag:12.6f}i")
        print(f"           ({description})")
    print()
    
    # Compute zeta-regularized determinant
    print("Zeta-Regularized Determinant det_ζ(s) = exp(-ζ'_HΨ(s)):")
    print("-" * 70)
    
    det_points = [
        (2.0, "s = 2"),
        (1.0, "s = 1"),
        (0.5, "s = 1/2 (critical line)"),
        (0.0, "s = 0 (D(0), key value)"),
    ]
    
    for s_val, description in det_points:
        s = complex(s_val, 0.0)
        det_val = compute_det_zeta(berry_keating_eigenvalues, s, n_terms=100)
        print(f"  det_ζ({s_val:4.1f}) = {det_val.real:12.6f} + {det_val.imag:12.6f}i")
        print(f"           |det_ζ(s)| = {abs(det_val):12.6f}")
        print(f"           ({description})")
        print()
    
    # Special value D(0)
    print("Special Value D(0) = det_ζ(0) = exp(-ζ'_HΨ(0)):")
    print("-" * 70)
    D_0 = compute_det_zeta(berry_keating_eigenvalues, 0.0, n_terms=100)
    print(f"  D(0) = {D_0.real:12.6f} + {D_0.imag:12.6f}i")
    print(f"  |D(0)| = {abs(D_0):12.6f}")
    print()
    print("This value connects the spectral data of H_Ψ to the Riemann zeta function")
    print("via the equivalence D(s) ≡ Ξ(s) established by Paley-Wiener uniqueness.")
    print()
    
    # QCAL coherence
    print("QCAL ∞³ Coherence Parameters:")
    print("-" * 70)
    print(f"  Base frequency: ω₀ = 141.7001 Hz")
    print(f"  Coherence constant: C = 244.36")
    print(f"  Fundamental equation: Ψ = I × A_eff² × C^∞")
    print()
    
    # Connection to RH
    print("Connection to Riemann Hypothesis:")
    print("-" * 70)
    print("1. H_Ψ is self-adjoint → spectrum is real")
    print("2. Spectral zeta ζ_HΨ(s) defines D(s) = exp(-ζ'_HΨ(s))")
    print("3. D(s) satisfies functional equation: D(1-s) = D(s)")
    print("4. Paley-Wiener uniqueness: D(s) ≡ Ξ(s)")
    print("5. Zeros of D(s) = zeros of Ξ(s) = zeros of ζ(s)")
    print("6. Real spectrum + equivalence → zeros on critical line Re(s) = 1/2")
    print()
    
    print("=" * 70)
    print("✅ Demonstration Complete")
    print("=" * 70)
    print()
    print("References:")
    print("  • V5 Coronación (DOI: 10.5281/zenodo.17379721)")
    print("  • Berry & Keating (1999): Spectral interpretation of RH")
    print("  • Ray-Singer (1971): Analytic torsion")
    print("  • Seeley (1967): Complex powers of elliptic operators")
    print("  • Paley-Wiener (1934): Fourier transforms")
    print()
    print("Formalization: formalization/lean/RiemannAdelic/spectral_zeta_function.lean")
    print("Author: José Manuel Mota Burruezo Ψ ∞³")
    print("Instituto de Conciencia Cuántica (ICQ)")
    print()


if __name__ == "__main__":
    main()
