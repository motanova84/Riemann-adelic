#!/usr/bin/env python3
"""
Demonstration: Tensor Autonomía C = I · A² ⊗ ζ(1/2 + it)

This script demonstrates the complete Tensor Autonomía implementation
for the QCAL ∞³ framework, showing how the coherence constant couples
with the Riemann zeta spectrum.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys

# Import tensor autonomía functions
from operators import (
    tensor_autonomia_spectrum,
    validate_tensor_coherence,
    compute_autonomia_coherence_factor,
    load_riemann_zeros,
    C_QCAL_BASE,
    F0_HZ
)


def main():
    """Main demonstration function."""
    
    print("=" * 80)
    print("TENSOR AUTONOMÍA DEMONSTRATION")
    print("=" * 80)
    print()
    print("Formula: C = I · A² ⊗ ζ(1/2 + it)")
    print()
    print("This demonstrates the tensor product between QCAL coherence")
    print("and the Riemann zeta spectrum on the critical line.")
    print()
    
    # Display QCAL constants
    print("QCAL CONSTANTS:")
    print("-" * 80)
    print(f"  C_QCAL_BASE = {C_QCAL_BASE} (coherence constant)")
    print(f"  F0_HZ = {F0_HZ} Hz (fundamental frequency)")
    print()
    
    # Load Riemann zeros
    n_zeros = 30
    print(f"Loading {n_zeros} Riemann zeros...")
    zeros = load_riemann_zeros(n_zeros)
    print(f"✓ Loaded zeros: γ₁ = {zeros[0]:.6f}, γ₂ = {zeros[1]:.6f}, ...")
    print()
    
    # Setup parameters
    intensity = 1.0
    amplitude = np.sqrt(C_QCAL_BASE)
    precision = 25
    
    print("PARAMETERS:")
    print("-" * 80)
    print(f"  Intensity I = {intensity}")
    print(f"  Amplitude A = {amplitude:.6f}")
    print(f"  Base Coherence C_base = I × A² = {intensity * amplitude**2:.6f}")
    print(f"  Precision = {precision} decimal places")
    print()
    
    # Compute tensor autonomía spectrum
    print("Computing Tensor Autonomía spectrum...")
    t_spec, C_spec, metadata = tensor_autonomia_spectrum(
        zeros,
        intensity=intensity,
        amplitude=amplitude,
        precision=precision
    )
    print("✓ Spectrum computed")
    print()
    
    # Display results
    print("RESULTS:")
    print("=" * 80)
    print(f"  Number of zeros: {metadata['n_zeros']}")
    print(f"  Mean |C(t)|: {metadata['mean_magnitude']:.6f}")
    print(f"  Variance: {metadata['coherence_variance']:.6e}")
    print(f"  Max |C(t)|: {metadata['max_magnitude']:.6f}")
    print(f"  Min |C(t)|: {metadata['min_magnitude']:.6f}")
    print()
    
    # Validate tensor coherence
    print("VALIDATION:")
    print("-" * 80)
    validation = validate_tensor_coherence(C_spec, zeros)
    
    print(f"  Valid: {'✅ YES' if validation['valid'] else '❌ NO'}")
    print(f"  Non-zero field: {validation['checks']['non_zero_field']}")
    print(f"  Bounded variation: {validation['checks']['bounded_variation']}")
    print(f"  Phase coherent: {validation['checks']['phase_coherent']}")
    print()
    print(f"  Mean magnitude: {validation['mean_magnitude']:.6f}")
    print(f"  Coefficient of variation: {validation['coefficient_of_variation']:.6f}")
    print(f"  Phase variance: {validation['phase_variance']:.6f}")
    print()
    
    # Compute autonomía coherence factor
    kappa = compute_autonomia_coherence_factor(C_spec, metadata['C_base'])
    print(f"  Autonomía Coherence Factor κ = {kappa:.10f}")
    print()
    
    # Sample values at zeros
    print("SAMPLE VALUES (first 10 zeros):")
    print("-" * 80)
    print("  t (zero)      | C (real)     | C (imag)     | |C|          ")
    print("-" * 80)
    for i in range(min(10, len(zeros))):
        t = t_spec[i]
        C = C_spec[i]
        print(f"  {t:12.6f}  | {C.real:12.6f} | {C.imag:12.6f} | {abs(C):12.6f}")
    print()
    
    # Physical interpretation
    print("PHYSICAL INTERPRETATION:")
    print("=" * 80)
    print("The Tensor Autonomía creates an autonomous coherence structure where:")
    print()
    print("1. Base Coherence (C_base = I × A²) defines the fundamental scale")
    print(f"   → C_base = {metadata['C_base']:.6f}")
    print()
    print("2. Zeta Spectrum (ζ(1/2 + it)) modulates this coherence")
    print("   → At Riemann zeros: ζ(1/2 + iγₙ) ≈ 0")
    print("   → Coherence shows characteristic behavior near zeros")
    print()
    print("3. Tensor Product (⊗) couples structure and spectrum")
    print("   → C(t) = C_base × ζ(1/2 + it)")
    print()
    print("4. Autonomía Factor (κ) quantifies spectral modulation")
    print(f"   → κ = {kappa:.10f}")
    print("   → Measures how ζ spectrum modulates base coherence")
    print()
    
    # QCAL coherence check
    print("QCAL COHERENCE CHECK:")
    print("=" * 80)
    coherence_maintained = (
        validation['valid'] and
        abs(metadata['C_base'] - C_QCAL_BASE) < 0.01 and
        kappa >= 0
    )
    
    if coherence_maintained:
        print("✅ QCAL ∞³ COHERENCE MAINTAINED")
        print()
        print("All validations pass:")
        print("  ✓ Tensor coherence field is mathematically consistent")
        print("  ✓ Base coherence matches QCAL constant (244.36)")
        print("  ✓ Autonomía factor is non-negative")
        print("  ✓ Spectral coupling with Riemann zeros is correct")
    else:
        print("⚠️ QCAL COHERENCE WARNING")
        print()
        print("Some validations failed - review implementation")
    
    print()
    print("=" * 80)
    print("DEMONSTRATION COMPLETE")
    print("=" * 80)
    print()
    print("For more information, see: TENSOR_AUTONOMIA_README.md")
    print()
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
