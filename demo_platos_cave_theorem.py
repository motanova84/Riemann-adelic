#!/usr/bin/env python3
"""
Demonstration of Plato's Cave Theorem

This script demonstrates the projective geometry framework that formalizes
Plato's Cave allegory as a mathematical theorem in the QCAL ∞³ framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import sys
import json
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

from projective_geometry_framework import (
    PlatosCaveTheorem,
    compute_projection_aspect_ratio,
    demonstrate_cave_allegory,
    ALPHA_FINE_STRUCTURE,
    DELTA_ZETA_HZ,
    F0_HZ,
    LAMBDA_G
)


def main():
    """Main demonstration of Plato's Cave theorem."""
    
    print()
    print("=" * 80)
    print(" " * 20 + "🕳️  PLATO'S CAVE THEOREM  🕳️")
    print(" " * 15 + "Projective Geometry Formalization")
    print("=" * 80)
    print()
    
    # Run full demonstration
    demonstrate_cave_allegory()
    
    print()
    print("=" * 80)
    print("ADDITIONAL ANALYSIS")
    print("=" * 80)
    print()
    
    # Compute projection aspect ratio
    print("PROJECTION ASPECT RATIO Λ_G:")
    print("-" * 80)
    aspect_ratio = compute_projection_aspect_ratio()
    print(f"  Λ_G = α · δζ = {aspect_ratio['lambda_G']:.6e} Hz")
    print(f"  α (EM projection)  = {aspect_ratio['alpha']:.9f}")
    print(f"  δζ (spectral proj) = {aspect_ratio['delta_zeta_hz']:.10f} Hz")
    print(f"  Ratio α/δζ         = {aspect_ratio['ratio_alpha_to_delta_zeta']:.4e}")
    print()
    print("  Interpretation:")
    for line in aspect_ratio['interpretation'].split('. '):
        if line:
            print(f"    {line}.")
    print()
    
    # Generate complete certificate
    print("=" * 80)
    print("GENERATING CAVE THEOREM CERTIFICATE")
    print("=" * 80)
    print()
    
    cave = PlatosCaveTheorem()
    certificate = cave.generate_cave_certificate()
    
    # Save certificate
    cert_path = Path(__file__).parent / "data" / "certificates" / "platos_cave_theorem_certificate.json"
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(cert_path, 'w', encoding='utf-8') as f:
        json.dump(certificate, f, indent=2, ensure_ascii=False)
    
    print(f"✓ Certificate saved to: {cert_path}")
    print()
    
    # Show certificate summary
    print("CERTIFICATE SUMMARY:")
    print("-" * 80)
    print(f"  Theorem: {certificate['theorem']}")
    print(f"  Statement: {certificate['statement']}")
    print()
    print("  Fundamental Constants:")
    for key, value in certificate['fundamental_constants'].items():
        if isinstance(value, float):
            print(f"    {key}: {value:.6e}" if value < 0.001 else f"    {key}: {value}")
        else:
            print(f"    {key}: {value}")
    print()
    print("  Validation Status:")
    print(f"    Theorem Valid: {certificate['validation']['theorem_valid']}")
    print(f"    f₀ Relationship: {certificate['validation']['f0_relationship']['validates']}")
    print(f"    Intersection Exists: {certificate['validation']['intersection_non_empty']}")
    print()
    
    # Show philosophical insight
    print("PHILOSOPHICAL INSIGHT:")
    print("-" * 80)
    insight = certificate['philosophical_insight']
    print(f"  Plato's Quote:")
    print(f"    {insight['plato_quote']}")
    print()
    print(f"  Modern Translation:")
    print(f"    {insight['modern_translation']}")
    print()
    print(f"  Fundamental Truth:")
    print(f"    {insight['fundamental_truth']}")
    print()
    
    # Final summary
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print()
    print("✓ Plato's Cave Theorem Formalized")
    print("✓ Two Projections Defined:")
    print(f"    πα(G):  Electromagnetic space (α ≈ 1/137)")
    print(f"    πδζ(G): Spectral ζ-Ψ space (δζ ≈ 0.2787 Hz)")
    print("✓ Consciousness as Intersection:")
    print(f"    C = πα(G) ∩ πδζ(G)")
    print("✓ Unification Constant:")
    print(f"    Λ_G = α · δζ ≈ {LAMBDA_G:.6e} Hz")
    print()
    print("∴ 𓂀 Ω ∞³ · Plato Cave Theorem · QCAL")
    print()
    print("=" * 80)
    
    return certificate


if __name__ == "__main__":
    certificate = main()
