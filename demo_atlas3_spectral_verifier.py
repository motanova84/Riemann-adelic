#!/usr/bin/env python3
"""
Demo: Atlas³ Spectral Verifier

Demonstrates the complete workflow of spectral verification
using the Atlas³ Spectral Verifier with the three pillars.

Author: José Manuel Mota Burruezo Ψ✧ ∞³
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import numpy as np
from pathlib import Path
import json

from core.atlas3_spectral_verifier import (
    create_atlas3_verifier,
    F0_BASE,
    F0_RESONANCE,
)


def demo_perfect_system():
    """
    Demonstrate Atlas³ verification with perfect critical line alignment
    and GUE-like spacing.
    """
    print("=" * 80)
    print("Demo 1: Perfect System (High Coherence Expected)")
    print("=" * 80)
    print()
    
    # Create verifier
    verifier = create_atlas3_verifier(
        node_id="demo_perfect",
        precision=25
    )
    
    # Generate perfect eigenvalues
    # Re(λ) = 0.5 exactly, Im(λ) with GUE-like spacing
    np.random.seed(888)  # QCAL resonance seed
    N = 100
    
    real_parts = np.full(N, 0.5)
    imag_parts = np.cumsum(np.random.gamma(2, 1, N))
    eigenvalues = real_parts + 1j * imag_parts
    
    print(f"Generated {N} eigenvalues:")
    print(f"  - Re(λ) = 0.5 (perfect critical line)")
    print(f"  - Im(λ) spacing ~ Gamma(2, 1) (GUE-like)")
    print()
    
    # Verify spectral signature
    signature = verifier.verify_spectral_signature(eigenvalues)
    
    # Generate beacon
    beacon_path = verifier.generate_beacon(signature, metadata={
        "demo": "perfect_system",
        "seed": 888
    })
    
    # Print activation report
    report = verifier.activation_report(signature)
    print(report)
    print()
    print(f"Beacon saved to: {beacon_path}")
    print()


def demo_imperfect_system():
    """
    Demonstrate Atlas³ verification with deviation from critical line
    and non-GUE spacing.
    """
    print("=" * 80)
    print("Demo 2: Imperfect System (Lower Coherence Expected)")
    print("=" * 80)
    print()
    
    # Create verifier
    verifier = create_atlas3_verifier(
        node_id="demo_imperfect",
        precision=25
    )
    
    # Generate imperfect eigenvalues
    np.random.seed(999)
    N = 50
    
    # Deviation from critical line
    real_parts = 0.51 + 0.03 * np.random.randn(N)
    
    # Non-GUE spacing (uniform random)
    imag_parts = np.cumsum(np.random.uniform(0.5, 2.0, N))
    eigenvalues = real_parts + 1j * imag_parts
    
    print(f"Generated {N} eigenvalues:")
    print(f"  - Re(λ) ~ 0.51 ± 0.03 (off critical line)")
    print(f"  - Im(λ) spacing ~ Uniform (not GUE)")
    print()
    
    # Verify spectral signature
    signature = verifier.verify_spectral_signature(eigenvalues)
    
    # Generate beacon
    beacon_path = verifier.generate_beacon(signature, metadata={
        "demo": "imperfect_system",
        "seed": 999
    })
    
    # Print activation report
    report = verifier.activation_report(signature)
    print(report)
    print()
    print(f"Beacon saved to: {beacon_path}")
    print()


def demo_pillar_analysis():
    """
    Demonstrate detailed analysis of each pillar separately.
    """
    print("=" * 80)
    print("Demo 3: Detailed Pillar Analysis")
    print("=" * 80)
    print()
    
    verifier = create_atlas3_verifier(node_id="demo_analysis")
    
    # Generate test eigenvalues
    np.random.seed(141)
    N = 60
    eigenvalues = 0.5 + 0.005 * np.random.randn(N) + \
                  1j * np.cumsum(np.random.gamma(2, 1, N))
    
    print(f"Generated {N} test eigenvalues")
    print()
    
    # Pilar 1: Critical Line Alignment
    print("━━━ PILAR 1: La Columna Vertebral ━━━")
    mean_re, std_re, deviation = verifier.verify_critical_line_alignment(
        eigenvalues
    )
    print(f"  Mean Re(λ):  {mean_re:.8f}")
    print(f"  Std Re(λ):   {std_re:.8f}")
    print(f"  Deviation:   {deviation:.8f}")
    print(f"  Target:      {0.5}")
    print(f"  Status:      {'✅ ALIGNED' if deviation < 0.05 else '⚠️ DEVIATING'}")
    print()
    
    # Pilar 2: GUE Detection
    print("━━━ PILAR 2: El Latido del Corazón ━━━")
    gue_detected, p_value = verifier.detect_gue_statistics(eigenvalues)
    print(f"  KS p-value:  {p_value:.6f}")
    print(f"  α level:     {0.05}")
    print(f"  GUE class:   {'GUE' if gue_detected else 'Unknown'}")
    print(f"  Status:      {'✅ DETECTED' if gue_detected else '⚠️ NOT CONFIRMED'}")
    print()
    
    # Pilar 3: Spectral Rigidity
    print("━━━ PILAR 3: La Memoria ━━━")
    sigma2_values, slope = verifier.compute_spectral_rigidity(eigenvalues)
    theoretical_slope = 1.0 / (np.pi**2)
    print(f"  Σ² values:   {len(sigma2_values)} computed")
    print(f"  Mean Σ²:     {np.mean(sigma2_values):.6f}")
    print(f"  Slope:       {slope:.6f}")
    print(f"  Theory:      {theoretical_slope:.6f} (π⁻²)")
    print(f"  Status:      {'✅ HOLONOMIC' if abs(slope - theoretical_slope) < 0.5 else '⚠️ EVOLVING'}")
    print()
    
    # Coherence Ψ
    print("━━━ COHERENCE Ψ ━━━")
    coherence = verifier.compute_coherence_psi(
        deviation, p_value, slope, theoretical_slope
    )
    print(f"  Ψ:           {coherence:.6f}")
    print(f"  Threshold:   {0.888}")
    print(f"  Status:      {'✅ SOVEREIGN' if coherence >= 0.888 else '⚠️ SUB-THRESHOLD'}")
    print()


def demo_beacon_inspection():
    """
    Demonstrate beacon inspection and validation.
    """
    print("=" * 80)
    print("Demo 4: Beacon Inspection")
    print("=" * 80)
    print()
    
    # Generate a beacon
    verifier = create_atlas3_verifier(node_id="demo_beacon")
    
    np.random.seed(777)
    N = 40
    eigenvalues = 0.5 + 0.01 * np.random.randn(N) + \
                  1j * np.cumsum(np.random.gamma(2, 1, N))
    
    signature = verifier.verify_spectral_signature(eigenvalues)
    beacon_path = verifier.generate_beacon(signature)
    
    # Inspect beacon
    print(f"Beacon generated: {beacon_path}")
    print()
    
    with open(beacon_path, 'r') as f:
        beacon_data = json.load(f)
    
    print("Beacon Contents:")
    print("-" * 40)
    print(f"  Node ID:          {beacon_data['node_id']}")
    print(f"  Protocol:         {beacon_data['protocol']}")
    print(f"  Timestamp:        {beacon_data['timestamp']}")
    print()
    print(f"  Base Frequency:   {beacon_data['frequency_base']} Hz")
    print(f"  Resonance:        {beacon_data['frequency_resonance']} Hz")
    print(f"  Φ⁴:               {beacon_data['phi_power_4']:.6f}")
    print()
    print("  Spectral Signature:")
    sig = beacon_data['spectral_signature']
    print(f"    Eigenvalues:    {sig['num_eigenvalues']}")
    print(f"    Mean Re(λ):     {sig['mean_real_part']:.8f}")
    print(f"    Deviation:      {sig['critical_line_deviation']:.8f}")
    print()
    print("  Three Pillars:")
    print(f"    Columna:        {beacon_data['critical_line_alignment']['status']}")
    print(f"    Latido:         {beacon_data['gue_statistics']['status']}")
    print(f"    Memoria:        {beacon_data['spectral_rigidity']['status']}")
    print()
    print(f"  Coherence Ψ:     {beacon_data['coherence']['psi']:.6f}")
    print(f"  Status:          {beacon_data['coherence']['status']}")
    print()
    print(f"  QCAL Signature:  {beacon_data['qcal_signature']}")
    print(f"  Author:          {beacon_data['author']}")
    print()


def demo_evolution_tracking():
    """
    Demonstrate tracking system evolution through multiple verifications.
    """
    print("=" * 80)
    print("Demo 5: Evolution Tracking")
    print("=" * 80)
    print()
    
    verifier = create_atlas3_verifier(node_id="demo_evolution")
    
    print("Tracking coherence evolution with increasing eigenvalues:")
    print()
    
    np.random.seed(888)
    N_values = [20, 50, 100, 200]
    
    results = []
    
    for N in N_values:
        # Generate eigenvalues
        eigenvalues = 0.5 + 0.001 * np.random.randn(N) + \
                      1j * np.cumsum(np.random.gamma(2, 1, N))
        
        # Verify
        signature = verifier.verify_spectral_signature(eigenvalues)
        
        results.append({
            'N': N,
            'coherence': signature.coherence_psi,
            'deviation': signature.critical_line_deviation,
            'p_value': signature.gue_p_value,
            'gue_detected': signature.gue_detected,
        })
        
        print(f"N = {N:3d}  →  Ψ = {signature.coherence_psi:.4f}  "
              f"(GUE: {'✅' if signature.gue_detected else '⚠️'}  "
              f"p={signature.gue_p_value:.3f})")
    
    print()
    print("Evolution Summary:")
    print("-" * 40)
    for r in results:
        status = "✅ SOVEREIGN" if r['coherence'] >= 0.888 else "⚠️ EVOLVING"
        print(f"  N={r['N']:3d}: Ψ={r['coherence']:.4f} {status}")
    print()


def main():
    """Run all demonstrations."""
    print()
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "    Atlas³ Spectral Verifier — Complete Demonstration".center(78) + "║")
    print("║" + "    Noēsis ∞³ — El Ojo del Oráculo".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    print()
    print(f"Base Frequency:      {F0_BASE} Hz")
    print(f"Resonance Harmonic:  {F0_RESONANCE} Hz (Φ⁴)")
    print()
    print("Protocol: QCAL-SYMBIO-BRIDGE v1.0")
    print("Signature: ∴𓂀Ω∞³Φ @ 888 Hz")
    print()
    
    # Run demonstrations
    demo_perfect_system()
    input("Press Enter to continue to Demo 2...")
    print()
    
    demo_imperfect_system()
    input("Press Enter to continue to Demo 3...")
    print()
    
    demo_pillar_analysis()
    input("Press Enter to continue to Demo 4...")
    print()
    
    demo_beacon_inspection()
    input("Press Enter to continue to Demo 5...")
    print()
    
    demo_evolution_tracking()
    
    print()
    print("=" * 80)
    print("All demonstrations complete!")
    print()
    print("Check data/beacons/ directory for generated beacon files.")
    print()
    print("∴𓂀Ω∞³Φ @ 888 Hz")
    print("=" * 80)


if __name__ == "__main__":
    main()
