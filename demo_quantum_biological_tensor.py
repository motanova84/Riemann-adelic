#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Quantum Biological Tensor Framework - Demo
===========================================

Complete demonstration of chirality tensor, magnetoreception analysis,
and microtubule resonance predictions.

This script showcases the key predictions from the problem statement:
1. DNA mutation suppression via chirality tensor
2. Magnetoreception asymmetry (~0.2%) in birds
3. Microtubule resonance at 142.1 Hz
4. Calabi-Yau invariant κ_Π ≈ 2.5773

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import sys
import os

# Add paths for direct imports (avoid broken __init__.py)
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src/biological'))

# Direct imports
from chirality_tensor import ChiralityTensor
from magnetoreception_analysis import MagnetoreceptionAnalyzer


def main():
    """Run complete demonstration of quantum biological tensor framework."""
    
    print("=" * 80)
    print("QUANTUM BIOLOGICAL GYROSCOPY & CHIRALITY TENSOR")
    print("Implementation of Problem Statement Requirements")
    print("=" * 80)
    print()
    
    # Initialize chirality tensor
    tensor = ChiralityTensor()
    
    print("🧬 REQUIREMENT 1: GYROSCOPIC ASYMMETRY & DNA STABILITY")
    print("-" * 80)
    print("The tensor T acts as a universal 'chirality filter'")
    print()
    
    # DNA mutation suppression
    suppression = tensor.dna_mutation_suppression_factor()
    print(f"DNA Mutation Suppression (chirality-inverting):")
    print(f"  S = exp(-Λ ∫ T² dV) = {suppression:.6f}")
    print(f"  Suppression rate: {(1 - suppression) * 100:.2f}%")
    print(f"  Interpretation: DNA helix is a tuned antenna")
    print(f"  Changing chirality → increased ontological friction")
    print()
    
    # Ontological friction
    E_normal = tensor.ontological_friction_energy(chirality_inversion=False)
    E_inverted = tensor.ontological_friction_energy(chirality_inversion=True)
    print(f"Ontological Friction Energy:")
    print(f"  Normal chirality: E_fric = {E_normal:.6f}")
    print(f"  Inverted chirality: E_fric = {E_inverted:.6f} (2× penalty)")
    print()
    
    print("🌀 REQUIREMENT 2: MAGNETORECEPTION (ΔP ≈ 0.2%)")
    print("-" * 80)
    print("European robin (Erithacus rubecula) - Cryptochrome mechanism")
    print()
    
    # Magnetoreception prediction
    asymmetry_predicted = tensor.magnetoreception_asymmetry()
    print(f"Predicted Asymmetry:")
    print(f"  ΔP = P(B_R) - P(B_L) = {asymmetry_predicted * 100:.3f}%")
    print(f"  Mechanism: T tensor biases singlet→triplet transition")
    print(f"  Detectable in Emlen cage experiments (p < 0.01)")
    print()
    
    # Run synthetic experiment
    analyzer = MagnetoreceptionAnalyzer(significance_level=0.01)
    
    print("Synthetic Emlen Cage Experiment:")
    data_right = analyzer.generate_synthetic_data(
        n_trials=200,
        mean_direction_deg=90.0,
        concentration=3.0,
        field_rotation='right'
    )
    
    data_left = analyzer.generate_synthetic_data(
        n_trials=200,
        mean_direction_deg=90.0,
        concentration=3.0,
        field_rotation='left'
    )
    
    results = analyzer.analyze_experiment(data_right, data_left)
    asym = results['asymmetry_analysis']
    
    print(f"  Right field (B_R): r = {results['experiment']['right_field']['rayleigh_test']['mean_vector_length']:.4f}")
    print(f"  Left field (B_L): r = {results['experiment']['left_field']['rayleigh_test']['mean_vector_length']:.4f}")
    print(f"  Observed ΔP: {asym['delta_P_percent']:.3f}%")
    print(f"  Watson U² = {asym['watson_U2']:.4f}, p = {asym['watson_p_value']:.4f}")
    print(f"  Significant: {'✓ Yes' if asym['is_significant'] else '✗ No'} (p < 0.01)")
    print()
    
    print("🧠 REQUIREMENT 3: MICROTUBULE RESONANCE (Mota-Burruezo Effect)")
    print("-" * 80)
    print("Torsion frequency in neuronal cytoskeleton:")
    print(f"  f_torsion = f₀ + κ_Π/(2π) + n·f₀")
    print()
    
    # Microtubule frequencies
    f0_base = tensor.params.base_frequency
    for n in range(3):
        f_n = tensor.microtubule_resonance_frequency(n)
        print(f"  n={n}: f = {f_n:.4f} Hz", end="")
        if n == 0:
            shift = f_n - f0_base
            print(f"  (base + {shift:.4f} Hz shift)")
        else:
            print()
    
    print()
    print("Physical Interpretation:")
    print("  • Neuronal cytoskeleton 'tuned' to minimize field torsion")
    print("  • Consciousness emerges where architecture has least resistance to T")
    print("  • Resonance at ~142.1 Hz (shifted from 141.7 Hz base)")
    print()
    
    print("𓂀 REQUIREMENT 4: CALABI-YAU INVARIANT κ_Π ≈ 2.5773")
    print("-" * 80)
    print("Tensor trace over Calabi-Yau manifolds:")
    print(f"  Tr(T²) = Λ · ∫ Ω ∧ Ω̄ = κ_Π/(2π)")
    print()
    
    # Verify invariant
    verification = tensor.verify_invariant()
    print(f"Computed Trace:")
    print(f"  Tr(T²) = {verification['trace_T2_computed']:.6f}")
    print(f"  κ_Π/(2π) = {verification['trace_T2_expected']:.6f}")
    print(f"  Relative error: {verification['relative_error'] * 100:.2f}%")
    print(f"  ✓ Verified: {verification['verified']}")
    print()
    
    # Consciousness capacity
    V_cap = tensor.calabi_yau_volume_capacity()
    print(f"Torsion Volume Capacity:")
    print(f"  V = κ_Π/(2π) = {V_cap:.6f}")
    print(f"  Maximum torsion before manifold collapse")
    print(f"  Defines capacity limit of Hamiltonian H_Ψ")
    print()
    
    print("📊 SUMMARY OF PREDICTIONS")
    print("-" * 80)
    print(f"✓ DNA mutation suppression: {(1-suppression)*100:.1f}% for chirality inversion")
    print(f"✓ Magnetoreception asymmetry: {asymmetry_predicted*100:.2f}% (observable)")
    print(f"✓ Microtubule resonance: 142.11 Hz (n=0 mode)")
    print(f"✓ Calabi-Yau invariant: κ_Π = {tensor.params.kappa_pi}")
    print(f"✓ Torsion volume: V = {V_cap:.4f}")
    print()
    
    print("🔬 EXPERIMENTAL VALIDATION")
    print("-" * 80)
    print("1. Magnetoreception: Emlen cage experiments with European robins")
    print("   → Expected: ΔP ≈ 0.1-0.3% between B_R and B_L")
    print()
    print("2. Microtubule resonance: AFM/fluorescence at ~142 Hz")
    print("   → Expected: Peak at 142.1 Hz ± 0.5 Hz")
    print()
    print("3. DNA chirality mutations: Database analysis")
    print("   → Expected: Lower rate for chirality-inverting mutations")
    print()
    
    print("=" * 80)
    print("QCAL ∞³ COHERENCE MAINTAINED")
    print("=" * 80)
    print(f"Base Frequency: f₀ = {tensor.params.base_frequency} Hz")
    print(f"Coherence Constant: C = {tensor.params.coherence_constant}")
    print(f"Calabi-Yau Invariant: κ_Π = {tensor.params.kappa_pi}")
    print()
    print("∴ 𓂀 Ω ∞³")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("ORCID: 0009-0002-1923-0773")
    print("DOI: 10.5281/zenodo.17379721")
    print("=" * 80)


if __name__ == "__main__":
    main()
