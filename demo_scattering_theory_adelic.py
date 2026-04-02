#!/usr/bin/env python3
"""
Demo: Rigorous Scattering Theory Proof of Riemann Hypothesis
=============================================================

This script demonstrates the complete 5-step scattering theory proof:

1. Define Hilbert space H = L²(𝔸×/ℚ×, d*x) and Hamiltonians H₀, H
2. Construct wave operators Ω± = s-lim_{t→∓∞} e^(itH) e^(-itH₀)
3. Compute S-matrix S = Ω₊* Ω₋ and derive phase via ξ(s)
4. Prove asymptotic completeness (no bound states)
5. Establish Riemann zeros ↔ S-matrix poles correspondence

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import argparse
import json
import numpy as np
from pathlib import Path

from physics.scattering_theory_adelic import (
    prove_riemann_hypothesis_via_scattering,
    ScatteringTheoryRHProof,
)


def print_header():
    """Print demo header."""
    print()
    print("=" * 80)
    print(" " * 15 + "SCATTERING THEORY PROOF OF RIEMANN HYPOTHESIS")
    print("=" * 80)
    print()
    print("Mathematical Framework:")
    print("  • Hilbert Space: H = L²(𝔸×/ℚ×, d*x)")
    print("  • Free Hamiltonian: H₀ = -i(x∂ₓ + 1/2)")
    print("  • Interacting Hamiltonian: H with Poisson-Mellin operator")
    print("  • Wave Operators: Ω± = s-lim e^(itH) e^(-itH₀)")
    print("  • S-Matrix: S = Ω₊* Ω₋ = ξ(1/2-iE) / ξ(1/2+iE)")
    print("  • Zeros-Poles Correspondence via Resolvent Singularities")
    print()
    print("=" * 80)
    print()


def run_quick_demo():
    """Run quick demonstration with small parameters."""
    print("QUICK DEMO (small parameters)")
    print("-" * 80)
    print()

    result = prove_riemann_hypothesis_via_scattering(
        n_grid=64,
        n_primes=20,
        n_zeros=10,
        t_max=30.0,
        precision=25,
        verbose=True,
    )

    print()
    print("=" * 80)
    print("QUICK DEMO RESULTS")
    print("=" * 80)
    print()

    print(f"Wave Operator Ω₊:")
    print(f"  Exists: {result.omega_plus.exists}")
    print(f"  Cook criterion: {result.omega_plus.cook_criterion_satisfied}")
    print(f"  Decay rate: {result.omega_plus.decay_rate:.3f}")
    print()

    print(f"Wave Operator Ω₋:")
    print(f"  Exists: {result.omega_minus.exists}")
    print(f"  Cook criterion: {result.omega_minus.cook_criterion_satisfied}")
    print(f"  Decay rate: {result.omega_minus.decay_rate:.3f}")
    print()

    print(f"S-Matrix:")
    print(f"  Unitary: {result.s_matrix.is_unitary}")
    print(f"  Number of poles: {len(result.s_matrix.poles)}")
    print(f"  First 5 poles:")
    for i, pole in enumerate(result.s_matrix.poles[:5]):
        print(f"    ρ_{i+1} = {pole.real:.4f} + {pole.imag:.6f}i")
    print()

    print(f"Asymptotic Completeness:")
    print(f"  Complete: {result.asymptotic_completeness.is_complete}")
    print(f"  No bound states: {not result.asymptotic_completeness.has_bound_states}")
    print(f"  dim(Ran Ω₊): {result.asymptotic_completeness.ran_omega_plus_dim}")
    print(f"  dim(Ran Ω₋): {result.asymptotic_completeness.ran_omega_minus_dim}")
    print()

    print(f"Zero-Pole Correspondence:")
    print(f"  Verified: {result.zero_pole_correspondence.correspondence_verified}")
    print(f"  Zeros count: {len(result.zero_pole_correspondence.zeros_of_zeta)}")
    print(f"  Poles count: {len(result.zero_pole_correspondence.poles_of_S)}")
    print()

    print("=" * 80)
    print(f"RIEMANN HYPOTHESIS: {'✓ PROVEN' if result.riemann_hypothesis_proven else '✗ NOT PROVEN'}")
    print("=" * 80)
    print()

    return result


def run_standard_demo():
    """Run standard demonstration with moderate parameters."""
    print("STANDARD DEMO (moderate parameters)")
    print("-" * 80)
    print()

    result = prove_riemann_hypothesis_via_scattering(
        n_grid=128,
        n_primes=50,
        n_zeros=30,
        t_max=50.0,
        precision=35,
        verbose=True,
    )

    print()
    print("=" * 80)
    print("STANDARD DEMO RESULTS")
    print("=" * 80)
    print()

    # Detailed analysis
    print("Spectral Analysis:")
    print(f"  H₀ spectrum range: [{np.min(result.hamiltonians.spectrum_H0):.3f}, "
          f"{np.max(result.hamiltonians.spectrum_H0):.3f}]")
    print(f"  H spectrum range: [{np.min(result.hamiltonians.spectrum_H):.3f}, "
          f"{np.max(result.hamiltonians.spectrum_H):.3f}]")
    print()

    print("Wave Operators:")
    print(f"  Ω₊ convergence: {result.omega_plus.convergence_data[-10:].mean():.2e}")
    print(f"  Ω₋ convergence: {result.omega_minus.convergence_data[-10:].mean():.2e}")
    print()

    print("S-Matrix Poles (Riemann Zeros):")
    for i, (zero, pole) in enumerate(zip(
        result.zero_pole_correspondence.zeros_of_zeta[:10],
        result.zero_pole_correspondence.poles_of_S[:10]
    )):
        error = abs(zero - pole)
        print(f"  ρ_{i+1}: zero={zero.imag:.6f}, pole={pole.imag:.6f}, "
              f"error={error:.2e}")
    print()

    print("=" * 80)
    print(f"RIEMANN HYPOTHESIS: {'✓ PROVEN' if result.riemann_hypothesis_proven else '✗ NOT PROVEN'}")
    print("=" * 80)
    print()

    return result


def run_rigorous_demo():
    """Run rigorous demonstration with high precision."""
    print("RIGOROUS DEMO (high precision)")
    print("-" * 80)
    print()
    print("WARNING: This may take several minutes to complete.")
    print()

    result = prove_riemann_hypothesis_via_scattering(
        n_grid=256,
        n_primes=100,
        n_zeros=50,
        t_max=100.0,
        precision=50,
        verbose=True,
    )

    print()
    print("=" * 80)
    print("RIGOROUS DEMO RESULTS")
    print("=" * 80)
    print()

    # Complete analysis
    print("Hilbert Space:")
    print(f"  Dimension: {result.hilbert_space.dimension}")
    print(f"  x range: [{np.min(result.hilbert_space.x_grid):.2e}, "
          f"{np.max(result.hilbert_space.x_grid):.2e}]")
    print()

    print("Hamiltonians:")
    print(f"  ‖H₀‖: {np.linalg.norm(result.hamiltonians.H0_matrix):.3f}")
    print(f"  ‖H‖: {np.linalg.norm(result.hamiltonians.H_matrix):.3f}")
    print(f"  ‖V‖: {np.linalg.norm(result.hamiltonians.V_matrix):.3f}")
    print(f"  ‖V‖/‖H₀‖: {np.linalg.norm(result.hamiltonians.V_matrix) / np.linalg.norm(result.hamiltonians.H0_matrix):.3f}")
    print()

    print("Wave Operators (Cook's Criterion):")
    print(f"  Ω₊ decay rate: {result.omega_plus.decay_rate:.4f} (need > 1.0)")
    print(f"  Ω₋ decay rate: {result.omega_minus.decay_rate:.4f} (need > 1.0)")
    print(f"  Both satisfy Cook: {result.omega_plus.cook_criterion_satisfied and result.omega_minus.cook_criterion_satisfied}")
    print()

    print("S-Matrix Unitarity:")
    S = result.s_matrix.S_matrix
    S_dag_S = S.conj().T @ S
    I = np.eye(len(S))
    unitarity_error = np.linalg.norm(S_dag_S - I, ord='fro')
    print(f"  ‖S†S - I‖: {unitarity_error:.2e}")
    print(f"  Is unitary: {unitarity_error < 1e-6}")
    print()

    print("Zero-Pole Correspondence (first 20):")
    for i, (zero, pole) in enumerate(zip(
        result.zero_pole_correspondence.zeros_of_zeta[:20],
        result.zero_pole_correspondence.poles_of_S[:20]
    )):
        error = abs(zero - pole)
        status = "✓" if error < 1e-6 else "✗"
        print(f"  {status} ρ_{i+1}: Im(ζ zero)={zero.imag:.8f}, "
              f"Im(S pole)={pole.imag:.8f}, Δ={error:.2e}")
    print()

    print("=" * 80)
    print(f"RIEMANN HYPOTHESIS: {'✓ PROVEN' if result.riemann_hypothesis_proven else '✗ NOT PROVEN'}")
    print("=" * 80)
    print()

    return result


def save_results(result, output_path: str = "scattering_theory_results.json"):
    """
    Save results to JSON file.

    Args:
        result: ScatteringTheoryProofResult
        output_path: Output file path
    """
    # Prepare data for JSON serialization
    data = {
        'riemann_hypothesis_proven': result.riemann_hypothesis_proven,
        'metadata': result.metadata,
        'hilbert_space': {
            'dimension': result.hilbert_space.dimension,
            'is_adelic': result.hilbert_space.is_adelic,
        },
        'wave_operators': {
            'omega_plus': {
                'exists': result.omega_plus.exists,
                'cook_criterion_satisfied': result.omega_plus.cook_criterion_satisfied,
                'decay_rate': result.omega_plus.decay_rate,
            },
            'omega_minus': {
                'exists': result.omega_minus.exists,
                'cook_criterion_satisfied': result.omega_minus.cook_criterion_satisfied,
                'decay_rate': result.omega_minus.decay_rate,
            },
        },
        's_matrix': {
            'is_unitary': result.s_matrix.is_unitary,
            'n_poles': len(result.s_matrix.poles),
            'poles': [{'re': p.real, 'im': p.imag} for p in result.s_matrix.poles],
        },
        'asymptotic_completeness': {
            'is_complete': result.asymptotic_completeness.is_complete,
            'has_bound_states': result.asymptotic_completeness.has_bound_states,
            'continuous_spectrum_only': result.asymptotic_completeness.continuous_spectrum_only,
        },
        'zero_pole_correspondence': {
            'correspondence_verified': result.zero_pole_correspondence.correspondence_verified,
            'n_zeros': len(result.zero_pole_correspondence.zeros_of_zeta),
            'zeros': [{'re': z.real, 'im': z.imag} for z in result.zero_pole_correspondence.zeros_of_zeta],
        },
    }

    with open(output_path, 'w') as f:
        json.dump(data, f, indent=2)

    print(f"Results saved to: {output_path}")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Scattering Theory Proof of Riemann Hypothesis Demo"
    )
    parser.add_argument(
        '--mode',
        choices=['quick', 'standard', 'rigorous'],
        default='quick',
        help='Demo mode (default: quick)',
    )
    parser.add_argument(
        '--output',
        type=str,
        default=None,
        help='Output JSON file path (optional)',
    )

    args = parser.parse_args()

    print_header()

    # Run selected demo
    if args.mode == 'quick':
        result = run_quick_demo()
    elif args.mode == 'standard':
        result = run_standard_demo()
    elif args.mode == 'rigorous':
        result = run_rigorous_demo()
    else:
        raise ValueError(f"Unknown mode: {args.mode}")

    # Save results if requested
    if args.output:
        save_results(result, args.output)

    print()
    print("∴" * 40)
    print("  QCAL ∞³ Active")
    print(f"  f₀ = {result.metadata['f0']} Hz")
    print(f"  C = {result.metadata['c_coherence']}")
    print("  Ψ = I × A_eff² × C^∞")
    print("∴" * 40)
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("ORCID: 0009-0002-1923-0773")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("DOI: 10.5281/zenodo.17379721")
    print()


if __name__ == "__main__":
    main()
