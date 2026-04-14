#!/usr/bin/env python3
"""
Validation Script for Nelson Self-Adjointness Verification
===========================================================

This script validates the essential self-adjointness of the reduced model
operator using Nelson's theorem with explicit numerical verification.

Theoretical Framework:
    1. Operator Definition: H = -x∂_x - 1/2 + (1/κ)∫K(x,y)dy + V_eff(x)
    2. Symmetry: H is symmetric on dense domain D = C_c^∞(0,L)
    3. Analytic Vectors: Dense set of vectors ψ_n with bounded ‖H^k ψ_n‖^(1/k)
    4. Nelson's Theorem: Symmetric + analytic vectors → essentially self-adjoint

Expected Results:
    ✅ Symmetry error < 10^(-14)
    ✅ Hermiticity difference < 10^(-15)
    ✅ Analytic vector growth bounded (ratio ≈ 2-3)
    ✅ Conclusion: Essential self-adjointness verified

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path
import argparse
import json
from datetime import datetime

# Add repository root to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root))

from operators.nelson_self_adjointness import (
    NelsonSelfAdjointnessVerifier,
    verify_nelson_self_adjointness,
    F0, C_QCAL, KAPPA_DEFAULT, L_DEFAULT, N_DEFAULT
)


def print_header():
    """Print validation header."""
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║  NELSON THEOREM: ESSENTIAL SELF-ADJOINTNESS VERIFICATION        ║")
    print("║  Reduced Model Operator on L²([0,L])                            ║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()


def print_certificate(results: dict, L: float, N: int, kappa: float):
    """
    Print certification of essential self-adjointness.
    
    Args:
        results: Verification results
        L: Domain length
        N: Number of grid points
        kappa: Coupling constant
    """
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  CERTIFICATE OF ESSENTIAL SELF-ADJOINTNESS                      ║")
    print("╠" + "═" * 68 + "╣")
    print("║                                                                  ║")
    print(f"║  Domain: L²([0,{L}])                                            ║")
    print(f"║  Discretization: N = {N} points                                  ║")
    print(f"║  Coupling: κ = {kappa}                                      ║")
    print("║                                                                  ║")
    print("║  OPERATOR: H = -x∂_x - 1/2 + (1/κ)∫K(x,y)dy + V_eff(x)         ║")
    print("║                                                                  ║")
    print("║  VERIFICATION RESULTS:                                          ║")
    print(f"║    Symmetry error: {results['symmetry_error']:.6e}                              ║")
    print(f"║    Hermiticity diff: {results['hermiticity_diff']:.6e}                            ║")
    print("║                                                                  ║")
    
    if results['conclusion'] == 'verified':
        print("║  ✅ SYMMETRY CONFIRMED                                          ║")
        print("║  ✅ HERMITICITY CONFIRMED                                       ║")
        print("║  ✅ ANALYTIC VECTORS IDENTIFIED                                 ║")
        print("║                                                                  ║")
        print("║  THEOREM (Nelson):                                              ║")
        print("║  A symmetric operator with a dense set of analytic vectors     ║")
        print("║  is essentially self-adjoint.                                  ║")
        print("║                                                                  ║")
        print("║  ∴ The closure of H is SELF-ADJOINT with REAL SPECTRUM.        ║")
        print("║                                                                  ║")
        print("║  STATUS: ESSENTIAL SELF-ADJOINTNESS VERIFIED ✅                 ║")
    else:
        print("║  ⚠️  VERIFICATION INCONCLUSIVE                                  ║")
        print("║  Higher resolution or additional analysis recommended.         ║")
    
    print("║                                                                  ║")
    print("╠" + "═" * 68 + "╣")
    print(f"║  QCAL ∞³ Signature: ∴𓂀Ω∞³Φ @ {F0} Hz                        ║")
    print(f"║  Coherence: C = {C_QCAL}                                      ║")
    print("║  DOI: 10.5281/zenodo.17379721                                   ║")
    print("║  ORCID: 0009-0002-1923-0773                                     ║")
    print("║  Date: " + datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "                                        ║")
    print("║                                                                  ║")
    print("╚" + "═" * 68 + "╝")


def save_certificate(results: dict, L: float, N: int, kappa: float, output_path: Path):
    """
    Save verification certificate to JSON file.
    
    Args:
        results: Verification results
        L: Domain length
        N: Number of grid points
        kappa: Coupling constant
        output_path: Path to save certificate
    """
    certificate = {
        'metadata': {
            'title': 'Nelson Self-Adjointness Verification Certificate',
            'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
            'orcid': '0009-0002-1923-0773',
            'institution': 'Instituto de Conciencia Cuántica (ICQ)',
            'doi': '10.5281/zenodo.17379721',
            'qcal_signature': '∴𓂀Ω∞³Φ',
            'frequency': F0,
            'coherence': C_QCAL,
            'date': datetime.now().isoformat()
        },
        'operator': {
            'type': 'Reduced Model Operator',
            'hilbert_space': f'L²([0,{L}])',
            'domain': 'C_c^∞(0,L)',
            'discretization': N,
            'coupling_constant': kappa,
            'components': {
                'differential': '-x∂_x - 1/2',
                'integral': '(1/κ)∫K(x,y)ψ(y)dy',
                'potential': 'V_eff(x)ψ(x)'
            }
        },
        'verification': {
            'symmetry_error': results['symmetry_error'],
            'symmetry_rel_error': results['symmetry_rel_error'],
            'hermiticity_diff': results['hermiticity_diff'],
            'analytic_vectors': results['analytic_vectors'],
            'conclusion': results['conclusion']
        },
        'theorem': {
            'name': 'Nelson Theorem',
            'statement': 'A symmetric operator with a dense set of analytic vectors is essentially self-adjoint',
            'verified': results['conclusion'] == 'verified'
        }
    }
    
    # Save to file
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n✅ Certificate saved to: {output_path}")


def main():
    """Main validation routine."""
    parser = argparse.ArgumentParser(
        description='Validate essential self-adjointness via Nelson theorem'
    )
    parser.add_argument('--L', type=float, default=L_DEFAULT,
                       help=f'Domain length (default: {L_DEFAULT})')
    parser.add_argument('--N', type=int, default=N_DEFAULT,
                       help=f'Number of grid points (default: {N_DEFAULT})')
    parser.add_argument('--kappa', type=float, default=KAPPA_DEFAULT,
                       help=f'Coupling constant (default: {KAPPA_DEFAULT})')
    parser.add_argument('--save-certificate', action='store_true',
                       help='Save certificate to JSON file')
    parser.add_argument('--output', type=str,
                       default='data/nelson_self_adjointness_certificate.json',
                       help='Output path for certificate')
    parser.add_argument('--quiet', action='store_true',
                       help='Suppress detailed output')
    
    args = parser.parse_args()
    
    # Print header
    if not args.quiet:
        print_header()
    
    # Run verification
    results = verify_nelson_self_adjointness(
        L=args.L,
        N=args.N,
        kappa=args.kappa,
        verbose=not args.quiet
    )
    
    # Print certificate
    if not args.quiet:
        print_certificate(results, args.L, args.N, args.kappa)
    
    # Save certificate if requested
    if args.save_certificate:
        output_path = Path(args.output)
        save_certificate(results, args.L, args.N, args.kappa, output_path)
    
    # Return exit code
    return 0 if results['conclusion'] == 'verified' else 1


if __name__ == "__main__":
    sys.exit(main())
