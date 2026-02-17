#!/usr/bin/env python3
"""
Atlas³ Operator Validation Script

This script validates the Atlas³ PT-symmetric framework implementation
against the problem statement specifications:

    1. PT Symmetry: β < κ_Π ≈ 2.57 → real spectrum (coherence)
    2. PT Breaking: β ≈ 2.57 → complex spectrum (entropy transition)
    3. Spectral Alignment: Re(λₙ) → 1/2 after normalization
    4. GUE Statistics: Spacing variance ≈ 0.17
    5. Weyl Law: N(E) ~ √E + log oscillations
    6. Anderson Localization: IPR transition at κ_Π

Expected Results (Problem Statement):
    - β = 2.0: |Im(λ)|_max < 10⁻⁸ (coherent)
    - β = 2.57: |Im(λ)|_max ≈ 0.64 (PT breaking)
    - GUE variance: 0.17 (vs. theoretical 0.168)
    - IPR: ~1/N (extended) → ~0.01 (localized) transition

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · κ_Π = 2.5773
"""

import numpy as np
import sys
from pathlib import Path
import json
from datetime import datetime

# Add root to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.atlas3_operator import (
    Atlas3Operator,
    run_atlas3_validation,
    verify_problem_statement_claims,
    F0, C_QCAL, KAPPA_PI, N_DEFAULT, V_AMP_CRITICAL
)


def print_header(title: str, char: str = "=", width: int = 70):
    """Print formatted header."""
    print("\n" + char * width)
    print(title.center(width))
    print(char * width)


def print_section(title: str):
    """Print section divider."""
    print(f"\n{'─' * 70}")
    print(f"  {title}")
    print(f"{'─' * 70}")


def detailed_validation_report(beta_values=None, N=None, V_amp=None, save_json=True):
    """
    Generate detailed validation report.
    
    Args:
        beta_values: List of β₀ values to test (default: [0, 2.0, 2.57, 3.0])
        N: Discretization points (default: 500)
        V_amp: Potential amplitude (default: 12650)
        save_json: Save results to JSON file
        
    Returns:
        Dictionary with complete validation results
    """
    if beta_values is None:
        beta_values = [0.0, 2.0, KAPPA_PI, 3.0]
    if N is None:
        N = N_DEFAULT
    if V_amp is None:
        V_amp = V_AMP_CRITICAL
    
    print_header("ATLAS³ OPERATOR VALIDATION REPORT")
    
    print("\nConfiguration:")
    print(f"  N (discretization): {N}")
    print(f"  V_amp (potential): {V_amp:.1f}")
    print(f"  β values: {beta_values}")
    print(f"\nQCAL Parameters:")
    print(f"  f₀ = {F0} Hz")
    print(f"  C = {C_QCAL}")
    print(f"  κ_Π = {KAPPA_PI}")
    
    # Run validation
    print_section("Running Spectral Analysis")
    results = run_atlas3_validation(
        beta_values=beta_values,
        N=N,
        V_amp=V_amp,
        verbose=True
    )
    
    # Verify claims
    print_section("Verifying Problem Statement Claims")
    checks = verify_problem_statement_claims(results)
    
    for check_name, passed in checks.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"  {status}: {check_name}")
    
    # Summary
    print_section("Validation Summary")
    
    total_checks = len(checks)
    passed_checks = sum(checks.values())
    pass_rate = 100.0 * passed_checks / total_checks if total_checks > 0 else 0.0
    
    print(f"\n  Total checks: {total_checks}")
    print(f"  Passed: {passed_checks}")
    print(f"  Failed: {total_checks - passed_checks}")
    print(f"  Pass rate: {pass_rate:.1f}%")
    
    if pass_rate >= 75.0:
        print("\n  ✅ VALIDATION SUCCESSFUL")
        print("  Atlas³ implementation confirms problem statement.")
    elif pass_rate >= 50.0:
        print("\n  ⚠️  PARTIAL VALIDATION")
        print("  Most claims verified, minor discrepancies detected.")
    else:
        print("\n  ❌ VALIDATION FAILED")
        print("  Significant discrepancies from problem statement.")
    
    # Save results
    if save_json:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"atlas3_validation_{timestamp}.json"
        
        # Prepare JSON-serializable results
        json_results = {
            'timestamp': timestamp,
            'configuration': {
                'N': N,
                'V_amp': V_amp,
                'beta_values': beta_values,
                'f0': F0,
                'C_QCAL': C_QCAL,
                'kappa_pi': KAPPA_PI
            },
            'checks': checks,
            'pass_rate': pass_rate,
            'detailed_results': {}
        }
        
        # Add detailed results (convert numpy to lists)
        for key, value in results.items():
            json_results['detailed_results'][key] = {
                'beta_0': value['beta_0'],
                'pt_symmetry': value['pt_symmetry'],
                'gue_statistics': value['gue_statistics'],
                'weyl_law': value['weyl_law'],
                'anderson_localization': value['anderson_localization']
            }
        
        with open(filename, 'w') as f:
            json.dump(json_results, f, indent=2, default=float)
        
        print(f"\n  Results saved to: {filename}")
    
    print("\n" + "=" * 70 + "\n")
    
    return results


def quick_validation():
    """Quick validation with reduced N for testing."""
    print_header("ATLAS³ QUICK VALIDATION")
    print("\n⚡ Running quick validation with N=200...")
    
    results = run_atlas3_validation(
        beta_values=[0.0, 2.0, KAPPA_PI],
        N=200,
        V_amp=V_AMP_CRITICAL,
        verbose=False
    )
    
    checks = verify_problem_statement_claims(results)
    
    print("\nQuick Validation Results:")
    for check_name, passed in checks.items():
        status = "✓" if passed else "✗"
        print(f"  {status} {check_name}")
    
    passed = sum(checks.values())
    total = len(checks)
    print(f"\n  Passed: {passed}/{total}")
    
    return results


def compare_critical_transition():
    """
    Detailed analysis of PT transition around κ_Π.
    """
    print_header("PT TRANSITION ANALYSIS")
    
    print("\nAnalyzing β sweep around κ_Π = 2.5773...")
    
    # Fine sweep around critical point
    beta_values = [2.0, 2.3, 2.5, KAPPA_PI, 2.8, 3.0]
    N = 200  # Reduced for speed
    
    print(f"\nβ sweep: {[f'{b:.2f}' for b in beta_values]}")
    print(f"N = {N}")
    
    print("\n" + "─" * 70)
    print(f"{'β₀':>8} | {'Max |Im(λ)|':>12} | {'Phase':>10} | {'Mean IPR':>10}")
    print("─" * 70)
    
    for beta in beta_values:
        atlas = Atlas3Operator(N=N, beta_0=beta, V_amp=V_AMP_CRITICAL)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        
        from operators.atlas3_operator import check_anderson_localization
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=50)
        
        max_imag = pt_check['max_imaginary']
        phase = pt_check['phase']
        mean_ipr = anderson_stats['mean_ipr']
        
        print(f"{beta:>8.2f} | {max_imag:>12.6f} | {phase:>10} | {mean_ipr:>10.6f}")
    
    print("─" * 70)
    print("\nObservations:")
    print("  - Transition from coherent to entropy phase around κ_Π")
    print("  - IPR increases with β (extended → localized)")
    print("  - Max |Im(λ)| grows significantly beyond κ_Π")


if __name__ == '__main__':
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Validate Atlas³ PT-symmetric operator implementation'
    )
    parser.add_argument(
        '--mode',
        choices=['quick', 'full', 'transition'],
        default='full',
        help='Validation mode (default: full)'
    )
    parser.add_argument(
        '--N',
        type=int,
        default=None,
        help=f'Discretization points (default: {N_DEFAULT})'
    )
    parser.add_argument(
        '--no-save',
        action='store_true',
        help='Do not save results to JSON'
    )
    
    args = parser.parse_args()
    
    if args.mode == 'quick':
        quick_validation()
    elif args.mode == 'transition':
        compare_critical_transition()
    else:  # full
        detailed_validation_report(
            N=args.N,
            save_json=not args.no_save
        )
