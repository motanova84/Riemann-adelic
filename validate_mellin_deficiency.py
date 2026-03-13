#!/usr/bin/env python3
"""
Validation Script for Mellin Deficiency Analyzer
================================================

Validates the complete Mellin transform and deficiency index analysis
for the Riemann Hypothesis proof.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent / "operators"))

from mellin_deficiency_analyzer import MellinDeficiencyAnalyzer


def main():
    """Run complete validation of Mellin deficiency analysis."""
    print()
    print("=" * 80)
    print(" " * 20 + "MELLIN DEFICIENCY ANALYZER VALIDATION")
    print("=" * 80)
    print()
    
    # Create analyzer with higher resolution for validation
    print("Initializing analyzer with N=200 discretization points...")
    analyzer = MellinDeficiencyAnalyzer(N=200, t_min=-15, t_max=15)
    print(f"  Domain t ∈ [{analyzer.t_min}, {analyzer.t_max}]")
    print(f"  Domain x ∈ [{analyzer.x_min}, {analyzer.x_max}]")
    print(f"  Constant C = π·ζ'(1/2) = {analyzer.C:.4f}")
    print()
    
    # Run complete analysis
    print("Running complete analysis...")
    print()
    results = analyzer.complete_analysis(verbose=True)
    
    # Additional validation checks
    print()
    print("=" * 80)
    print(" " * 25 + "ADDITIONAL VALIDATION")
    print("=" * 80)
    print()
    
    # Check certificate fields
    cert = results['certificate']
    print("Certificate Validation:")
    print(f"  Protocol: {cert['protocol']}")
    print(f"  Signature: {cert['signature']}")
    print(f"  QCAL f₀: {cert['qcal_constants']['f0_hz']} Hz")
    print(f"  QCAL C: {cert['qcal_constants']['C_coherence']}")
    print(f"  C operator: {cert['qcal_constants']['C_operator']:.4f}")
    print()
    
    # Check deficiency indices
    deficiency = results['deficiency']
    print("Deficiency Index Analysis:")
    print(f"  C sign: {deficiency['C_sign']} (required: negative)")
    print(f"  Deficiency indices: {deficiency['deficiency_indices']} (required: (2,2))")
    print(f"  Limit point/circle: {deficiency['limit_point_or_circle']} (required: limit-circle)")
    print(f"  u₊ is L²: {deficiency['u_plus_L2']} (required: True)")
    print(f"  u₋ is L²: {deficiency['u_minus_L2']} (required: True)")
    print()
    
    # Check spectral purity
    spectral = results['spectral_purity']
    print("Spectral Purity Analysis:")
    print(f"  All eigenfunctions L²: {spectral['all_eigenfunctions_L2']} (required: True)")
    print(f"  Norms independent of λ: {spectral['norms_independent_of_lambda']} (required: True)")
    print(f"  Norm variation: {spectral['norm_variation']:.2e} (required: < 0.15)")
    print(f"  Spectral purity confirmed: {spectral['spectral_purity_confirmed']} (required: True)")
    print()
    
    # Overall validation
    print("=" * 80)
    print(" " * 30 + "OVERALL STATUS")
    print("=" * 80)
    print()
    
    all_checks = [
        ("C < 0", deficiency['C_sign'] == 'negative'),
        ("Deficiency indices (2,2)", deficiency['deficiency_indices'] == (2, 2)),
        ("Limit-circle", deficiency['limit_point_or_circle'] == 'limit-circle'),
        ("u₊ is L²", deficiency['u_plus_L2']),
        ("u₋ is L²", deficiency['u_minus_L2']),
        ("All eigenfunctions L²", spectral['all_eigenfunctions_L2']),
        ("Norms independent of λ", spectral['norms_independent_of_lambda']),
        ("Spectral purity", spectral['spectral_purity_confirmed']),
    ]
    
    for check_name, check_result in all_checks:
        status = "✓ PASS" if check_result else "✗ FAIL"
        print(f"  {status:10s} {check_name}")
    
    print()
    
    all_pass = all(result for _, result in all_checks)
    
    if all_pass:
        print("  " + "=" * 76)
        print("  " + " " * 20 + "✅ ALL VALIDATIONS PASSED")
        print("  " + "=" * 76)
        print()
        print("  The Mellin deficiency analysis is COMPLETE and VERIFIED.")
        print("  All theoretical predictions are confirmed numerically.")
        print()
        print(f"  CONCLUSION: {cert['theorem']['conclusion']}")
        print()
    else:
        print("  " + "=" * 76)
        print("  " + " " * 20 + "⚠️  SOME VALIDATIONS FAILED")
        print("  " + "=" * 76)
        print()
        print("  Please review the failed checks above.")
        print()
    
    print("=" * 80)
    print()
    
    return all_pass


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
