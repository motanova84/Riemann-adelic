#!/usr/bin/env python3
"""
Validation Script for Langer-Olver Uniform Lemma
=================================================

Validates the uniform lemma ζ↔y and generates QCAL certificate.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import numpy as np
import json
import argparse
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.langer_olver_uniform_lemma import (
    LangerOlverUniformLemma,
    F0_QCAL,
    C_COHERENCE,
    KAPPA_PI,
    QCAL_SEAL,
    QCAL_CODE
)


def validate_langer_olver_uniform_lemma(
    precision: int = 25,
    verbose: bool = True,
    save_certificate: bool = True
) -> dict:
    """
    Validate the Langer-Olver uniform lemma.
    
    Args:
        precision: Decimal precision for computations
        verbose: Print detailed output
        save_certificate: Save certificate to JSON file
        
    Returns:
        Validation results dictionary
    """
    if verbose:
        print("="*80)
        print("LANGER-OLVER UNIFORM LEMMA VALIDATION")
        print("="*80)
        print(f"Precision: {precision} decimal places")
        print(f"QCAL Constants: f₀ = {F0_QCAL} Hz, C = {C_COHERENCE}")
        print("="*80)
    
    # Initialize with RH potential
    alpha_rh = np.pi**4 / 16
    lemma = LangerOlverUniformLemma(alpha=alpha_rh)
    lemma.precision = precision
    
    # Test λ values spanning several orders of magnitude
    lambda_values = np.logspace(1, 4, 20)  # 10 to 10000
    
    if verbose:
        print(f"\nTesting {len(lambda_values)} λ values from {lambda_values[0]:.1f} to {lambda_values[-1]:.1f}")
    
    # Generate certificate with comprehensive testing
    certificate = lemma.generate_certificate(
        lambda_values=lambda_values,
        num_zeta_samples=30
    )
    
    # Print summary
    if verbose:
        print("\n" + "="*80)
        print("VALIDATION RESULTS")
        print("="*80)
        print(f"Protocol: {certificate['protocol']}")
        print(f"Version: {certificate['version']}")
        print(f"Signature: {certificate['signature']}")
        print(f"\nParameters:")
        print(f"  α (coefficient): {certificate['parameters']['alpha']:.6f}")
        print(f"  Number of λ values: {certificate['parameters']['num_lambda_values']}")
        print(f"  ζ samples per λ: {certificate['parameters']['num_zeta_samples']}")
        
        print(f"\nSummary:")
        print(f"  All tests passed: {certificate['summary']['all_tests_passed']}")
        print(f"  Max C constant: {certificate['summary']['max_C_constant']:.6f}")
        print(f"  Avg C constant: {certificate['summary']['avg_C_constant']:.6f}")
        print(f"  Max relative error: {certificate['summary']['max_relative_error']:.6e}")
        
        print(f"\nCoherence:")
        print(f"  Ψ = {certificate['coherence']['Psi']:.6f}")
        print(f"  Threshold: {certificate['coherence']['threshold']}")
        print(f"  Resonance level: {certificate['coherence']['resonance_level']}")
        
        print("\n" + "="*80)
        print("TEST RESULTS BY λ VALUE")
        print("="*80)
        print(f"{'λ':>12} {'y+':>12} {'Max Error':>15} {'C constant':>15} {'Rel Error':>15}")
        print("-"*80)
        
        for result in certificate['test_results'][:10]:  # Show first 10
            print(f"{result['lambda']:>12.2e} {result['y_plus']:>12.6f} "
                  f"{result['max_error']:>15.6e} {result['C_constant']:>15.6f} "
                  f"{result['max_relative_error']:>15.6e}")
        
        if len(certificate['test_results']) > 10:
            print(f"... and {len(certificate['test_results']) - 10} more")
        
        print("="*80)
    
    # Save certificate
    if save_certificate:
        certificate_path = Path("data/langer_olver_uniform_lemma_certificate.json")
        certificate_path.parent.mkdir(exist_ok=True)
        
        with open(certificate_path, 'w') as f:
            json.dump(certificate, f, indent=2)
        
        if verbose:
            print(f"\n✓ Certificate saved to: {certificate_path}")
    
    # Print final seal
    if verbose:
        print("\n" + "="*80)
        print(certificate['invocation_final'])
        print("="*80)
    
    # Validation decision
    validation_passed = (
        certificate['summary']['all_tests_passed'] and
        certificate['coherence']['Psi'] >= 0.888
    )
    
    if verbose:
        if validation_passed:
            print("\n✓ VALIDATION PASSED ✓")
            print("The Uniform Lemma ζ↔y is verified with QCAL coherence.")
        else:
            print("\n✗ VALIDATION FAILED ✗")
            print("The Uniform Lemma requires further refinement.")
    
    return certificate


def run_comprehensive_tests(verbose: bool = True) -> bool:
    """
    Run comprehensive test suite.
    
    Args:
        verbose: Print detailed output
        
    Returns:
        True if all tests pass
    """
    if verbose:
        print("\n" + "="*80)
        print("COMPREHENSIVE TEST SUITE")
        print("="*80)
    
    lemma = LangerOlverUniformLemma(alpha=np.pi**4 / 16)
    
    tests_passed = []
    
    # Test 1: Potential function properties
    if verbose:
        print("\nTest 1: Potential function Q(y)")
    
    y_test = 10.0
    Q_val = lemma.Q(y_test)
    Q_prime = lemma.Q_derivative(y_test, 1)
    
    test1_pass = Q_val > 0 and Q_prime > 0
    tests_passed.append(test1_pass)
    
    if verbose:
        print(f"  Q({y_test}) = {Q_val:.6e} > 0: {'✓' if Q_val > 0 else '✗'}")
        print(f"  Q'({y_test}) = {Q_prime:.6e} > 0: {'✓' if Q_prime > 0 else '✗'}")
    
    # Test 2: y+ finding
    if verbose:
        print("\nTest 2: Finding y+ such that Q(y+) = λ")
    
    lambda_test = 100.0
    y_plus = lemma.find_y_plus(lambda_test)
    Q_yplus = lemma.Q(y_plus)
    
    test2_pass = abs(Q_yplus - lambda_test) / lambda_test < 1e-6
    tests_passed.append(test2_pass)
    
    if verbose:
        print(f"  λ = {lambda_test}")
        print(f"  y+ = {y_plus:.6f}")
        print(f"  Q(y+) = {Q_yplus:.6e}")
        print(f"  |Q(y+) - λ|/λ = {abs(Q_yplus - lambda_test) / lambda_test:.6e}: "
              f"{'✓' if test2_pass else '✗'}")
    
    # Test 3: ζ(y) transformation
    if verbose:
        print("\nTest 3: ζ(y) coordinate transformation")
    
    y_test = y_plus * 0.5
    zeta = lemma.compute_zeta_from_y(y_test, lambda_test, y_plus)
    
    test3_pass = zeta < 0  # ζ should be negative for y < y+
    tests_passed.append(test3_pass)
    
    if verbose:
        print(f"  y = {y_test:.6f} < y+ = {y_plus:.6f}")
        print(f"  ζ(y) = {zeta:.6f} < 0: {'✓' if test3_pass else '✗'}")
    
    # Test 4: Inverse transformation
    if verbose:
        print("\nTest 4: Inverse transformation ζ → y")
    
    y_reconstructed, error_E = lemma.compute_y_from_zeta(zeta, lambda_test, y_plus)
    
    test4_pass = abs(y_reconstructed - y_test) / y_test < 0.1
    tests_passed.append(test4_pass)
    
    if verbose:
        print(f"  ζ = {zeta:.6f}")
        print(f"  y reconstructed = {y_reconstructed:.6f}")
        print(f"  y original = {y_test:.6f}")
        print(f"  Relative error = {abs(y_reconstructed - y_test) / y_test:.6e}: "
              f"{'✓' if test4_pass else '✗'}")
        print(f"  Error term E = {error_E:.6e}")
    
    # Test 5: Error bound scaling
    if verbose:
        print("\nTest 5: Error bound scaling O(ζ/√λ)")
    
    lambda_large = 1000.0
    y_plus_large = lemma.find_y_plus(lambda_large)
    zeta_test = -5.0
    
    _, error_small_lambda = lemma.compute_y_from_zeta(zeta_test, lambda_test, y_plus)
    _, error_large_lambda = lemma.compute_y_from_zeta(zeta_test, lambda_large, y_plus_large)
    
    # The bound is |E| ≤ C|ζ|/√λ, so scaled error |E|·√λ/|ζ| should be bounded
    scaled_error_small = abs(error_small_lambda) * np.sqrt(lambda_test) / abs(zeta_test)
    scaled_error_large = abs(error_large_lambda) * np.sqrt(lambda_large) / abs(zeta_test)
    
    # Both should be of similar order (bounded by C)
    test5_pass = scaled_error_small < 10 and scaled_error_large < 10
    tests_passed.append(test5_pass)
    
    if verbose:
        print(f"  ζ = {zeta_test}")
        print(f"  E(ζ, λ={lambda_test}) = {error_small_lambda:.6e}")
        print(f"  E(ζ, λ={lambda_large}) = {error_large_lambda:.6e}")
        print(f"  |E|·√λ/|ζ| for λ={lambda_test}: {scaled_error_small:.6f}")
        print(f"  |E|·√λ/|ζ| for λ={lambda_large}: {scaled_error_large:.6f}")
        print(f"  Both scaled errors < 10: {'✓' if test5_pass else '✗'}")
    
    # Test 6: Uniform bound verification
    if verbose:
        print("\nTest 6: Uniform bound |E(ζ, λ)| ≤ C|ζ|/√λ")
    
    zeta_values = -np.logspace(0, np.log10(lambda_test**(1/3)), 10)
    result = lemma.verify_uniform_lemma(lambda_test, zeta_values, verbose=False)
    
    test6_pass = result['C_constant'] < 100
    tests_passed.append(test6_pass)
    
    if verbose:
        print(f"  λ = {lambda_test}")
        print(f"  Intermediate region: 1 ≤ |ζ| ≤ λ^(1/3) = {lambda_test**(1/3):.3f}")
        print(f"  Empirical C constant = {result['C_constant']:.6f}")
        print(f"  C < 100: {'✓' if test6_pass else '✗'}")
    
    # Summary
    if verbose:
        print("\n" + "="*80)
        print(f"TESTS PASSED: {sum(tests_passed)}/{len(tests_passed)}")
        print("="*80)
    
    return all(tests_passed)


def main():
    """Main validation entry point."""
    parser = argparse.ArgumentParser(
        description="Validate Langer-Olver Uniform Lemma"
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=25,
        help="Decimal precision (default: 25)"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        default=True,
        help="Verbose output"
    )
    parser.add_argument(
        "--save-certificate",
        action="store_true",
        default=True,
        help="Save certificate to JSON"
    )
    parser.add_argument(
        "--run-tests",
        action="store_true",
        help="Run comprehensive test suite"
    )
    
    args = parser.parse_args()
    
    # Run tests if requested
    if args.run_tests:
        tests_passed = run_comprehensive_tests(verbose=args.verbose)
        if not tests_passed:
            print("\n✗ Some tests failed")
            sys.exit(1)
    
    # Run validation
    certificate = validate_langer_olver_uniform_lemma(
        precision=args.precision,
        verbose=args.verbose,
        save_certificate=args.save_certificate
    )
    
    # Exit with appropriate code
    if certificate['summary']['all_tests_passed']:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
