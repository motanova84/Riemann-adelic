#!/usr/bin/env python3
"""
Validation script for Atlas³ Symbol Calculus Integration

This script validates the integration of pseudodifferential symbol calculus
with the Atlas³ operator implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import numpy as np
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))

from atlas3_operator import Atlas3Operator, KAPPA_PI
from atlas3_symbol_calculus import (
    PseudodifferentialSymbol,
    WeylLawCalculator,
    validate_weyl_law_derivation
)


def validate_symbol_integration():
    """Validate integration of symbol calculus with Atlas³ operator."""
    
    print("=" * 80)
    print("Atlas³ Pseudodifferential Symbol Calculus Integration Validation")
    print("=" * 80)
    
    # Create operator
    print("\n1. Creating Atlas³ Operator")
    print("-" * 80)
    
    N = 500
    beta_0 = 2.0
    V_amp = 12650.0
    
    atlas = Atlas3Operator(N=N, beta_0=beta_0, V_amp=V_amp)
    print(f"  Operator created: N={N}, β₀={beta_0}, V_amp={V_amp}")
    
    # Compute spectrum
    print("\n2. Computing Spectrum")
    print("-" * 80)
    
    eigenvalues, eigenvectors = atlas.compute_spectrum()
    print(f"  Spectrum computed: {len(eigenvalues)} eigenvalues")
    print(f"  Energy range: [{eigenvalues.real.min():.2f}, {eigenvalues.real.max():.2f}]")
    
    # Check PT symmetry
    pt_check = atlas.check_pt_symmetry(eigenvalues)
    print(f"  PT symmetric: {pt_check['pt_symmetric']}")
    print(f"  Max |Im(λ)|: {pt_check['max_imaginary']:.6f}")
    
    # Get symbol calculus
    print("\n3. Symbol Calculus Framework")
    print("-" * 80)
    
    symbol_calc = atlas.get_symbol_calculus()
    
    if symbol_calc is None:
        print("  ❌ Symbol calculus not available")
        return False
    
    print("  ✅ Symbol calculus initialized")
    print(f"  Components: {list(symbol_calc.keys())}")
    
    # Validate Weyl law
    print("\n4. Weyl Law Validation from Symbol")
    print("-" * 80)
    
    weyl_validation = atlas.validate_weyl_law_from_symbol(eigenvalues)
    
    print(f"  E_max: {weyl_validation['E_max']:.2f}")
    print(f"  N (spectral count): {weyl_validation['N_spectral']}")
    print(f"  N (Weyl exact): {weyl_validation['N_weyl_exact']:.2f}")
    print(f"  N (Weyl asymptotic): {weyl_validation['N_weyl_asymptotic']:.2f}")
    print(f"  N (Riemann-von Mangoldt): {weyl_validation['N_riemann_von_mangoldt']:.2f}")
    print(f"  Relative error (exact): {weyl_validation['relative_error_exact']:.2%}")
    print(f"  Weyl law satisfied: {'✅' if weyl_validation['weyl_law_satisfied'] else '❌'}")
    
    # Compute trace from symbol
    print("\n5. Trace Formula from Symbol Fixed Points")
    print("-" * 80)
    
    trace_result = atlas.compute_trace_from_symbol(tau=0.5, primes=[2, 3, 5, 7], k_max=10)
    
    print(f"  τ = {trace_result['tau']}")
    print(f"  Tr(e^(-τH)) ≈ {trace_result['trace_real']:.6f} + {trace_result['trace_imag']:.6f}i")
    print(f"  |Trace| = {trace_result['trace_magnitude']:.6f}")
    print(f"  Primes used: {trace_result['primes_used']}")
    
    # Show prime contributions
    print(f"\n  Prime orbit contributions:")
    for p, contrib in trace_result['prime_contributions'].items():
        print(f"    p = {p}: {contrib.real:.6f} + {contrib.imag:.6f}i")
    
    # Derive κ from symbol
    print("\n6. κ Derivation from Symbol Expansion")
    print("-" * 80)
    
    kappa_result = atlas.derive_kappa_from_symbol()
    
    print(f"  κ (hermiticity condition): {kappa_result['kappa_hermiticity']:.6f}")
    print(f"  κ (Maslov index): {kappa_result['kappa_maslov_index']:.6f}")
    print(f"  κ (PT compensation): {kappa_result['kappa_pt_compensation']:.6f}")
    print(f"  κ (experimental κ_Π): {kappa_result['kappa_experimental']:.6f}")
    print(f"  Error (hermiticity): {kappa_result['error_hermiticity']:.6f}")
    print(f"  Derivation consistent: {'✅' if kappa_result['derivation_consistent'] else '❌'}")
    
    # Summary
    print("\n" + "=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    
    checks = [
        ("Symbol calculus available", symbol_calc is not None),
        ("Weyl law validated", weyl_validation.get('weyl_law_satisfied', False)),
        ("Trace formula computed", trace_result.get('trace_magnitude', 0) > 0),
        ("κ derivation consistent", kappa_result.get('derivation_consistent', False)),
    ]
    
    all_passed = all(check[1] for check in checks)
    
    for name, passed in checks:
        status = "✅" if passed else "❌"
        print(f"  {status} {name}")
    
    print("\n" + "=" * 80)
    if all_passed:
        print("✅ ALL VALIDATIONS PASSED")
        print("\nVerdict:")
        print("  • Symbol calculus successfully integrated with Atlas³ operator")
        print("  • Weyl law derived from phase space volume")
        print("  • Trace formula derived from Hamiltonian flow fixed points")
        print("  • κ anchored by hermiticity condition and symbol expansion")
    else:
        print("⚠️  SOME VALIDATIONS FAILED")
    
    print("=" * 80)
    
    return all_passed


def test_symbol_standalone():
    """Test symbol calculus standalone (without operator integration)."""
    
    print("\n" + "=" * 80)
    print("Standalone Symbol Calculus Test")
    print("=" * 80)
    
    # Create symbol
    symbol = PseudodifferentialSymbol(V_amp=12650.0, beta_0=2.0, use_principal=True)
    weyl = WeylLawCalculator(symbol)
    
    # Test Weyl law
    T = 50.0
    N_exact = weyl.counting_function(T)
    N_asymp = weyl.weyl_asymptotic(T)
    
    print(f"\nWeyl Law Test (T={T}):")
    print(f"  N(T) exact: {N_exact:.4f}")
    print(f"  N(T) asymptotic: {N_asymp:.4f}")
    print(f"  Relative error: {abs(N_exact - N_asymp)/N_exact:.2%}")
    
    # Validate
    result = validate_weyl_law_derivation(T_max=100.0, num_points=20)
    print(f"\nWeyl Law Validation:")
    print(f"  Mean error: {result['mean_error_asymptotic']:.2%}")
    print(f"  Convergence confirmed: {'✅' if result['convergence_confirmed'] else '❌'}")
    
    return True


if __name__ == "__main__":
    # Run standalone test first
    test_symbol_standalone()
    
    # Run integration validation
    success = validate_symbol_integration()
    
    # Exit with appropriate code
    sys.exit(0 if success else 1)
