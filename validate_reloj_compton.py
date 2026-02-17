#!/usr/bin/env python3
"""
Validation Script for Reloj Compton Module

This script validates the implementation of reloj_compton.py by running
comprehensive tests on:
1. Individual Compton frequency calculations
2. Cosmic scale factor derivation
3. Master equation computation
4. Error tolerance validation
5. High-precision calculations

The validation ensures that the fundamental frequency f₀ = 141.7001 Hz
is correctly derived from first principles using particle Compton frequencies.

Usage:
    python validate_reloj_compton.py [--precision DPS]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Framework
"""

import sys
from pathlib import Path
import argparse

# Import the reloj_compton module
from reloj_compton import ComptonClock


def test_compton_frequencies(clock: ComptonClock) -> bool:
    """
    Test 1: Validate Compton frequency calculations.
    
    Verifies that Compton frequencies for fundamental particles are
    calculated correctly using f = (m c²) / h.
    """
    print("\n" + "="*80)
    print("TEST 1: Compton Frequency Calculations")
    print("="*80)
    
    analysis = clock.analyze_particle_compton_frequencies()
    
    # Expected approximate values (Hz)
    expected = {
        "electron": 1.235590e20,
        "proton": 2.268732e23,
        "neutron": 2.271859e23,
        "planck": 2.952099e42
    }
    
    tolerance = 0.01  # 1% tolerance
    all_passed = True
    
    for particle, expected_freq in expected.items():
        calculated_freq = analysis[particle]["frequency_Hz"]
        rel_error = abs(calculated_freq - expected_freq) / expected_freq
        
        passed = rel_error < tolerance
        status = "✅ PASS" if passed else "❌ FAIL"
        
        print(f"\n{particle.capitalize()}:")
        print(f"  Expected:   {expected_freq:.6e} Hz")
        print(f"  Calculated: {calculated_freq:.6e} Hz")
        print(f"  Error:      {rel_error*100:.4f}%")
        print(f"  {status}")
        
        if not passed:
            all_passed = False
    
    return all_passed


def test_cosmic_scale_factor(clock: ComptonClock) -> bool:
    """
    Test 2: Validate cosmic scale factor derivation.
    
    Verifies that K = 2·(m_P/m_e)^(1/3)·φ³ ≈ 2.44×10⁸ is calculated correctly.
    """
    print("\n" + "="*80)
    print("TEST 2: Cosmic Scale Factor Derivation")
    print("="*80)
    
    scale_factor = clock.derive_cosmic_scale_factor()
    K = scale_factor["K"]
    
    # Expected value
    expected_K = 2.44e8
    tolerance = 0.01  # 1% tolerance
    
    rel_error = abs(K - expected_K) / expected_K
    passed = rel_error < tolerance
    status = "✅ PASS" if passed else "❌ FAIL"
    
    print(f"\nCosmic Scale Factor K:")
    print(f"  K = 2·(m_P/m_e)^(1/3)·φ³")
    print(f"  Expected:   {expected_K:.6e}")
    print(f"  Calculated: {K:.6e}")
    print(f"  Error:      {rel_error*100:.4f}%")
    print(f"  {status}")
    
    print(f"\nComponents:")
    print(f"  Mass ratio (m_P/m_e): {scale_factor['mass_ratio_m_P_over_m_e']:.6e}")
    print(f"  Cube root:            {scale_factor['mass_ratio_cbrt']:.6e}")
    print(f"  φ:                    {scale_factor['phi']:.10f}")
    print(f"  φ³:                   {scale_factor['phi_cubed']:.10f}")
    
    return passed


def test_master_equation(clock: ComptonClock) -> bool:
    """
    Test 3: Validate master equation computation.
    
    Verifies that the master equation correctly computes f₀ from all components:
    f₀ = (c/(2π)) · √(m_P/m_e) · α · φ · (ℓ_P/λ_C) · K
    """
    print("\n" + "="*80)
    print("TEST 3: Master Equation Computation")
    print("="*80)
    
    results = clock.compute_fundamental_frequency(verbose=False)
    
    f0_calc = results["f0_calculated_Hz"]
    f0_theory = results["f0_theoretical_Hz"]
    error = results["error_percent"]
    
    # Expected error: ~0.11%
    max_error = 1.0  # Maximum acceptable error: 1%
    passed = error < max_error
    status = "✅ PASS" if passed else "❌ FAIL"
    
    print(f"\nMaster Equation: f₀ = (c/(2π)) · √(m_P/m_e) · α · φ · (ℓ_P/λ_C) · K")
    print(f"\nComponents:")
    comp = results["master_equation_components"]
    print(f"  c/(2π):       {comp['c_over_2pi_m_per_s']:.6e} m/s")
    print(f"  √(m_P/m_e):   {comp['sqrt_mass_ratio']:.6e}")
    print(f"  α:            {comp['alpha']:.10f}")
    print(f"  φ:            {comp['phi']:.10f}")
    print(f"  ℓ_P/λ_C:      {comp['length_ratio_l_P_over_lambda_C']:.6e}")
    print(f"  K:            {comp['K_cosmic_scale_factor']:.6e}")
    
    print(f"\nResult:")
    print(f"  f₀ calculated:  {f0_calc:.4f} Hz")
    print(f"  f₀ theoretical: {f0_theory:.4f} Hz")
    print(f"  Error:          {error:.4f}%")
    print(f"  {status}")
    
    return passed


def test_error_tolerance(clock: ComptonClock) -> bool:
    """
    Test 4: Validate error tolerance.
    
    Ensures that the calculated frequency matches the problem statement
    requirements: f₀ ≈ 141.5459 Hz with error ≈ 0.1088%.
    """
    print("\n" + "="*80)
    print("TEST 4: Error Tolerance Validation")
    print("="*80)
    
    results = clock.compute_fundamental_frequency(verbose=False)
    
    f0_calc = results["f0_calculated_Hz"]
    error = results["error_percent"]
    
    # Problem statement specifications
    expected_f0_calc = 141.5459
    expected_error = 0.1088
    
    # Allow small tolerance for numerical differences
    f0_tolerance = 0.001  # Hz
    error_tolerance = 0.001  # %
    
    f0_match = abs(f0_calc - expected_f0_calc) < f0_tolerance
    error_match = abs(error - expected_error) < error_tolerance
    
    passed = f0_match and error_match
    status = "✅ PASS" if passed else "❌ FAIL"
    
    print(f"\nProblem Statement Requirements:")
    print(f"  Expected f₀ calculated: {expected_f0_calc:.4f} Hz")
    print(f"  Actual f₀ calculated:   {f0_calc:.4f} Hz")
    print(f"  Match: {'✅' if f0_match else '❌'}")
    
    print(f"\n  Expected error: {expected_error:.4f}%")
    print(f"  Actual error:   {error:.4f}%")
    print(f"  Match: {'✅' if error_match else '❌'}")
    
    print(f"\n  Overall: {status}")
    
    return passed


def test_high_precision(precisions: list = [50, 100, 200]) -> bool:
    """
    Test 5: Validate high-precision calculations.
    
    Tests that the module works correctly with different precision levels.
    """
    print("\n" + "="*80)
    print("TEST 5: High-Precision Calculations")
    print("="*80)
    
    all_passed = True
    
    for dps in precisions:
        try:
            clock = ComptonClock(precision=dps)
            results = clock.compute_fundamental_frequency(verbose=False)
            
            error = results["error_percent"]
            passed = error < 1.0
            status = "✅ PASS" if passed else "❌ FAIL"
            
            print(f"\nPrecision: {dps} decimal places")
            print(f"  f₀ calculated: {results['f0_calculated_Hz']:.6f} Hz")
            print(f"  Error:         {error:.6f}%")
            print(f"  {status}")
            
            if not passed:
                all_passed = False
                
        except Exception as e:
            print(f"\nPrecision: {dps} decimal places")
            print(f"  ❌ FAIL: {str(e)}")
            all_passed = False
    
    return all_passed


def run_validation_suite(precision: int = 50) -> bool:
    """
    Run complete validation suite.
    
    Executes all validation tests and reports results.
    """
    print("\n" + "╔" + "═"*78 + "╗")
    print("║" + " "*15 + "RELOJ COMPTON VALIDATION SUITE" + " "*33 + "║")
    print("║" + " "*78 + "║")
    print("║" + "  QCAL ∞³ Framework Validation".ljust(78) + "║")
    print("╚" + "═"*78 + "╝")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print()
    
    # Create Compton Clock instance
    clock = ComptonClock(precision=precision)
    
    # Run all tests
    results = []
    
    print("\n" + "🔬 Running Validation Tests...")
    
    results.append(("Compton Frequencies", test_compton_frequencies(clock)))
    results.append(("Cosmic Scale Factor", test_cosmic_scale_factor(clock)))
    results.append(("Master Equation", test_master_equation(clock)))
    results.append(("Error Tolerance", test_error_tolerance(clock)))
    results.append(("High Precision", test_high_precision([50, 100])))
    
    # Summary
    print("\n" + "="*80)
    print("VALIDATION SUMMARY")
    print("="*80)
    
    all_passed = True
    for test_name, passed in results:
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"{test_name:.<50} {status}")
        if not passed:
            all_passed = False
    
    print("\n" + "="*80)
    if all_passed:
        print("🎉 ALL TESTS PASSED")
        print("✅ Reloj Compton module validated successfully")
    else:
        print("⚠️  SOME TESTS FAILED")
        print("❌ Please review the failed tests above")
    print("="*80 + "\n")
    
    return all_passed


def main():
    """Main entry point for validation script."""
    parser = argparse.ArgumentParser(
        description="Validate reloj_compton.py implementation",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument(
        '--precision',
        type=int,
        default=50,
        help='Decimal precision for computations (default: 50)'
    )
    
    args = parser.parse_args()
    
    # Run validation suite
    success = run_validation_suite(precision=args.precision)
    
    # Return exit code
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
