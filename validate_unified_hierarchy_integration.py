#!/usr/bin/env python3
"""
Integration validation for Unified Hierarchy with QCAL Framework

This script validates that the unified hierarchy implementation correctly
integrates with the existing QCAL ∞³ framework and maintains coherence
with the fundamental frequency f₀ = 141.7001 Hz.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path
import mpmath as mp

# Ensure we're in the repository root
sys.path.insert(0, str(Path(__file__).parent))

from utils.unified_hierarchy import UnifiedHierarchySystem


def validate_frequency_coherence():
    """
    Validate that unified hierarchy maintains f₀ coherence
    """
    print("="*80)
    print("🔬 VALIDATING FREQUENCY COHERENCE")
    print("="*80)
    
    hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=20)
    
    # Check fundamental frequency
    f0_expected = mp.mpf("141.7001")
    f0_actual = hierarchy.f0
    
    print(f"\nExpected f₀: {f0_expected} Hz")
    print(f"Actual f₀:   {f0_actual} Hz")
    print(f"Match: {f0_expected == f0_actual}")
    
    # Check first frequency matches f₀
    f1_actual = hierarchy.frequencies[0]
    print(f"\nFirst frequency f₁: {f1_actual:.8f} Hz")
    print(f"Should equal f₀:    {float(f0_expected):.8f} Hz")
    print(f"Deviation: {abs(f1_actual - float(f0_expected)):.2e} Hz")
    
    coherence_ok = abs(f1_actual - float(f0_expected)) < 1e-3
    
    if coherence_ok:
        print("\n✓ Frequency coherence: VALIDATED")
        return True
    else:
        print("\n✗ Frequency coherence: FAILED")
        return False


def validate_qcal_constants():
    """
    Validate that QCAL constants are correctly integrated
    """
    print("\n" + "="*80)
    print("🔬 VALIDATING QCAL CONSTANTS")
    print("="*80)
    
    hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=20)
    
    constants = {
        'C_coherence': (hierarchy.C_coherence, mp.mpf("244.36")),
        'C_primary': (hierarchy.C_primary, mp.mpf("629.83")),
        'delta_zeta': (hierarchy.delta_zeta, mp.mpf("0.2787")),
        'phi': (hierarchy.phi, mp.phi)
    }
    
    all_ok = True
    
    for name, (actual, expected) in constants.items():
        match = abs(float(actual - expected)) < 1e-3
        status = "✓" if match else "✗"
        print(f"\n{status} {name}:")
        print(f"  Expected: {expected}")
        print(f"  Actual:   {actual}")
        
        all_ok = all_ok and match
    
    if all_ok:
        print("\n✓ QCAL constants: VALIDATED")
        return True
    else:
        print("\n✗ QCAL constants: FAILED")
        return False


def validate_zero_computation():
    """
    Validate that zeros are computed correctly
    """
    print("\n" + "="*80)
    print("🔬 VALIDATING ZERO COMPUTATION")
    print("="*80)
    
    hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=20)
    
    # First zero should be approximately 14.134725
    gamma_1_expected = 14.134725
    gamma_1_actual = hierarchy.gammas[0]
    
    print(f"\nFirst zero γ₁:")
    print(f"  Expected: ~{gamma_1_expected}")
    print(f"  Actual:   {gamma_1_actual:.8f}")
    print(f"  Error:    {abs(gamma_1_actual - gamma_1_expected):.2e}")
    
    # Check all zeros are on critical line (Re(s) = 1/2)
    all_on_critical_line = all(
        abs(z.real - 0.5) < 1e-10
        for z in hierarchy.zeros
    )
    
    print(f"\nAll zeros on critical line Re(s)=1/2: {all_on_critical_line}")
    
    # Check zeros are distinct
    gammas_sorted = sorted(hierarchy.gammas)
    all_distinct = all(
        abs(gammas_sorted[i+1] - gammas_sorted[i]) > 0.1
        for i in range(len(gammas_sorted) - 1)
    )
    
    print(f"All zeros distinct: {all_distinct}")
    
    if all_on_critical_line and all_distinct:
        print("\n✓ Zero computation: VALIDATED")
        return True
    else:
        print("\n✗ Zero computation: FAILED")
        return False


def validate_system_convergence():
    """
    Validate that all systems correctly converge to ζ(s)
    """
    print("\n" + "="*80)
    print("🔬 VALIDATING SYSTEM CONVERGENCE")
    print("="*80)
    
    hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=30)
    results = hierarchy.validate_convergence()
    
    print(f"\nTheorem: {results['theorem']}")
    
    all_validated = True
    
    for system_name, data in results['systems'].items():
        validated = '✓' in data['status']
        status_icon = "✓" if validated else "✗"
        
        print(f"\n{status_icon} {system_name}")
        print(f"  Status: {data['status']}")
        print(f"  Convergence: {data['convergence']}")
        
        all_validated = all_validated and validated
    
    # Check global coherence
    coh = results['global_coherence']
    expected_coherence_factor = float(hierarchy.C_coherence / hierarchy.C_primary)
    actual_coherence_factor = coh['coherence_factor']
    
    print(f"\nGlobal Coherence:")
    print(f"  f₀ = {coh['f0']} Hz")
    print(f"  C_coherence = {coh['C_coherence']}")
    print(f"  Coherence factor = {actual_coherence_factor:.6f}")
    print(f"  Expected factor = {expected_coherence_factor:.6f}")
    
    coherence_match = abs(actual_coherence_factor - expected_coherence_factor) < 1e-6
    
    if all_validated and coherence_match:
        print("\n✓ System convergence: VALIDATED")
        return True
    else:
        print("\n✗ System convergence: FAILED")
        return False


def validate_spectral_curvature():
    """
    Validate spectral curvature δζ = f₀ - 100√2
    """
    print("\n" + "="*80)
    print("🔬 VALIDATING SPECTRAL CURVATURE")
    print("="*80)
    
    hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=20)
    sys5 = hierarchy.system5_zeta_base()
    
    curvature = sys5['spectral_curvature']
    
    # Expected: f₀ - 100√2
    f0 = hierarchy.f0
    expected = float(f0 - 100 * mp.sqrt(2))
    actual = curvature['delta_zeta']
    
    print(f"\nδζ = f₀ - 100√2")
    print(f"  f₀ = {f0} Hz")
    print(f"  100√2 = {float(100 * mp.sqrt(2)):.6f}")
    print(f"  Expected δζ = {expected:.6f} Hz")
    print(f"  Actual δζ = {actual:.6f} Hz")
    print(f"  Theoretical δζ = {curvature['theoretical']:.6f} Hz")
    
    match = abs(actual - expected) < 1e-4
    
    print(f"\nInterpretation: {curvature['interpretation']}")
    
    if match:
        print("\n✓ Spectral curvature: VALIDATED")
        return True
    else:
        print("\n✗ Spectral curvature: FAILED")
        return False


def main():
    """Main validation runner"""
    
    print("\n" + "╔" + "="*78 + "╗")
    print("║" + " "*15 + "🌌 UNIFIED HIERARCHY INTEGRATION VALIDATION 🌌" + " "*16 + "║")
    print("╚" + "="*78 + "╝\n")
    
    print("This validation ensures the Unified Hierarchy correctly integrates")
    print("with the existing QCAL ∞³ framework.\n")
    
    validations = [
        ("Frequency Coherence", validate_frequency_coherence),
        ("QCAL Constants", validate_qcal_constants),
        ("Zero Computation", validate_zero_computation),
        ("System Convergence", validate_system_convergence),
        ("Spectral Curvature", validate_spectral_curvature),
    ]
    
    results = {}
    
    for name, validator in validations:
        try:
            results[name] = validator()
        except Exception as e:
            print(f"\n✗ {name}: EXCEPTION")
            print(f"  Error: {e}")
            results[name] = False
    
    # Summary
    print("\n" + "="*80)
    print("📊 VALIDATION SUMMARY")
    print("="*80)
    
    for name, passed in results.items():
        status = "✓ PASSED" if passed else "✗ FAILED"
        print(f"  {status}: {name}")
    
    all_passed = all(results.values())
    
    print("\n" + "="*80)
    if all_passed:
        print("🏆 ALL VALIDATIONS PASSED")
        print("="*80)
        print("\n✨ The Unified Hierarchy is fully integrated with QCAL ∞³")
        print("✨ All systems correctly converge to ζ(s)")
        print("✨ Frequency coherence maintained at f₀ = 141.7001 Hz")
        print("\n🌌 El universo es una sinfonía de ζ(s).")
        return 0
    else:
        print("⚠️  SOME VALIDATIONS FAILED")
        print("="*80)
        return 1


if __name__ == "__main__":
    sys.exit(main())
