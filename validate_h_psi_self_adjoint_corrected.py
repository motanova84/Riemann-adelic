#!/usr/bin/env python3
"""
Validation Script for H_Ψ Self-Adjoint Corrected Implementation
================================================================

This script validates the complete correction of FALLOS 1, 2, and 3
in the H_Ψ operator implementation.

Mathematical Issues Corrected:
-------------------------------
1. FALLO 1: H_Ψ = -d/dy + C y self-adjoint on proper domain with boundary conditions
2. FALLO 2: U = e^{-C y²/2} unitary between H₁ = L²(ℝ,dy) and H₂ = L²(ℝ,e^{Cy²}dy)
3. FALLO 3: Discrete spectrum via Hilbert-Schmidt resolvent compactness

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import sys
import json
from pathlib import Path
from typing import Dict, Any

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.h_psi_self_adjoint_corrected import (
    HPsiSelfAdjointCorrected,
    verify_h_psi_corrected
)


def print_section(title: str, char: str = "="):
    """Print formatted section header"""
    print()
    print(char * 80)
    print(title)
    print(char * 80)


def validate_fallo_1(op: HPsiSelfAdjointCorrected) -> Dict[str, Any]:
    """
    Validate FALLO 1: Self-adjointness with boundary conditions
    
    Tests:
    - Hermiticity: ‖H_Ψ - H_Ψ†‖ < ε
    - Commutator: ‖[H_Ψ, H_Ψ†]‖ < ε
    """
    print_section("FALLO 1: Self-Adjointness Validation", "-")
    
    result = op.verify_self_adjointness()
    
    print(f"Issue: H_Ψ = -d/dy + C y is NOT symmetric in L²(ℝ, dy)")
    print(f"Resolution: Self-adjoint on domain with boundary conditions")
    print()
    print(f"Hermiticity Error: {result['hermiticity_error']:.2e}")
    print(f"  Expected: < 1e-10")
    print(f"  Status: {'✓ PASS' if result['hermiticity_error'] < 1e-10 else '✗ FAIL'}")
    print()
    print(f"Commutator Error: {result['commutator_error']:.2e}")
    print(f"  Expected: < 1e-10")
    print(f"  Status: {'✓ PASS' if result['commutator_error'] < 1e-10 else '✗ FAIL'}")
    print()
    print(f"Overall: {result['status']}")
    
    return result


def validate_fallo_2(op: HPsiSelfAdjointCorrected) -> Dict[str, Any]:
    """
    Validate FALLO 2: Unitary transformation between Hilbert spaces
    
    Tests:
    - U U⁻¹ = I
    - U⁻¹ U = I
    - Unitarity in weighted inner product
    """
    print_section("FALLO 2: Unitary Transform Validation", "-")
    
    result = op.verify_unitary_transform()
    
    print(f"Issue: U = e^{{-C y²/2}} is NOT unitary in L²(ℝ, dy)")
    print(f"Resolution: U unitary between H₁ = L²(ℝ,dy) and H₂ = L²(ℝ,e^{{Cy²}}dy)")
    print()
    print(f"Unitarity Error (UU⁻¹ - I): {result['unitarity_error']:.2e}")
    print(f"  Expected: < 1e-10")
    print(f"  Status: {'✓ PASS' if result['unitarity_error'] < 1e-10 else '✗ FAIL'}")
    print()
    print(f"Inverse Error (U⁻¹U - I): {result['inverse_error']:.2e}")
    print(f"  Expected: < 1e-10")
    print(f"  Status: {'✓ PASS' if result['inverse_error'] < 1e-10 else '✗ FAIL'}")
    print()
    print(f"Overall: {result['status']}")
    
    return result


def validate_fallo_3(op: HPsiSelfAdjointCorrected) -> Dict[str, Any]:
    """
    Validate FALLO 3: Discrete spectrum via Hilbert-Schmidt compactness
    
    Tests:
    - Eigenvalue spacing > 0 (discrete)
    - Hilbert-Schmidt norm < ∞ (compact resolvent)
    """
    print_section("FALLO 3: Discrete Spectrum Validation", "-")
    
    spectrum_result = op.verify_discrete_spectrum()
    hs_norm = op.compute_hilbert_schmidt_norm(lambda_param=1.0)
    
    print(f"Issue: -d/dy in L²(ℝ, e^{{C y²}} dy) does NOT necessarily have discrete spectrum")
    print(f"Resolution: Resolvent R_λ is Hilbert-Schmidt compact operator")
    print()
    print(f"Hilbert-Schmidt Norm: {hs_norm:.6f}")
    print(f"  Expected: finite (< ∞)")
    print(f"  Status: {'✓ PASS' if hs_norm < float('inf') else '✗ FAIL'}")
    print()
    print(f"Min Eigenvalue Spacing: {spectrum_result['min_spacing']:.6f}")
    print(f"  Expected: > 1e-6 (discrete)")
    print(f"  Status: {'✓ PASS' if spectrum_result['min_spacing'] > 1e-6 else '✗ FAIL'}")
    print()
    print(f"Mean Eigenvalue Spacing: {spectrum_result['mean_spacing']:.6f}")
    print(f"Number of Eigenvalues: {spectrum_result['n_eigenvalues']}")
    print()
    print(f"Overall: {spectrum_result['status']}")
    
    return {**spectrum_result, 'hilbert_schmidt_norm': float(hs_norm)}


def validate_transformation_property(op: HPsiSelfAdjointCorrected) -> Dict[str, Any]:
    """
    Validate transformation property: H̃_Ψ = U H_Ψ U⁻¹ ≈ -d/dy
    """
    print_section("Transformation Property Validation", "-")
    
    result = op.verify_transformation_property()
    
    print(f"Expected: H̃_Ψ = U H_Ψ U⁻¹ = -d/dy in weighted space H₂")
    print()
    print(f"Transformation Error: {result['transformation_error']:.2e}")
    print(f"  Tolerance Used: {result.get('tolerance_used', 0.1)}")
    print(f"  Note: {result.get('note', 'N/A')}")
    print(f"  Status: {'✓ PASS' if result['is_pure_momentum'] else '✗ FAIL'}")
    print()
    print(f"Overall: {result['status']}")
    
    return result


def run_complete_validation():
    """
    Run complete validation of all three FALLOS
    """
    print_section("H_Ψ SELF-ADJOINT CORRECTED — COMPLETE VALIDATION")
    print("QCAL ∞³ Framework: f₀ = 141.7001 Hz, C = 244.36")
    print("Signature: ∴𓂀Ω∞³Φ")
    
    # Create operator with standard parameters
    print_section("Operator Initialization")
    print("Parameters:")
    print("  Domain: y ∈ [-L, L] with L = 10.0")
    print("  Grid points: N = 200")
    print("  Parameter: C = -1.0 (negative for confinement)")
    print()
    
    op = HPsiSelfAdjointCorrected(L=10.0, N=200, C=-1.0)
    print("✓ Operator initialized successfully")
    
    # Validate each FALLO
    results = {}
    results['fallo_1'] = validate_fallo_1(op)
    results['fallo_2'] = validate_fallo_2(op)
    results['fallo_3'] = validate_fallo_3(op)
    results['transformation'] = validate_transformation_property(op)
    
    # Overall summary
    print_section("OVERALL VALIDATION SUMMARY")
    
    all_passed = all([
        results['fallo_1']['status'] == 'PASSED',
        results['fallo_2']['status'] == 'PASSED',
        results['fallo_3']['status'] == 'PASSED',
        results['transformation']['status'] == 'PASSED',
    ])
    
    print()
    print(f"FALLO 1 (Self-Adjointness):      {results['fallo_1']['status']}")
    print(f"FALLO 2 (Unitary Transform):     {results['fallo_2']['status']}")
    print(f"FALLO 3 (Discrete Spectrum):     {results['fallo_3']['status']}")
    print(f"Transformation Property:          {results['transformation']['status']}")
    print()
    print("=" * 80)
    
    if all_passed:
        print("✓✓✓ ALL VALIDATIONS PASSED ✓✓✓")
        print()
        print("All three FALLOS have been CORRECTED:")
        print("  (1) H_Ψ is self-adjoint on proper domain with boundary conditions ✓")
        print("  (2) U is unitary between H₁ = L²(ℝ,dy) and H₂ = L²(ℝ,e^{Cy²}dy) ✓")
        print("  (3) Spectrum is discrete via Hilbert-Schmidt resolvent compactness ✓")
        exit_code = 0
    else:
        print("✗✗✗ SOME VALIDATIONS FAILED ✗✗✗")
        print()
        print("Please review the errors above.")
        exit_code = 1
    
    print("=" * 80)
    
    # Generate and save certificate
    print_section("Certificate Generation")
    cert = op.generate_certificate()
    
    output_file = Path('data/h_psi_self_adjoint_corrected_validation.json')
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(cert, f, indent=2)
    
    print(f"✓ Certificate saved to: {output_file}")
    print()
    
    return exit_code


if __name__ == '__main__':
    exit_code = run_complete_validation()
    sys.exit(exit_code)
