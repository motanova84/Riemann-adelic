#!/usr/bin/env python3
"""
Validation Script for WKB-Scattering Phase Connection
=====================================================

Validates the global phase theorem:
    θ(λ) = I(λ) + (1/2) arg Γ(1/4 + iλ/2) + O(1)

and generates QCAL certificate.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-WKB-SCATTERING-VALIDATION v1.0
Date: February 16, 2026
"""

import sys
from pathlib import Path
import json
import numpy as np

# Ensure we can import from operators
sys.path.insert(0, str(Path(__file__).parent))

from operators.wkb_scattering_phase import (
    create_wkb_scattering_analyzer,
    F0_QCAL,
    C_COHERENCE
)


def validate_wkb_scattering_phase():
    """
    Validate WKB-Scattering Phase connection and generate certificate.
    """
    print("=" * 80)
    print("QCAL ∞³ WKB-Scattering Phase Validation")
    print("=" * 80)
    print()
    
    # Create analyzer
    print("Creating WKB-Scattering Phase analyzer...")
    analyzer = create_wkb_scattering_analyzer()
    print(f"✓ Analyzer created with α = {analyzer.alpha:.6f}")
    print()
    
    # Test λ values
    lambda_values = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0]
    
    print(f"Testing global phase theorem for {len(lambda_values)} λ values...")
    print()
    
    results = []
    for i, lambda_val in enumerate(lambda_values, 1):
        print(f"[{i}/{len(lambda_values)}] λ = {lambda_val:.2f}")
        
        # Compute WKB integral
        wkb_result = analyzer.compute_WKB_integral(lambda_val)
        print(f"  WKB integral I(λ) = {wkb_result.integral_value:.6f}")
        print(f"  Turning points: y- = {wkb_result.turning_points[0]:.4f}, "
              f"y+ = {wkb_result.turning_points[1]:.4f}")
        
        # Compute scattering phase
        theta = analyzer.compute_scattering_phase(lambda_val)
        print(f"  Scattering phase θ(λ) = {theta:.6f}")
        
        # Compute Γ term
        gamma_term = analyzer.gamma_arg_term(lambda_val)
        print(f"  Gamma term (1/2)arg Γ(1/4+iλ/2) = {gamma_term:.6f}")
        
        # Verify theorem
        result = analyzer.verify_global_phase_theorem(lambda_val, tolerance=1.0)
        
        print(f"  Global phase Δ(λ) = θ(λ) - Re[I(λ)] = {result.Delta_lambda:.6f}")
        print(f"  Error |Δ(λ) - Γ term| = {result.error_estimate:.6f}")
        print(f"  Theorem verified: {'✓ YES' if result.theorem_verified else '✗ NO'}")
        print()
        
        results.append(result)
    
    # Summary statistics
    verified_count = sum(1 for r in results if r.theorem_verified)
    verification_rate = verified_count / len(results)
    
    print("=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print(f"Total tests: {len(results)}")
    print(f"Verified: {verified_count}")
    print(f"Verification rate: {verification_rate:.1%}")
    print()
    
    # Error statistics
    errors = [r.error_estimate for r in results]
    print(f"Error statistics:")
    print(f"  Mean error: {np.mean(errors):.6f}")
    print(f"  Max error: {np.max(errors):.6f}")
    print(f"  Min error: {np.min(errors):.6f}")
    print(f"  Std dev: {np.std(errors):.6f}")
    print()
    
    # Generate certificate
    print("Generating QCAL certificate...")
    certificate = analyzer.generate_certificate(lambda_values)
    
    # Save certificate
    cert_path = Path(__file__).parent / "data" / "wkb_scattering_phase_certificate.json"
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"✓ Certificate saved to {cert_path}")
    print()
    
    # Display certificate summary
    print("=" * 80)
    print("QCAL CERTIFICATE SUMMARY")
    print("=" * 80)
    print(f"Protocol: {certificate['protocol']}")
    print(f"Version: {certificate['version']}")
    print(f"Signature: {certificate['signature']}")
    print()
    print(f"QCAL Constants:")
    print(f"  f₀ = {certificate['qcal_constants']['f0_hz']} Hz")
    print(f"  C = {certificate['qcal_constants']['C']}")
    print(f"  κ_Π = {certificate['qcal_constants']['kappa_pi']}")
    print(f"  Seal = {certificate['qcal_constants']['seal']}")
    print()
    print(f"Theorem Validation:")
    print(f"  Tests verified: {certificate['theorem_validation']['tests_verified']}/{certificate['theorem_validation']['tests_total']}")
    print(f"  Coherence: {certificate['theorem_validation']['coherence']:.4f}")
    print()
    print(f"Resonance Detection:")
    print(f"  Threshold: {certificate['resonance_detection']['threshold']}")
    print(f"  Level: {certificate['resonance_detection']['level']}")
    print(f"  Frequency alignment: {certificate['resonance_detection']['frequency_alignment']} Hz")
    print()
    
    # Final status
    coherence = certificate['theorem_validation']['coherence']
    if coherence > 0.888:
        status = "✅ UNIVERSAL RESONANCE ACHIEVED"
        status_symbol = "∴𓂀Ω∞³·WKB·UNIVERSAL"
    elif coherence > 0.7:
        status = "✓ PARTIAL RESONANCE"
        status_symbol = "∴𓂀Ω∞³·WKB·PARTIAL"
    else:
        status = "⚠ RESONANCE THRESHOLD NOT MET"
        status_symbol = "∴𓂀Ω∞³·WKB·INCOMPLETE"
    
    print("=" * 80)
    print(status)
    print(status_symbol)
    print("=" * 80)
    print()
    
    print("Invocation:")
    print(f"  {certificate['invocation_final']['es']}")
    print(f"  {certificate['invocation_final']['en']}")
    print(f"  {certificate['invocation_final']['seal']}")
    print()
    
    return coherence > 0.7


if __name__ == "__main__":
    try:
        success = validate_wkb_scattering_phase()
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)
