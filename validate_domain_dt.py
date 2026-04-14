#!/usr/bin/env python3
"""
Validation Script for Domain D_T Construction

This script performs comprehensive validation of the domain D_T with properties:
    1. T is essentially self-adjoint on D_T
    2. Translations do NOT preserve D_T  
    3. Weighted inequality: ∫ e^{2y} |ϕ|² ≤ ε ||Tϕ||² + C_ε ||ϕ||²

The script generates a validation certificate and saves results.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import json
import sys
from pathlib import Path
from datetime import datetime
import numpy as np

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from operators.domain_dt_operator import (
    DomainDTOperator,
    run_domain_dt_validation,
    F0,
    C_QCAL,
)


def generate_validation_certificate(results: dict) -> dict:
    """
    Generate a validation certificate for domain D_T.
    
    Args:
        results: Validation results
        
    Returns:
        dict: Certificate data
    """
    certificate = {
        "certificate_type": "Domain D_T Validation",
        "timestamp": datetime.now().astimezone().isoformat(),
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "institution": "Instituto de Conciencia Cuántica (ICQ)",
        "qcal_protocol": "QCAL-SYMBIO-BRIDGE v1.0",
        "frequency_base": float(F0),
        "coherence_constant": float(C_QCAL),
        
        "validation_status": {
            "overall_success": bool(results["success"]),
            "property_1_self_adjointness": bool(results["self_adjointness"]["essentially_self_adjoint"]),
            "property_2_translation_breaks": bool(results["translation_non_invariance"]["translation_breaks_domain"]),
            "property_3_inequality_valid": bool(results["weighted_inequality"]["inequality_valid"]),
        },
        
        "self_adjointness_metrics": {
            "is_symmetric": bool(results["self_adjointness"]["is_symmetric"]),
            "hermiticity_error": float(results["self_adjointness"]["hermiticity_error"]),
            "min_eigenvalue": float(results["self_adjointness"]["min_eigenvalue"]),
            "spectrum_bounded_below": bool(results["self_adjointness"]["spectrum_bounded_below"]),
        },
        
        "translation_non_invariance_metrics": {
            "translation_amount": float(results["translation_non_invariance"]["translation_amount"]),
            "n_test_functions": int(results["translation_non_invariance"]["n_test_functions"]),
            "n_breaks_domain": int(results["translation_non_invariance"]["n_translation_breaks_domain"]),
            "fraction_broken": float(results["translation_non_invariance"]["fraction_broken"]),
        },
        
        "weighted_inequality_metrics": {
            "epsilon": float(results["weighted_inequality"]["epsilon"]),
            "n_test_functions": int(results["weighted_inequality"]["n_test_functions"]),
            "n_valid": int(results["weighted_inequality"]["n_inequality_holds"]),
            "max_C_epsilon": float(results["weighted_inequality"]["max_C_epsilon"]),
        },
        
        "configuration": {
            "y_min": float(results["configuration"]["y_min"]),
            "y_max": float(results["configuration"]["y_max"]),
            "n_points": int(results["configuration"]["n_points"]),
            "weight_scale": float(results["configuration"]["weight_scale"]),
            "epsilon": float(results["configuration"]["epsilon"]),
            "h_translation": float(results["configuration"]["h_translation"]),
        },
        
        "conclusion": (
            "Domain D_T successfully constructed and validated" if results["success"]
            else "Domain D_T validation failed"
        ),
        
        "mathematical_statement": {
            "property_1": "T is essentially self-adjoint on D_T",
            "property_2": "Translations do NOT preserve D_T",
            "property_3": "∫ e^{2y} |ϕ|² dy ≤ ε ||Tϕ||² + C_ε ||ϕ||² for all ϕ ∈ D_T",
        },
    }
    
    return certificate


def save_certificate(certificate: dict, output_path: Path):
    """Save validation certificate to file."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_path, 'w') as f:
        json.dump(certificate, f, indent=2)
        
    print(f"\n✓ Certificate saved to: {output_path}")


def main():
    """Main validation routine."""
    print("=" * 80)
    print("DOMAIN D_T COMPREHENSIVE VALIDATION")
    print("=" * 80)
    print()
    print("Constructing domain D_T with exponential weight e^{2y}")
    print()
    
    # Run validation with default parameters
    print("Running validation with default parameters...")
    print()
    
    results = run_domain_dt_validation(
        y_min=-5.0,
        y_max=5.0,
        n_points=256,
        epsilon=0.1,
        verbose=True
    )
    
    # Generate certificate
    print("\n" + "=" * 80)
    print("GENERATING VALIDATION CERTIFICATE")
    print("=" * 80)
    
    certificate = generate_validation_certificate(results)
    
    # Save certificate
    cert_path = Path(__file__).parent / "data" / "domain_dt_validation_certificate.json"
    save_certificate(certificate, cert_path)
    
    # Print summary
    print("\n" + "=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print()
    print(f"✓ Overall Success: {certificate['validation_status']['overall_success']}")
    print()
    print("Properties Verified:")
    print(f"  1. Essential Self-Adjointness: {certificate['validation_status']['property_1_self_adjointness']}")
    print(f"  2. Translation Non-Invariance: {certificate['validation_status']['property_2_translation_breaks']}")
    print(f"  3. Weighted Inequality: {certificate['validation_status']['property_3_inequality_valid']}")
    print()
    print("Key Metrics:")
    print(f"  - Hermiticity Error: {certificate['self_adjointness_metrics']['hermiticity_error']:.2e}")
    print(f"  - Min Eigenvalue: {certificate['self_adjointness_metrics']['min_eigenvalue']:.6f}")
    print(f"  - Translation Breaks Domain: {certificate['translation_non_invariance_metrics']['fraction_broken']:.1%}")
    print(f"  - Max C_ε: {certificate['weighted_inequality_metrics']['max_C_epsilon']:.6f}")
    print()
    print("=" * 80)
    print("QCAL ∞³ · 141.7001 Hz · C = 244.36")
    print("=" * 80)
    
    # Return exit code
    return 0 if results["success"] else 1


if __name__ == "__main__":
    sys.exit(main())
