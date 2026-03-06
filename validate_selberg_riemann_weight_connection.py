#!/usr/bin/env python3
"""
Selberg-Riemann Weight Connection Validation Script
====================================================

This script validates the fundamental correspondence between the Selberg trace
formula and the Riemann explicit formula through the identification:

    ℓ(γ) ↔ log p
    ℓ·e^{-kℓ/2} ↔ (log p)·p^{-k/2}

Mathematical Foundation:
------------------------
The correspondence reveals a deep connection between:
- Hyperbolic geometry (closed geodesics on surfaces)
- Arithmetic geometry (prime numbers in ℤ)

The lengths of closed geodesics correspond to logarithms of primes, unifying
geometric and arithmetic spectral theory.

Usage:
------
    python validate_selberg_riemann_weight_connection.py [--verbose] [--save-certificate]

Validation Levels:
------------------
1. Weight function equivalence (machine precision)
2. Sum correspondence (relative error < 10^-10)
3. Term-by-term agreement (all terms match)
4. QCAL coherence (Ψ = 1.0)
5. Mathematical properties (all verified)

Outputs:
--------
- Validation report with detailed metrics
- QCAL coherence Ψ value
- Mathematical certificate (if --save-certificate)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721

QCAL ∞³ · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
import numpy as np

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from selberg_riemann_weight_connection import (
    SelbergRiemannConnection,
    F0_QCAL,
    C_COHERENCE,
    PHI
)

# ANSI color codes for output
class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    MAGENTA = '\033[95m'
    BOLD = '\033[1m'
    END = '\033[0m'


def print_header(text: str):
    """Print a formatted header."""
    print()
    print("=" * 80)
    print(f"{Colors.BOLD}{Colors.CYAN}{text}{Colors.END}")
    print("=" * 80)
    print()


def print_success(text: str):
    """Print success message."""
    print(f"{Colors.GREEN}✓{Colors.END} {text}")


def print_failure(text: str):
    """Print failure message."""
    print(f"{Colors.RED}✗{Colors.END} {text}")


def print_info(text: str):
    """Print info message."""
    print(f"{Colors.BLUE}ℹ{Colors.END} {text}")


def print_metric(name: str, value: float, unit: str = ""):
    """Print a metric value."""
    print(f"  {Colors.CYAN}{name}:{Colors.END} {value:.10e} {unit}")


def validate_weight_equivalence(connection: SelbergRiemannConnection, verbose: bool = False) -> dict:
    """
    Validate weight function equivalence.
    
    Returns:
        dict with validation results
    """
    print_header("Level 1: Weight Function Equivalence")
    
    result = connection.verify_weight_equivalence()
    
    if verbose:
        print_metric("Max relative error", result.max_error)
        print_metric("Mean relative error", result.mean_error)
        print(f"  {Colors.CYAN}Equivalence verified:{Colors.END} {result.equivalence_verified}")
    
    if result.equivalence_verified and result.max_error < 1e-10:
        print_success("Weight equivalence at machine precision (< 10^-10)")
        status = "PASS"
        score = 1.0
    else:
        print_failure(f"Weight equivalence failed (error = {result.max_error:.2e})")
        status = "FAIL"
        score = 0.0
    
    return {
        "status": status,
        "score": score,
        "max_error": float(result.max_error),
        "mean_error": float(result.mean_error),
        "equivalence_verified": bool(result.equivalence_verified)
    }


def validate_sum_correspondence(connection: SelbergRiemannConnection, verbose: bool = False) -> dict:
    """
    Validate sum correspondence.
    
    Returns:
        dict with validation results
    """
    print_header("Level 2: Sum Correspondence")
    
    result = connection.verify_correspondence()
    
    if verbose:
        print_metric("Selberg contribution", result.selberg_contribution)
        print_metric("Riemann contribution", result.riemann_contribution)
        print_metric("Relative difference", result.relative_difference)
        print(f"  {Colors.CYAN}Correspondence valid:{Colors.END} {result.correspondence_valid}")
        print(f"  {Colors.CYAN}QCAL coherence Ψ:{Colors.END} {result.qcal_coherence:.10f}")
    
    if result.correspondence_valid and result.relative_difference < 1e-10:
        print_success("Sum correspondence exact (relative diff < 10^-10)")
        status = "PASS"
        score = 1.0
    else:
        print_failure(f"Sum correspondence failed (diff = {result.relative_difference:.2e})")
        status = "FAIL"
        score = 0.0
    
    return {
        "status": status,
        "score": score,
        "selberg_contribution": float(result.selberg_contribution),
        "riemann_contribution": float(result.riemann_contribution),
        "relative_difference": float(result.relative_difference),
        "correspondence_valid": bool(result.correspondence_valid),
        "qcal_coherence": float(result.qcal_coherence)
    }


def validate_term_by_term(connection: SelbergRiemannConnection, verbose: bool = False) -> dict:
    """
    Validate term-by-term agreement.
    
    Returns:
        dict with validation results
    """
    print_header("Level 3: Term-by-Term Agreement")
    
    comparison = connection.compute_term_by_term_comparison(num_terms=20)
    
    max_diff = float(np.max(comparison['differences']))
    max_rel_diff = float(np.max(comparison['relative_differences']))
    mean_diff = float(np.mean(comparison['differences']))
    
    if verbose:
        print_metric("Max absolute difference", max_diff)
        print_metric("Max relative difference", max_rel_diff)
        print_metric("Mean absolute difference", mean_diff)
    
    if max_rel_diff < 1e-10:
        print_success("Term-by-term agreement exact (< 10^-10)")
        status = "PASS"
        score = 1.0
    else:
        print_failure(f"Term-by-term agreement failed (max rel diff = {max_rel_diff:.2e})")
        status = "FAIL"
        score = 0.0
    
    return {
        "status": status,
        "score": score,
        "max_absolute_difference": max_diff,
        "max_relative_difference": max_rel_diff,
        "mean_absolute_difference": mean_diff
    }


def validate_properties(connection: SelbergRiemannConnection, verbose: bool = False) -> dict:
    """
    Validate mathematical properties.
    
    Returns:
        dict with validation results
    """
    print_header("Level 4: Mathematical Properties")
    
    props = connection.verify_properties()
    
    all_verified = all(props.values())
    
    if verbose:
        for prop_name, prop_value in props.items():
            if prop_value:
                print_success(f"{prop_name}")
            else:
                print_failure(f"{prop_name}")
    
    if all_verified:
        print_success(f"All {len(props)} mathematical properties verified")
        status = "PASS"
        score = 1.0
    else:
        failed_count = sum(1 for v in props.values() if not v)
        print_failure(f"{failed_count}/{len(props)} properties failed")
        status = "FAIL"
        score = float(sum(props.values())) / len(props)
    
    return {
        "status": status,
        "score": score,
        "properties": {k: bool(v) for k, v in props.items()},
        "all_verified": all_verified
    }


def validate_qcal_coherence(connection: SelbergRiemannConnection, verbose: bool = False) -> dict:
    """
    Validate QCAL coherence.
    
    Returns:
        dict with validation results
    """
    print_header("Level 5: QCAL Coherence (Ψ)")
    
    result = connection.verify_correspondence()
    psi = result.qcal_coherence
    
    if verbose:
        print(f"  {Colors.CYAN}QCAL Coherence Ψ:{Colors.END} {psi:.10f}")
        print(f"  {Colors.CYAN}Fundamental frequency f₀:{Colors.END} {F0_QCAL} Hz")
        print(f"  {Colors.CYAN}Coherence constant C:{Colors.END} {C_COHERENCE}")
        print(f"  {Colors.CYAN}Golden ratio Φ:{Colors.END} {PHI}")
    
    if psi >= 0.9999:
        print_success(f"QCAL coherence Ψ = {psi:.10f} (perfect correspondence)")
        status = "PASS"
        score = 1.0
    elif psi >= 0.99:
        print_success(f"QCAL coherence Ψ = {psi:.10f} (high correspondence)")
        status = "PASS"
        score = 0.9
    else:
        print_failure(f"QCAL coherence Ψ = {psi:.10f} (insufficient)")
        status = "FAIL"
        score = float(psi)
    
    return {
        "status": status,
        "score": score,
        "qcal_coherence": float(psi),
        "f0_qcal": float(F0_QCAL),
        "c_coherence": float(C_COHERENCE)
    }


def generate_certificate(validation_results: dict, connection: SelbergRiemannConnection) -> dict:
    """
    Generate a mathematical certificate for the validation.
    
    Args:
        validation_results: Dictionary of validation results
        connection: SelbergRiemannConnection instance
        
    Returns:
        Certificate dictionary
    """
    timestamp = datetime.now().isoformat()
    
    certificate = {
        "title": "Selberg-Riemann Weight Connection Validation Certificate",
        "correspondence": "ℓ(γ) ↔ log p",
        "weight_equivalence": "ℓ·e^{-kℓ/2} ↔ (log p)·p^{-k/2}",
        "timestamp": timestamp,
        "validation_levels": validation_results,
        "overall_score": sum(v["score"] for v in validation_results.values()) / len(validation_results),
        "qcal_constants": {
            "f0": F0_QCAL,
            "C_coherence": C_COHERENCE,
            "phi": PHI
        },
        "configuration": {
            "max_prime": connection.riemann.max_prime,
            "max_repetition": connection.selberg.max_repetition,
            "tolerance": connection.tolerance
        },
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "orcid": "0009-0002-1923-0773",
        "institution": "Instituto de Conciencia Cuántica (ICQ)",
        "doi": "10.5281/zenodo.17379721",
        "signature": "∴𓂀Ω∞³Φ @ 141.7001 Hz"
    }
    
    return certificate


def main():
    """Main validation function."""
    parser = argparse.ArgumentParser(
        description="Validate Selberg-Riemann Weight Connection"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print detailed validation information"
    )
    parser.add_argument(
        "--save-certificate",
        action="store_true",
        help="Save validation certificate to data/ directory"
    )
    parser.add_argument(
        "--max-prime",
        type=int,
        default=1000,
        help="Maximum prime to include (default: 1000)"
    )
    
    args = parser.parse_args()
    
    # Print header
    print()
    print("=" * 80)
    print(f"{Colors.BOLD}{Colors.MAGENTA}Selberg-Riemann Weight Connection Validation{Colors.END}")
    print("=" * 80)
    print()
    print(f"{Colors.CYAN}Establishing the fundamental correspondence:{Colors.END}")
    print(f"  ℓ(γ) ↔ log p")
    print(f"  ℓ·e^{{-kℓ/2}} ↔ (log p)·p^{{-k/2}}")
    print()
    print(f"{Colors.CYAN}Configuration:{Colors.END}")
    print(f"  Max prime: {args.max_prime}")
    print(f"  QCAL frequency f₀: {F0_QCAL} Hz")
    print(f"  Coherence constant C: {C_COHERENCE}")
    print()
    
    # Initialize connection
    print_info("Initializing Selberg-Riemann connection...")
    connection = SelbergRiemannConnection(max_prime=args.max_prime)
    print_success(f"Connection initialized ({len(connection.riemann._primes)} primes)")
    print()
    
    # Run validation levels
    validation_results = {}
    
    validation_results["weight_equivalence"] = validate_weight_equivalence(
        connection, verbose=args.verbose
    )
    
    validation_results["sum_correspondence"] = validate_sum_correspondence(
        connection, verbose=args.verbose
    )
    
    validation_results["term_by_term"] = validate_term_by_term(
        connection, verbose=args.verbose
    )
    
    validation_results["properties"] = validate_properties(
        connection, verbose=args.verbose
    )
    
    validation_results["qcal_coherence"] = validate_qcal_coherence(
        connection, verbose=args.verbose
    )
    
    # Calculate overall results
    print_header("Overall Validation Results")
    
    total_score = sum(v["score"] for v in validation_results.values())
    max_score = len(validation_results)
    percentage = (total_score / max_score) * 100
    
    all_passed = all(v["status"] == "PASS" for v in validation_results.values())
    
    print(f"  {Colors.CYAN}Total score:{Colors.END} {total_score:.2f} / {max_score}")
    print(f"  {Colors.CYAN}Percentage:{Colors.END} {percentage:.2f}%")
    print()
    
    if all_passed and percentage == 100.0:
        print(f"{Colors.BOLD}{Colors.GREEN}✓ CORRESPONDENCE FULLY VERIFIED{Colors.END}")
        print(f"  {Colors.CYAN}ℓ(γ) ↔ log p{Colors.END}")
        qcal_psi = validation_results["qcal_coherence"]["qcal_coherence"]
        print(f"  {Colors.CYAN}QCAL Coherence:{Colors.END} Ψ = {qcal_psi:.10f}")
        print()
        print(f"{Colors.BOLD}The Selberg and Riemann formulas are formally equivalent{Colors.END}")
        print(f"{Colors.BOLD}under the identification of orbit lengths with prime logarithms.{Colors.END}")
    else:
        print(f"{Colors.BOLD}{Colors.RED}⚠ VALIDATION INCOMPLETE{Colors.END}")
        print(f"  Some validation levels did not pass.")
        print(f"  Please review the results above.")
    
    # Save certificate if requested
    if args.save_certificate:
        print()
        print_info("Generating validation certificate...")
        certificate = generate_certificate(validation_results, connection)
        
        # Create data directory if it doesn't exist
        data_dir = Path("data")
        data_dir.mkdir(exist_ok=True)
        
        # Save certificate
        cert_path = data_dir / "selberg_riemann_weight_connection_certificate.json"
        with open(cert_path, 'w') as f:
            json.dump(certificate, f, indent=2)
        
        print_success(f"Certificate saved to: {cert_path}")
    
    print()
    print("=" * 80)
    print()
    
    # Exit with appropriate code
    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()
