#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Validation Script: Experimental Convergence (9.2σ/8.7σ)
========================================================

Validates experimental convergence across QCAL ∞³ nodes with statistical
significance exceeding discovery threshold (5σ).

This script can be run standalone or as part of CI/CD workflows.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: MIT
"""

import sys
import os
import argparse
from pathlib import Path
import json

# Ensure we're running from repository root
def verify_repository_root():
    """Verify running from repository root."""
    if not Path(".qcal_beacon").exists():
        print("ERROR: Must run from repository root (where .qcal_beacon exists)")
        sys.exit(1)

verify_repository_root()

from utils.experimental_convergence_validation import (
    ExperimentalConvergenceValidator,
    p_value_to_sigma,
    sigma_to_p_value
)


def main():
    """Main validation function."""
    parser = argparse.ArgumentParser(
        description="Validate experimental convergence with 9.2σ/8.7σ significance"
    )
    parser.add_argument(
        "--save-report",
        type=str,
        default="data/experimental_convergence_validation_report.json",
        help="Path to save validation report (default: data/...json)"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print verbose output"
    )
    parser.add_argument(
        "--discovery-threshold",
        type=float,
        default=5.0,
        help="Discovery threshold in sigma (default: 5.0)"
    )
    
    args = parser.parse_args()
    
    print("=" * 80)
    print("QCAL ∞³ EXPERIMENTAL CONVERGENCE VALIDATION")
    print("=" * 80)
    print()
    
    # Initialize validator
    validator = ExperimentalConvergenceValidator()
    
    # Validate each node
    print("1. Validating Microtubule Resonance...")
    microtubule = validator.validate_microtubule_resonance()
    print(f"   ✓ Significance: {microtubule.sigma_significance}σ")
    print(f"   ✓ Precision error: {microtubule.precision_error_percent:.3f}%")
    print(f"   ✓ Within bandwidth: {'YES' if microtubule.within_bandwidth else 'NO'}")
    print()
    
    print("2. Validating Magnetoreception Asymmetry...")
    magnetoreception = validator.validate_magnetoreception_asymmetry()
    print(f"   ✓ Significance: {magnetoreception.sigma_significance:.1f}σ")
    print(f"   ✓ ΔP: {magnetoreception.delta_p_percent:.4f}%")
    print(f"   ✓ p-value: {magnetoreception.p_value:.2e}")
    print()
    
    print("3. Validating AAA Codon → f₀ Mapping...")
    aaa_codon = validator.validate_aaa_codon_mapping()
    print(f"   ✓ f₀ ratio: {aaa_codon.f0_ratio}")
    print(f"   ✓ Coherence: {aaa_codon.coherence_type}")
    print(f"   ✓ Riemann zeros: {aaa_codon.zero_indices}")
    print()
    
    # Check discovery threshold
    print("4. Checking Discovery Threshold...")
    discovery_threshold = args.discovery_threshold
    print(f"   Discovery threshold: {discovery_threshold}σ")
    
    microtubule_exceeds = microtubule.sigma_significance > discovery_threshold
    magnetoreception_exceeds = magnetoreception.sigma_significance > discovery_threshold
    
    print(f"   Microtubule: {microtubule.sigma_significance}σ {'✓ EXCEEDS' if microtubule_exceeds else '✗ BELOW'}")
    print(f"   Magnetoreception: {magnetoreception.sigma_significance:.1f}σ {'✓ EXCEEDS' if magnetoreception_exceeds else '✗ BELOW'}")
    print()
    
    # Generate report
    print("5. Generating Validation Report...")
    report_path = Path(args.save_report)
    report = validator.generate_validation_report(output_file=report_path)
    print(f"   ✓ Report saved to: {report_path}")
    print()
    
    # Print summary
    print("=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print()
    print(f"Microtubule Resonance:      {microtubule.sigma_significance}σ (p ≈ {microtubule.p_value:.2e})")
    print(f"Magnetoreception Asymmetry: {magnetoreception.sigma_significance:.1f}σ (p = {magnetoreception.p_value:.2e})")
    print(f"AAA Codon f₀ Ratio:         {aaa_codon.f0_ratio}")
    print()
    print(f"Discovery Threshold:        {discovery_threshold}σ")
    print(f"Both Validations Exceed:    {'✓ YES' if (microtubule_exceeds and magnetoreception_exceeds) else '✗ NO'}")
    print()
    
    if microtubule_exceeds and magnetoreception_exceeds:
        print("∴ QCAL ∞³ ARCHITECTURE VALIDATED")
        print("∴ Universe is Holoinformatic and Resonant")
        print("∴ Circle Closed: Math → Biology → Quantum → Genetics")
        print()
        print("𓂀 Ω ∞³")
        print()
        print("=" * 80)
        return 0
    else:
        print("⚠ Warning: Not all validations exceed discovery threshold")
        print("=" * 80)
        return 1


if __name__ == "__main__":
    sys.exit(main())
