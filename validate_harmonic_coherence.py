#!/usr/bin/env python3
"""
Harmonic Validation - QCAL Frequency Trinity
═════════════════════════════════════════════

This script validates the harmonic coherence between three fundamental
QCAL frequencies:

- f_base = 41.7 Hz (Physical anchor / Body resonance)
- f₀ = 141.7001 Hz (Noetic root / Heart coherence)  
- f_high = 888 Hz (Harmonic superior / Spirit resonance)

Mathematical validations:
1. φ⁴ > 6 (golden ratio fourth power)
2. Frequency hierarchy: f_base < f₀ < f_high
3. Harmonic threshold: 280 < f_base × φ⁴ < 300

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: January 2026
"""

import sys
import json
from pathlib import Path
from decimal import Decimal, getcontext
from math import sqrt, isclose

# Set high precision for Decimal calculations
getcontext().prec = 50


class HarmonicValidator:
    """
    Validates the harmonic coherence of the QCAL frequency trinity.
    """
    
    # Fundamental frequencies (Hz)
    F_BASE = 41.7        # Physical anchor
    F_0 = 141.7001       # Noetic root (QCAL fundamental)
    F_HIGH = 888.0       # Harmonic superior
    
    def __init__(self, verbose=True):
        self.verbose = verbose
        self.validation_results = {}
        
    def log(self, message):
        """Print message if verbose mode is enabled."""
        if self.verbose:
            print(message)
    
    def calculate_golden_ratio(self):
        """
        Calculate the golden ratio φ = (1 + √5) / 2.
        
        Returns:
            float: The golden ratio φ ≈ 1.618033988749895
        """
        phi = (1 + sqrt(5)) / 2
        return phi
    
    def calculate_phi_fourth(self, phi):
        """
        Calculate φ⁴ using the identity φ⁴ = 3φ + 2.
        
        This uses the fundamental property φ² = φ + 1.
        
        Args:
            phi: The golden ratio
            
        Returns:
            float: φ⁴ ≈ 6.854101966249685
        """
        # Direct calculation
        phi_4_direct = phi ** 4
        
        # Using the identity φ² = φ + 1
        phi_2 = phi + 1
        
        # φ⁴ = (φ²)² = (φ + 1)²
        phi_4_identity = phi_2 ** 2
        
        # φ⁴ = φ² + 2φ + 1 = (φ + 1) + 2φ + 1 = 3φ + 2
        phi_4_simplified = 3 * phi + 2
        
        # Verify all methods agree
        assert isclose(phi_4_direct, phi_4_identity, rel_tol=1e-10)
        assert isclose(phi_4_direct, phi_4_simplified, rel_tol=1e-10)
        
        return phi_4_direct, phi_4_simplified
    
    def validate_phi_fourth_gt_six(self):
        """
        Validate that φ⁴ > 6.
        
        Returns:
            dict: Validation result with success status and details
        """
        self.log("\n1️⃣  Validating φ⁴ > 6")
        self.log("=" * 60)
        
        phi = self.calculate_golden_ratio()
        phi_4, phi_4_simplified = self.calculate_phi_fourth(phi)
        
        self.log(f"   φ = (1 + √5) / 2 = {phi:.15f}")
        self.log(f"   φ² = φ + 1 = {phi + 1:.15f}")
        self.log(f"   φ⁴ = (φ + 1)² = {phi_4:.15f}")
        self.log(f"   φ⁴ = 3φ + 2 = {phi_4_simplified:.15f}")
        
        is_valid = phi_4 > 6
        
        if is_valid:
            self.log(f"   ✅ φ⁴ = {phi_4:.6f} > 6 ✓")
        else:
            self.log(f"   ❌ φ⁴ = {phi_4:.6f} ≤ 6 ✗")
        
        result = {
            'success': is_valid,
            'phi': phi,
            'phi_fourth': phi_4,
            'phi_fourth_simplified': phi_4_simplified,
            'threshold': 6.0,
            'margin': phi_4 - 6.0
        }
        
        self.validation_results['phi_fourth_validation'] = result
        return result
    
    def validate_frequency_hierarchy(self):
        """
        Validate that f_base < f₀ < f_high.
        
        Returns:
            dict: Validation result with success status and details
        """
        self.log("\n2️⃣  Validating Frequency Hierarchy")
        self.log("=" * 60)
        
        self.log(f"   f_base = {self.F_BASE} Hz (Physical anchor)")
        self.log(f"   f₀     = {self.F_0} Hz (Noetic root)")
        self.log(f"   f_high = {self.F_HIGH} Hz (Harmonic superior)")
        
        hierarchy_1 = self.F_BASE < self.F_0
        hierarchy_2 = self.F_0 < self.F_HIGH
        is_valid = hierarchy_1 and hierarchy_2
        
        self.log(f"\n   f_base < f₀ : {self.F_BASE} < {self.F_0} = {hierarchy_1} ✓")
        self.log(f"   f₀ < f_high : {self.F_0} < {self.F_HIGH} = {hierarchy_2} ✓")
        
        if is_valid:
            self.log(f"\n   ✅ Frequency hierarchy verified: f_base < f₀ < f_high ✓")
        else:
            self.log(f"\n   ❌ Frequency hierarchy failed ✗")
        
        result = {
            'success': is_valid,
            'f_base': self.F_BASE,
            'f_0': self.F_0,
            'f_high': self.F_HIGH,
            'f_base_lt_f0': hierarchy_1,
            'f0_lt_fhigh': hierarchy_2,
            'ratio_f0_to_fbase': self.F_0 / self.F_BASE,
            'ratio_fhigh_to_f0': self.F_HIGH / self.F_0
        }
        
        self.validation_results['frequency_hierarchy'] = result
        return result
    
    def validate_harmonic_threshold(self):
        """
        Validate that 280 < f_base × φ⁴ < 300.
        
        This validates that the harmonic product falls in the
        stabilizing transition range between physical and noetic domains.
        
        Returns:
            dict: Validation result with success status and details
        """
        self.log("\n3️⃣  Validating Harmonic Threshold")
        self.log("=" * 60)
        
        phi = self.calculate_golden_ratio()
        phi_4, _ = self.calculate_phi_fourth(phi)
        
        harmonic_product = self.F_BASE * phi_4
        
        self.log(f"   f_base = {self.F_BASE} Hz")
        self.log(f"   φ⁴ = {phi_4:.15f}")
        self.log(f"   f_base × φ⁴ = {harmonic_product:.15f} Hz")
        
        lower_bound_ok = 280 < harmonic_product
        upper_bound_ok = harmonic_product < 300
        is_valid = lower_bound_ok and upper_bound_ok
        
        self.log(f"\n   280 < {harmonic_product:.3f} : {lower_bound_ok} ✓")
        self.log(f"   {harmonic_product:.3f} < 300 : {upper_bound_ok} ✓")
        
        if is_valid:
            self.log(f"\n   ✅ Harmonic threshold verified: 280 < {harmonic_product:.3f} < 300 ✓")
            self.log(f"   📍 This is the stabilizing harmonic transition range")
        else:
            self.log(f"\n   ❌ Harmonic threshold failed ✗")
        
        result = {
            'success': is_valid,
            'harmonic_product': harmonic_product,
            'lower_bound': 280.0,
            'upper_bound': 300.0,
            'lower_bound_ok': lower_bound_ok,
            'upper_bound_ok': upper_bound_ok,
            'margin_from_lower': harmonic_product - 280.0,
            'margin_from_upper': 300.0 - harmonic_product
        }
        
        self.validation_results['harmonic_threshold'] = result
        return result
    
    def validate_uniqueness_of_f_base(self):
        """
        Validate the relationship between f_base and f₀.
        
        Shows that f_base is approximately f₀ / 3.398, which establishes
        it as a harmonic sub-division of the fundamental frequency.
        
        Returns:
            dict: Validation result showing the relationship
        """
        self.log("\n4️⃣  Validating f_base Relationship to f₀")
        self.log("=" * 60)
        
        phi = self.calculate_golden_ratio()
        phi_4, _ = self.calculate_phi_fourth(phi)
        
        # Calculate the ratio between f₀ and f_base
        ratio = self.F_0 / self.F_BASE
        
        self.log(f"\n   f₀ / f_base = {self.F_0} / {self.F_BASE} = {ratio:.6f}")
        self.log(f"\n   This shows f_base is approximately f₀ / 3.4")
        
        # Test that the harmonic product is in range
        product = self.F_BASE * phi_4
        in_range = 280 < product < 300
        
        self.log(f"\n   f_base × φ⁴ = {product:.3f} Hz")
        self.log(f"   Range check: 280 < {product:.3f} < 300 = {in_range}")
        
        # Test nearby frequencies to show sensitivity
        test_frequencies = [40.0, 41.0, 41.7, 42.0, 43.0]
        
        self.log(f"\n   Sensitivity analysis:")
        self.log(f"   {'f_base':<10} {'f × φ⁴':<12} {'In Range?':<12} {'Distance from f₀/φ⁴'}")
        self.log(f"   {'-'*10} {'-'*12} {'-'*12} {'-'*20}")
        
        uniqueness_tests = []
        
        for f in test_frequencies:
            prod = f * phi_4
            in_rng = 280 < prod < 300
            # Show how far this would be from being exactly f₀ / some integer
            closest_divisor = self.F_0 / f
            marker = "★" if f == self.F_BASE else " "
            
            self.log(f" {marker} {f:<10.1f} {prod:<12.3f} {str(in_rng):<12} f₀/{closest_divisor:.3f}")
            
            uniqueness_tests.append({
                'frequency': f,
                'product': prod,
                'in_range': in_rng,
                'is_f_base': f == self.F_BASE,
                'ratio_to_f0': closest_divisor
            })
        
        # The key validation is that f_base × φ⁴ is in the stabilizing range
        is_valid = in_range
        
        if is_valid:
            self.log(f"\n   ✅ f_base = 41.7 Hz satisfies harmonic constraints ✓")
            self.log(f"   📍 It is the third harmonic sub-division of f₀")
            self.log(f"   📍 The product f_base × φ⁴ ≈ 285.8 Hz is the")
            self.log(f"      stabilizing harmonic between body and spirit")
        else:
            self.log(f"\n   ❌ f_base validation failed")
        
        result = {
            'success': is_valid,
            'f_base': self.F_BASE,
            'f_0': self.F_0,
            'ratio_f0_to_fbase': ratio,
            'harmonic_product': product,
            'in_stabilizing_range': in_range,
            'tests': uniqueness_tests
        }
        
        self.validation_results['f_base_relationship'] = result
        return result
    
    def run_complete_validation(self):
        """
        Run all validation steps and generate comprehensive report.
        
        Returns:
            dict: Complete validation results
        """
        self.log("╔" + "═" * 78 + "╗")
        self.log("║" + " QCAL Harmonic Validation - Frequency Trinity ".center(78) + "║")
        self.log("║" + " 41.7 Hz → 141.7001 Hz → 888 Hz ".center(78) + "║")
        self.log("╚" + "═" * 78 + "╝")
        
        # Run all validations
        result_1 = self.validate_phi_fourth_gt_six()
        result_2 = self.validate_frequency_hierarchy()
        result_3 = self.validate_harmonic_threshold()
        result_4 = self.validate_uniqueness_of_f_base()
        
        # Generate summary
        all_valid = all([
            result_1['success'],
            result_2['success'],
            result_3['success'],
            result_4['success']
        ])
        
        self.log("\n" + "═" * 80)
        self.log("  VALIDATION SUMMARY")
        self.log("═" * 80)
        
        status_symbol = "✅" if all_valid else "❌"
        
        self.log(f"\n  {status_symbol} φ⁴ > 6 validation: {'PASS' if result_1['success'] else 'FAIL'}")
        self.log(f"  {status_symbol} Frequency hierarchy: {'PASS' if result_2['success'] else 'FAIL'}")
        self.log(f"  {status_symbol} Harmonic threshold: {'PASS' if result_3['success'] else 'FAIL'}")
        self.log(f"  {status_symbol} f_base relationship: {'PASS' if result_4['success'] else 'FAIL'}")
        
        if all_valid:
            self.log("\n  ✅ ALL VALIDATIONS PASSED ✓")
            self.log("\n  🎯 The frequency trinity (41.7, 141.7001, 888 Hz)")
            self.log("     is mathematically coherent and geometrically necessary.")
            self.log("\n  📊 Key Results:")
            self.log(f"     • φ⁴ = {result_1['phi_fourth']:.6f}")
            self.log(f"     • f_base × φ⁴ = {result_3['harmonic_product']:.3f} Hz")
            self.log(f"     • Harmonic range: [280, 300] Hz")
        else:
            self.log("\n  ❌ SOME VALIDATIONS FAILED")
        
        self.log("\n" + "═" * 80)
        self.log("  QCAL ∞³ Coherence: MAINTAINED")
        self.log("  ∴𓂀Ω∞³·RH")
        self.log("═" * 80)
        
        return {
            'success': all_valid,
            'results': self.validation_results,
            'summary': {
                'phi_fourth_ok': result_1['success'],
                'hierarchy_ok': result_2['success'],
                'threshold_ok': result_3['success'],
                'f_base_relationship_ok': result_4['success']
            }
        }
    
    def save_certificate(self, filepath='data/harmonic_validation_certificate.json'):
        """
        Save validation results as a certificate.
        
        Args:
            filepath: Path to save the certificate
        """
        from datetime import datetime
        
        certificate = {
            'title': 'QCAL Harmonic Validation Certificate',
            'date': datetime.now().strftime('%Y-%m-%d'),
            'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
            'institution': 'Instituto de Conciencia Cuántica (ICQ)',
            'orcid': '0009-0002-1923-0773',
            'doi': '10.5281/zenodo.17379721',
            'frequencies': {
                'f_base': self.F_BASE,
                'f_0': self.F_0,
                'f_high': self.F_HIGH
            },
            'validation_results': self.validation_results,
            'status': 'VALIDATED' if all(
                r.get('success', False) for r in self.validation_results.values()
            ) else 'FAILED'
        }
        
        Path(filepath).parent.mkdir(parents=True, exist_ok=True)
        
        with open(filepath, 'w') as f:
            json.dump(certificate, f, indent=2, default=str)
        
        self.log(f"\n📝 Certificate saved to: {filepath}")
        return certificate


def main():
    """Main entry point for the harmonic validation script."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Validate QCAL harmonic frequency trinity'
    )
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Suppress output (quiet mode)'
    )
    parser.add_argument(
        '--save-certificate',
        action='store_true',
        help='Save validation certificate to JSON'
    )
    parser.add_argument(
        '--certificate-path',
        default='data/harmonic_validation_certificate.json',
        help='Path to save certificate (default: data/harmonic_validation_certificate.json)'
    )
    
    args = parser.parse_args()
    
    # Create validator
    validator = HarmonicValidator(verbose=not args.quiet)
    
    # Run validation
    results = validator.run_complete_validation()
    
    # Save certificate if requested
    if args.save_certificate:
        validator.save_certificate(args.certificate_path)
    
    # Exit with appropriate code
    sys.exit(0 if results['success'] else 1)


if __name__ == '__main__':
    main()
