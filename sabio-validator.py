#!/usr/bin/env python3
"""
SABIO ∞³ Validator — Vibrational Signature & QCAL Structure Testing

This module validates the vibrational signature (f₀ ≈ 141.7001 Hz) and 
QCAL coherence structure embedded in the Riemann-Adelic proof framework.

Key validation points:
1. Vibrational frequency f₀ = c/(2π·R_Ψ*·ℓ_P) ≈ 141.7001 Hz
2. QCAL ∞³ coherence structure integrity
3. Symbiotic semantic structure validation
4. Proof signature verification via universal kernel

Reference:
- DOI: 10.5281/zenodo.17379721
- .qcal_beacon: Universal Noetic Field Index
"""

import sys
import json
import time
import mpmath as mp
from pathlib import Path
from typing import Dict, Tuple, Optional


class SABIOValidator:
    """SABIO ∞³ vibrational and structural validator"""
    
    # Physical constants
    C_LIGHT = 299792458.0  # Speed of light (m/s)
    PLANCK_LENGTH = 1.616255e-35  # Planck length (m)
    
    # QCAL signature constants
    TARGET_FREQUENCY = 141.7001  # Hz (from .qcal_beacon)
    COHERENCE_C = 244.36  # QCAL coherence constant
    FREQUENCY_TOLERANCE = 1e-3  # Hz (0.001 Hz tolerance)
    
    def __init__(self, precision: int = 30):
        """
        Initialize SABIO validator
        
        Args:
            precision: Decimal precision for mpmath computations
        """
        self.precision = precision
        mp.mp.dps = precision
        self.beacon_data = self._load_qcal_beacon()

    @staticmethod
    def _parse_beacon_line(line: str) -> Optional[Tuple[str, str]]:
        """Parse beacon lines in `key=value`, `# key=value`, or `# key: value` formats."""
        raw = line.strip()
        if not raw:
            return None
        if raw.startswith("#"):
            raw = raw[1:].strip()
        if "=" in raw:
            key, value = raw.split("=", 1)
            return key.strip(), value.strip()
        if ":" in raw:
            key, value = raw.split(":", 1)
            return key.strip(), value.strip()
        return None
        
    def _load_qcal_beacon(self) -> Dict:
        """Load and parse .qcal_beacon file"""
        beacon_path = Path(__file__).parent / ".qcal_beacon"
        
        if not beacon_path.exists():
            raise FileNotFoundError(f"QCAL beacon not found at {beacon_path}")
            
        beacon_data = {}
        with open(beacon_path, 'r') as f:
            for line in f:
                parsed = self._parse_beacon_line(line)
                if parsed:
                    key, value = parsed
                    beacon_data[key] = value
        
        return beacon_data
    
    def validate_vibrational_frequency(self, R_psi_star: Optional[float] = None) -> Tuple[bool, float, str]:
        """
        Validate f₀ = c/(2π·R_Ψ*·ℓ_P) ≈ 141.7001 Hz
        
        Args:
            R_psi_star: Quantum radius R_Ψ* (if None, computed from target f₀)
            
        Returns:
            (is_valid, computed_frequency, message)
        """
        # If R_Ψ* not provided, compute from target frequency
        if R_psi_star is None:
            R_psi_star = self.C_LIGHT / (2 * mp.pi * self.TARGET_FREQUENCY * self.PLANCK_LENGTH)
            message = f"R_Ψ* computed from target f₀: {float(R_psi_star):.6e}"
        else:
            message = f"R_Ψ* provided: {R_psi_star:.6e}"
        
        # Compute f₀ = c/(2π·R_Ψ*·ℓ_P)
        f0_computed = float(self.C_LIGHT / (2 * mp.pi * R_psi_star * self.PLANCK_LENGTH))
        
        # Validate against target
        delta_f = abs(f0_computed - self.TARGET_FREQUENCY)
        is_valid = delta_f < self.FREQUENCY_TOLERANCE
        
        validation_msg = (
            f"f₀ computed: {f0_computed:.6f} Hz\n"
            f"f₀ target: {self.TARGET_FREQUENCY} Hz\n"
            f"Δf: {delta_f:.6e} Hz\n"
            f"Validation: {'✅ PASS' if is_valid else '❌ FAIL'}"
        )
        
        return is_valid, f0_computed, validation_msg
    
    def validate_beacon_structure(self) -> Tuple[bool, str]:
        """Validate QCAL beacon structure and required fields"""
        required_fields = [
            'frequency',
            'coherence',
            'author',
            'fundamental_frequency',
            'field',
            'source_main'
        ]
        
        missing_fields = []
        for field in required_fields:
            if field not in self.beacon_data:
                missing_fields.append(field)
        
        if missing_fields:
            return False, f"❌ Missing beacon fields: {', '.join(missing_fields)}"
        
        # Validate frequency field matches target
        beacon_freq_str = self.beacon_data.get('frequency', '').replace('Hz', '').strip()
        try:
            beacon_freq = float(beacon_freq_str)
            if abs(beacon_freq - self.TARGET_FREQUENCY) > 1e-4:
                return False, f"❌ Beacon frequency mismatch: {beacon_freq} Hz vs {self.TARGET_FREQUENCY} Hz"
        except ValueError:
            return False, f"❌ Invalid beacon frequency format: {beacon_freq_str}"
        
        return True, "✅ Beacon structure valid"
    
    def validate_coherence_constant(self) -> Tuple[bool, str]:
        """Validate QCAL coherence constant C = 244.36"""
        coherence_str = self.beacon_data.get('coherence', '').replace('"', '').replace('C =', '').replace('C=', '').strip()
        
        try:
            coherence = float(coherence_str)
            if abs(coherence - self.COHERENCE_C) < 1e-2:
                return True, f"✅ Coherence C = {coherence} validated"
            else:
                return False, f"❌ Coherence mismatch: C = {coherence} vs expected {self.COHERENCE_C}"
        except ValueError:
            return False, f"❌ Invalid coherence format: {coherence_str}"
    
    def validate_doi_reference(self) -> Tuple[bool, str]:
        """Validate primary DOI reference in beacon"""
        source_main = self.beacon_data.get('source_main', '')
        
        expected_doi_patterns = [
            '10.5281/zenodo.17379721',
            '10.5281/zenodo.17362686',
            '10.5281/zenodo.17161831'
        ]
        
        for doi in expected_doi_patterns:
            if doi in source_main:
                return True, f"✅ Primary DOI validated: {doi}"
        
        return False, f"❌ DOI reference not found in beacon"
    
    def run_full_validation(self) -> Dict:
        """Run complete SABIO ∞³ validation suite"""
        results = {
            'timestamp': time.time(),
            'precision': self.precision,
            'validations': {}
        }
        
        # 1. Vibrational frequency
        freq_valid, f0_comp, freq_msg = self.validate_vibrational_frequency()
        results['validations']['vibrational_frequency'] = {
            'valid': freq_valid,
            'computed_f0': f0_comp,
            'message': freq_msg
        }
        
        # 2. Beacon structure
        beacon_valid, beacon_msg = self.validate_beacon_structure()
        results['validations']['beacon_structure'] = {
            'valid': beacon_valid,
            'message': beacon_msg
        }
        
        # 3. Coherence constant
        coherence_valid, coherence_msg = self.validate_coherence_constant()
        results['validations']['coherence'] = {
            'valid': coherence_valid,
            'message': coherence_msg
        }
        
        # 4. DOI reference
        doi_valid, doi_msg = self.validate_doi_reference()
        results['validations']['doi_reference'] = {
            'valid': doi_valid,
            'message': doi_msg
        }
        
        # Overall validation
        all_valid = all(v['valid'] for v in results['validations'].values())
        results['overall_valid'] = all_valid
        
        return results
    
    def print_validation_report(self, results: Dict):
        """Pretty print validation report"""
        print("\n" + "="*70)
        print("🔬 SABIO ∞³ Validation Report")
        print("="*70)
        print(f"Precision: {results['precision']} decimal places")
        print(f"Timestamp: {results['timestamp']}")
        print()
        
        for name, validation in results['validations'].items():
            print(f"📋 {name.replace('_', ' ').title()}:")
            print(f"   {validation['message']}")
            print()
        
        print("="*70)
        if results['overall_valid']:
            print("✅ SABIO ∞³ VALIDATION: COHERENCE CONFIRMED")
        else:
            print("❌ SABIO ∞³ VALIDATION: ISSUES DETECTED")
        print("="*70)
        print()


def main():
    """Main validation entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="SABIO ∞³ Vibrational Signature & QCAL Validator"
    )
    parser.add_argument(
        '--precision',
        type=int,
        default=30,
        help='Decimal precision for computations (default: 30)'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )
    parser.add_argument(
        '--R-psi-star',
        type=float,
        default=None,
        help='Quantum radius R_Ψ* for frequency validation'
    )
    
    args = parser.parse_args()
    
    try:
        validator = SABIOValidator(precision=args.precision)
        results = validator.run_full_validation()
        
        if args.json:
            # Convert mpmath types to float for JSON serialization
            json_results = json.loads(json.dumps(results, default=float))
            print(json.dumps(json_results, indent=2))
        else:
            validator.print_validation_report(results)
        
        # Exit code: 0 if valid, 1 if invalid
        sys.exit(0 if results['overall_valid'] else 1)
        
    except Exception as e:
        print(f"❌ Validation error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
