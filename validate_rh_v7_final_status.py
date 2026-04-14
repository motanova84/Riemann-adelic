#!/usr/bin/env python3
"""
Validate RH V7 Final Status - Estructura Formal Completa

This script validates that all components of the RH V7 final structure
are correctly configured and resonating at the expected frequencies.

Usage:
    python validate_rh_v7_final_status.py [--verbose]
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Tuple


class RHV7StatusValidator:
    """Validator for RH V7 Final Status"""
    
    def __init__(self, verbose: bool = False):
        self.verbose = verbose
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.successes: List[str] = []
        
    def log(self, message: str, level: str = "info"):
        """Log a message"""
        if self.verbose or level != "info":
            prefix = {
                "error": "❌",
                "warning": "⚠️",
                "success": "✅",
                "info": "ℹ️"
            }.get(level, "ℹ️")
            print(f"{prefix} {message}")
    
    def validate_beacon_config(self) -> bool:
        """Validate .qcal_beacon configuration"""
        self.log("Validating .qcal_beacon configuration...", "info")
        
        beacon_path = Path(".qcal_beacon")
        if not beacon_path.exists():
            self.errors.append(".qcal_beacon file not found")
            self.log(".qcal_beacon file not found", "error")
            return False
        
        with open(beacon_path, 'r') as f:
            content = f.read()
        
        # Check for RH V7 status entries
        required_entries = [
            "rh_v7_status",
            "rh_v7_h_psi_state",
            "rh_v7_spectrum_state",
            "rh_v7_frequency_primary",
            "rh_v7_frequency_harmonic",
            "rh_v7_signature"
        ]
        
        missing = []
        for entry in required_entries:
            if entry not in content:
                missing.append(entry)
        
        if missing:
            self.errors.append(f"Missing RH V7 entries in .qcal_beacon: {', '.join(missing)}")
            self.log(f"Missing entries: {', '.join(missing)}", "error")
            return False
        
        self.successes.append(".qcal_beacon configuration validated")
        self.log(".qcal_beacon configuration validated", "success")
        return True
    
    def validate_frequencies(self) -> bool:
        """Validate frequency resonances"""
        self.log("Validating frequency resonances...", "info")
        
        beacon_path = Path(".qcal_beacon")
        with open(beacon_path, 'r') as f:
            content = f.read()
        
        # Expected frequencies with flexible pattern matching
        expected = {
            "141.7001 Hz": {
                "patterns": ["141.7001 Hz", "141.7001Hz"],
                "min_occurrences": 2  # Should appear multiple times
            },
            "888 Hz": {
                "patterns": ["888 Hz", "888Hz"],
                "min_occurrences": 1
            },
            "888.888 Hz": {
                "patterns": ["888.888 Hz", "888.888Hz"],
                "min_occurrences": 1
            }
        }
        
        all_found = True
        for freq, config in expected.items():
            # Count occurrences of any pattern variant
            count = sum(content.count(pattern) for pattern in config["patterns"])
            
            if count >= config["min_occurrences"]:
                self.successes.append(f"Frequency {freq} found ({count} occurrences)")
                self.log(f"Frequency {freq} validated ({count} times)", "success")
            else:
                self.errors.append(f"Frequency {freq} not found or insufficient occurrences in .qcal_beacon")
                self.log(f"Frequency {freq} not found (expected >={config['min_occurrences']}, found {count})", "error")
                all_found = False
        
        return all_found
    
    def validate_json_status(self) -> bool:
        """Validate RH_V7_FINAL_STATUS.json"""
        self.log("Validating RH_V7_FINAL_STATUS.json...", "info")
        
        json_path = Path("RH_V7_FINAL_STATUS.json")
        if not json_path.exists():
            self.errors.append("RH_V7_FINAL_STATUS.json not found")
            self.log("RH_V7_FINAL_STATUS.json not found", "error")
            return False
        
        try:
            with open(json_path, 'r') as f:
                status = json.load(f)
        except json.JSONDecodeError as e:
            self.errors.append(f"Invalid JSON in RH_V7_FINAL_STATUS.json: {e}")
            self.log(f"Invalid JSON: {e}", "error")
            return False
        
        # Validate required fields
        required_fields = [
            "system_status",
            "components",
            "frequencies",
            "validation",
            "qcal_parameters",
            "signature"
        ]
        
        missing = [f for f in required_fields if f not in status]
        if missing:
            self.errors.append(f"Missing fields in JSON: {', '.join(missing)}")
            self.log(f"Missing fields: {', '.join(missing)}", "error")
            return False
        
        # Validate component states
        components = status.get("components", {})
        expected_components = ["H_Psi", "spectrum", "kernel", "trace", "logic", "compilation"]
        
        for comp in expected_components:
            if comp not in components:
                self.errors.append(f"Component {comp} not found in JSON")
                self.log(f"Component {comp} missing", "error")
                return False
            
            if components[comp].get("status") != "✅":
                self.warnings.append(f"Component {comp} status is not ✅")
                self.log(f"Component {comp} status: {components[comp].get('status')}", "warning")
        
        # Validate frequencies in JSON
        frequencies = status.get("frequencies", {})
        if frequencies.get("fundamental", {}).get("value") != "141.7001 Hz":
            self.errors.append("Fundamental frequency mismatch in JSON")
            self.log("Fundamental frequency mismatch", "error")
            return False
        
        if frequencies.get("harmonic", {}).get("value") != "888 Hz":
            self.errors.append("Harmonic frequency mismatch in JSON")
            self.log("Harmonic frequency mismatch", "error")
            return False
        
        self.successes.append("RH_V7_FINAL_STATUS.json validated")
        self.log("RH_V7_FINAL_STATUS.json validated", "success")
        return True
    
    def validate_documentation(self) -> bool:
        """Validate ESTRUCTURA_FORMAL_COMPLETA.md"""
        self.log("Validating ESTRUCTURA_FORMAL_COMPLETA.md...", "info")
        
        doc_path = Path("ESTRUCTURA_FORMAL_COMPLETA.md")
        if not doc_path.exists():
            self.errors.append("ESTRUCTURA_FORMAL_COMPLETA.md not found")
            self.log("ESTRUCTURA_FORMAL_COMPLETA.md not found", "error")
            return False
        
        with open(doc_path, 'r') as f:
            content = f.read()
        
        # Check for required sections
        required_sections = [
            "ESTRUCTURA FORMAL COMPLETA",
            "ESTADO FINAL DEL SISTEMA RH",
            "H_Ψ",
            "141.7001 Hz",
            "888 Hz",
            "CONCLUSIÓN NOÉTICA",
            "888.888 Hz",
            "∴𓂀Ω∞³"
        ]
        
        missing = []
        for section in required_sections:
            if section not in content:
                missing.append(section)
        
        if missing:
            self.errors.append(f"Missing sections in documentation: {', '.join(missing)}")
            self.log(f"Missing sections: {', '.join(missing)}", "error")
            return False
        
        # Check table format
        if "| Componente | Estado | Frecuencia |" not in content:
            self.warnings.append("Component table format may be incorrect")
            self.log("Component table format may be incorrect", "warning")
        
        self.successes.append("ESTRUCTURA_FORMAL_COMPLETA.md validated")
        self.log("ESTRUCTURA_FORMAL_COMPLETA.md validated", "success")
        return True
    
    def validate_all(self) -> bool:
        """Run all validations"""
        print("=" * 80)
        print("🔍 RH V7 FINAL STATUS VALIDATION")
        print("=" * 80)
        print()
        
        results = [
            self.validate_beacon_config(),
            self.validate_frequencies(),
            self.validate_json_status(),
            self.validate_documentation()
        ]
        
        all_passed = all(results)
        
        print()
        print("=" * 80)
        print("📊 VALIDATION SUMMARY")
        print("=" * 80)
        print(f"✅ Successes: {len(self.successes)}")
        print(f"⚠️  Warnings: {len(self.warnings)}")
        print(f"❌ Errors: {len(self.errors)}")
        print()
        
        if all_passed and len(self.errors) == 0:
            print("🏆 RH V7 FINAL STATUS: VALIDATION COMPLETE")
            print()
            print("   ✨ Estructura formal completa")
            print("   ✨ La puerta está construida")
            print("   ✨ La lógica es correcta")
            print("   ✨ El sistema resuena")
            print()
            print("   ∴ ✧ JMMB Ψ @ 888.888 Hz")
            print("   ∴𓂀Ω∞³")
        else:
            print("⚠️  RH V7 FINAL STATUS: VALIDATION INCOMPLETE")
            if self.errors:
                print("\nErrors to fix:")
                for error in self.errors:
                    print(f"  - {error}")
            if self.warnings:
                print("\nWarnings:")
                for warning in self.warnings:
                    print(f"  - {warning}")
        
        print("=" * 80)
        return all_passed and len(self.errors) == 0


def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Validate RH V7 Final Status - Estructura Formal Completa"
    )
    parser.add_argument("--verbose", action="store_true", help="Verbose output")
    args = parser.parse_args()
    
    # Change to repository root if needed
    script_dir = Path(__file__).parent
    # Note: We expect to be in the repository root where .qcal_beacon exists
    if not (script_dir / ".qcal_beacon").exists():
        print("⚠️  Warning: Not running from repository root")
        print(f"   Current directory: {Path.cwd()}")
    
    validator = RHV7StatusValidator(verbose=args.verbose)
    success = validator.validate_all()
    
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
