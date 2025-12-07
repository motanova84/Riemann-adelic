#!/usr/bin/env python3
"""
SAT Certificate Validator
=========================

This script validates SAT certificates generated for mathematical theorems.
It verifies cryptographic hashes, checks theorem consistency, and ensures
certificate integrity.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Date: December 2025
DOI: 10.5281/zenodo.17379721

Usage:
    python scripts/validate_sat_certificates.py [--certificate FILE] [--all]
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Tuple


class SATCertificateValidator:
    """Validate SAT certificates for mathematical theorems."""
    
    def __init__(self, certificates_dir: str = "certificates/sat"):
        self.certificates_dir = Path(certificates_dir)
        self.validation_timestamp = datetime.utcnow().isoformat() + "Z"
        
    def load_certificate(self, filepath: Path) -> Dict[str, Any]:
        """Load certificate from JSON file."""
        try:
            with open(filepath, 'r') as f:
                return json.load(f)
        except Exception as e:
            raise ValueError(f"Failed to load certificate: {e}")
    
    def verify_certificate_hash(self, certificate: Dict[str, Any]) -> Tuple[bool, str]:
        """Verify the cryptographic hash of the certificate."""
        # Extract stored hash
        stored_hash = certificate.get("cryptographic_proof", {}).get("certificate_hash")
        if not stored_hash:
            return False, "No certificate hash found"
        
        # Remove hash fields for recomputation
        cert_copy = certificate.copy()
        if "cryptographic_proof" in cert_copy:
            cert_copy["cryptographic_proof"] = {
                "certificate_hash": None,
                "validator_signature": None
            }
        
        # Recompute hash
        cert_string = json.dumps(cert_copy, sort_keys=True, default=str)
        computed_hash = hashlib.sha256(cert_string.encode('utf-8')).hexdigest()
        
        if computed_hash == stored_hash:
            return True, "Hash verified successfully"
        else:
            return False, f"Hash mismatch: expected {stored_hash[:16]}..., got {computed_hash[:16]}..."
    
    def verify_file_hash(self, certificate: Dict[str, Any]) -> Tuple[bool, str]:
        """Verify the hash of the source file."""
        file_info = certificate.get("file_info", {})
        filepath = Path(file_info.get("path", ""))
        stored_hash = file_info.get("sha256")
        
        if not filepath.exists():
            return False, f"Source file not found: {filepath}"
        
        # Compute current file hash
        sha256 = hashlib.sha256()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b""):
                sha256.update(chunk)
        current_hash = sha256.hexdigest()
        
        if current_hash == stored_hash:
            return True, "File hash verified successfully"
        else:
            return False, f"File has been modified (hash mismatch)"
    
    def verify_sat_formula(self, certificate: Dict[str, Any]) -> Tuple[bool, str]:
        """Verify the SAT formula evaluation."""
        sat_formula = certificate.get("sat_formula", {})
        variables = sat_formula.get("variables", {})
        satisfied = sat_formula.get("satisfied", False)
        
        # Re-evaluate SAT formula
        all_conditions = all([
            v if v is not None else True 
            for v in variables.values()
        ])
        
        if all_conditions == satisfied:
            return True, f"SAT formula correctly evaluated: {satisfied}"
        else:
            return False, f"SAT formula evaluation error: expected {satisfied}, got {all_conditions}"
    
    def verify_dependencies(self, certificate: Dict[str, Any]) -> Tuple[bool, str]:
        """Verify theorem dependencies are satisfied."""
        dependencies = certificate.get("dependencies", [])
        
        # For now, just check dependencies are listed
        # In a full implementation, we would verify each dependency's certificate
        if isinstance(dependencies, list):
            return True, f"Dependencies listed: {len(dependencies)} items"
        else:
            return False, "Dependencies malformed"
    
    def verify_qcal_signature(self, certificate: Dict[str, Any]) -> Tuple[bool, str]:
        """Verify QCAL coherence signature."""
        qcal_sig = certificate.get("qcal_signature", {})
        
        expected_values = {
            "base_frequency": "141.7001 Hz",
            "coherence_constant": "C = 244.36",
            "field_equation": "Ψ = I × A_eff² × C^∞"
        }
        
        for key, expected_value in expected_values.items():
            if qcal_sig.get(key) != expected_value:
                return False, f"QCAL signature mismatch for {key}"
        
        return True, "QCAL signature verified"
    
    def validate_certificate(self, certificate: Dict[str, Any]) -> Dict[str, Any]:
        """Perform complete validation of a certificate."""
        
        theorem_name = certificate.get("theorem_name", "unknown")
        print(f"🔍 Validating certificate: {theorem_name}")
        
        validations = {
            "certificate_hash": self.verify_certificate_hash(certificate),
            "file_hash": self.verify_file_hash(certificate),
            "sat_formula": self.verify_sat_formula(certificate),
            "dependencies": self.verify_dependencies(certificate),
            "qcal_signature": self.verify_qcal_signature(certificate)
        }
        
        # Print results
        all_passed = True
        for check_name, (passed, message) in validations.items():
            status = "✅" if passed else "❌"
            print(f"   {status} {check_name}: {message}")
            all_passed = all_passed and passed
        
        result = {
            "theorem": theorem_name,
            "certificate_id": certificate.get("certificate_id"),
            "validation_timestamp": self.validation_timestamp,
            "all_checks_passed": all_passed,
            "checks": {
                name: {"passed": passed, "message": message}
                for name, (passed, message) in validations.items()
            }
        }
        
        print(f"   {'✅ VALID' if all_passed else '❌ INVALID'}")
        print()
        
        return result
    
    def validate_all_certificates(self) -> List[Dict[str, Any]]:
        """Validate all certificates in directory."""
        
        print("=" * 80)
        print("🔍 SAT Certificate Validator")
        print("=" * 80)
        print(f"Timestamp: {self.validation_timestamp}")
        print(f"Certificates directory: {self.certificates_dir}")
        print()
        
        if not self.certificates_dir.exists():
            print(f"❌ Certificates directory not found: {self.certificates_dir}")
            return []
        
        # Find all certificate files
        cert_files = list(self.certificates_dir.glob("SAT_*.json"))
        print(f"Found {len(cert_files)} certificate(s)")
        print()
        
        results = []
        for cert_file in cert_files:
            try:
                certificate = self.load_certificate(cert_file)
                result = self.validate_certificate(certificate)
                results.append(result)
            except Exception as e:
                print(f"❌ Error validating {cert_file.name}: {e}")
                print()
        
        # Generate summary
        total = len(results)
        passed = sum(1 for r in results if r["all_checks_passed"])
        
        print("=" * 80)
        print("✅ Validation Complete")
        print("=" * 80)
        print(f"Total certificates: {total}")
        print(f"Passed: {passed}/{total}")
        print(f"Failed: {total - passed}/{total}")
        
        # Save validation report
        report = {
            "validation_type": "SAT_CERTIFICATES_VALIDATION",
            "timestamp": self.validation_timestamp,
            "total_certificates": total,
            "passed": passed,
            "failed": total - passed,
            "results": results
        }
        
        report_path = self.certificates_dir / "validation_report.json"
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        print(f"Report saved to: {report_path}")
        print()
        
        return results


def main():
    parser = argparse.ArgumentParser(
        description="Validate SAT certificates for mathematical theorems"
    )
    parser.add_argument(
        '--certificate',
        type=str,
        help='Validate specific certificate file'
    )
    parser.add_argument(
        '--all',
        action='store_true',
        help='Validate all certificates in directory'
    )
    parser.add_argument(
        '--certificates-dir',
        type=str,
        default='certificates/sat',
        help='Directory containing certificates'
    )
    
    args = parser.parse_args()
    
    validator = SATCertificateValidator(certificates_dir=args.certificates_dir)
    
    if args.certificate:
        cert_path = Path(args.certificate)
        if not cert_path.exists():
            print(f"❌ Certificate file not found: {cert_path}")
            sys.exit(1)
        
        certificate = validator.load_certificate(cert_path)
        result = validator.validate_certificate(certificate)
        
        if not result["all_checks_passed"]:
            sys.exit(1)
    elif args.all:
        results = validator.validate_all_certificates()
        if not all(r["all_checks_passed"] for r in results):
            sys.exit(1)
    else:
        print("Please specify --certificate FILE or --all")
        sys.exit(1)


if __name__ == "__main__":
    main()
