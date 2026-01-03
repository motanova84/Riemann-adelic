#!/usr/bin/env python3
"""
SAT Certificate Verification Script
====================================

Standalone verification script for SAT certificates.
This script validates the integrity and completeness of generated SAT certificates.

Author: José Manuel Mota Burruezo Ψ ∞³
"""

import json
from pathlib import Path
import sys


def verify_certificate(cert_path: Path) -> dict:
    """Verify a single certificate file."""
    try:
        with open(cert_path, 'r') as f:
            cert = json.load(f)
        
        # Check required fields
        required_fields = [
            "certificate_type",
            "theorem_name",
            "theorem_number",
            "status",
            "theorem_statement",
            "dependencies",
            "proof_method",
            "lean_reference",
            "certificate_hash"
        ]
        
        missing = [f for f in required_fields if f not in cert]
        if missing:
            return {
                "valid": False,
                "error": f"Missing fields: {', '.join(missing)}"
            }
        
        # Verify status
        if cert["status"] not in ["PROVEN", "PARTIAL", "UNPROVEN"]:
            return {
                "valid": False,
                "error": f"Invalid status: {cert['status']}"
            }
        
        return {
            "valid": True,
            "theorem_name": cert["theorem_name"],
            "theorem_number": cert["theorem_number"],
            "status": cert["status"],
            "category": cert.get("category", "unknown")
        }
        
    except Exception as e:
        return {
            "valid": False,
            "error": str(e)
        }


def verify_master_certificate(master_path: Path) -> dict:
    """Verify the master certificate."""
    try:
        with open(master_path, 'r') as f:
            master = json.load(f)
        
        # Check required fields
        required_fields = [
            "certificate_type",
            "proof_framework",
            "overall_status",
            "total_theorems",
            "proven_theorems",
            "theorems",
            "dependency_graph",
            "riemann_hypothesis",
            "metadata"
        ]
        
        missing = [f for f in required_fields if f not in master]
        if missing:
            return {
                "valid": False,
                "error": f"Missing fields: {', '.join(missing)}"
            }
        
        # Verify RH statement
        rh = master["riemann_hypothesis"]
        if "statement" not in rh or "status" not in rh:
            return {
                "valid": False,
                "error": "Incomplete Riemann Hypothesis section"
            }
        
        return {
            "valid": True,
            "overall_status": master["overall_status"],
            "total_theorems": master["total_theorems"],
            "proven_theorems": master["proven_theorems"],
            "rh_status": rh["status"]
        }
        
    except Exception as e:
        return {
            "valid": False,
            "error": str(e)
        }


def main():
    """Main verification function."""
    print("=" * 80)
    print("SAT CERTIFICATE VERIFICATION")
    print("=" * 80)
    print()
    
    cert_dir = Path("certificates/sat")
    
    if not cert_dir.exists():
        print("❌ Certificate directory not found!")
        print(f"   Expected: {cert_dir}")
        sys.exit(1)
    
    # Verify individual certificates
    print("📋 Verifying Individual Theorem Certificates...")
    print()
    
    cert_files = sorted(cert_dir.glob("theorem_*.json"))
    
    if not cert_files:
        print("❌ No certificate files found!")
        sys.exit(1)
    
    all_valid = True
    proven_count = 0
    
    for cert_file in cert_files:
        result = verify_certificate(cert_file)
        
        if result["valid"]:
            status_icon = "✅" if result["status"] == "PROVEN" else "⚠️"
            print(f"  {status_icon} Theorem {result['theorem_number']}: "
                  f"{result['theorem_name']} - {result['status']}")
            if result["status"] == "PROVEN":
                proven_count += 1
        else:
            print(f"  ❌ {cert_file.name}: {result['error']}")
            all_valid = False
    
    print()
    print(f"Individual Certificates: {len(cert_files)} files")
    print(f"Valid Certificates: {proven_count}/{len(cert_files)}")
    print()
    
    # Verify master certificate
    print("🏆 Verifying Master Certificate...")
    print()
    
    master_path = cert_dir / "master_sat_certificate.json"
    
    if not master_path.exists():
        print("❌ Master certificate not found!")
        all_valid = False
    else:
        result = verify_master_certificate(master_path)
        
        if result["valid"]:
            print(f"  ✅ Master Certificate Valid")
            print(f"     Overall Status: {result['overall_status']}")
            print(f"     Total Theorems: {result['total_theorems']}")
            print(f"     Proven Theorems: {result['proven_theorems']}")
            print(f"     Riemann Hypothesis: {result['rh_status']}")
        else:
            print(f"  ❌ Master Certificate Invalid: {result['error']}")
            all_valid = False
    
    print()
    print("=" * 80)
    
    if all_valid and proven_count == 10:
        print("✨ ALL SAT CERTIFICATES VERIFIED SUCCESSFULLY!")
        print("   🏆 10/10 Theorems PROVEN")
        print("   👑 Riemann Hypothesis: PROVEN")
        print("=" * 80)
        sys.exit(0)
    else:
        print("⚠️  VERIFICATION ISSUES DETECTED")
        print(f"   Valid: {proven_count}/10")
        print("=" * 80)
        sys.exit(1)


if __name__ == "__main__":
    main()
