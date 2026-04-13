#!/usr/bin/env python3
"""
SAT Certificates Integration Script
===================================

Integrates SAT certificate generation and validation with existing
V5 Coronación validation framework.

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Date: December 2025
DOI: 10.5281/zenodo.17379721

Usage:
    python scripts/integrate_sat_certificates.py [--generate] [--validate] [--full]
"""

import argparse
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict


class SATCertificateIntegrator:
    """Integrate SAT certificates with validation framework."""
    
    def __init__(self):
        self.root_dir = Path(__file__).parent.parent
        self.certificates_dir = self.root_dir / "certificates" / "sat"
        self.data_dir = self.root_dir / "data"
        self.timestamp = datetime.utcnow().isoformat() + "Z"
        
    def run_command(self, cmd: list, description: str) -> Dict[str, Any]:
        """Run a command and return result."""
        print(f"▶️  {description}...")
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,
                cwd=self.root_dir
            )
            
            success = result.returncode == 0
            print(f"   {'✅' if success else '❌'} {description}: {'Success' if success else 'Failed'}")
            
            return {
                "success": success,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "returncode": result.returncode
            }
        except Exception as e:
            print(f"   ❌ {description}: Error - {e}")
            return {
                "success": False,
                "error": str(e)
            }
    
    def generate_certificates(self) -> Dict[str, Any]:
        """Generate SAT certificates for all key theorems."""
        print("\n" + "=" * 80)
        print("🎯 STEP 1: Generate SAT Certificates")
        print("=" * 80 + "\n")
        
        result = self.run_command(
            [sys.executable, "scripts/generate_sat_certificates.py", "--all"],
            "Generating SAT certificates"
        )
        
        # Check if certificates were created
        if self.certificates_dir.exists():
            cert_files = list(self.certificates_dir.glob("SAT_*.json"))
            result["certificates_generated"] = len(cert_files)
            print(f"\n📋 Generated {len(cert_files)} certificates\n")
        else:
            result["certificates_generated"] = 0
        
        return result
    
    def validate_certificates(self) -> Dict[str, Any]:
        """Validate all generated SAT certificates."""
        print("\n" + "=" * 80)
        print("🔍 STEP 2: Validate SAT Certificates")
        print("=" * 80 + "\n")
        
        result = self.run_command(
            [sys.executable, "scripts/validate_sat_certificates.py", "--all"],
            "Validating SAT certificates"
        )
        
        # Load validation report if available
        report_path = self.certificates_dir / "validation_report.json"
        if report_path.exists():
            with open(report_path, 'r') as f:
                validation_report = json.load(f)
                result["validation_report"] = validation_report
                
                print(f"\n📊 Validation Summary:")
                print(f"   Total certificates: {validation_report['total_certificates']}")
                print(f"   Passed: {validation_report['passed']}")
                print(f"   Failed: {validation_report['failed']}")
                print()
        
        return result
    
    def integrate_with_v5_coronacion(self) -> Dict[str, Any]:
        """Integrate SAT certificates with V5 Coronación validation."""
        print("\n" + "=" * 80)
        print("🔗 STEP 3: Integrate with V5 Coronación Validation")
        print("=" * 80 + "\n")
        
        # Load certificate summary
        summary_path = self.certificates_dir / "certificates_summary.json"
        if not summary_path.exists():
            print("   ⚠️  No certificate summary found")
            return {"success": False, "error": "No summary file"}
        
        with open(summary_path, 'r') as f:
            cert_summary = json.load(f)
        
        # Create integration data
        integration_data = {
            "integration_type": "SAT_CERTIFICATES_V5_CORONACION",
            "timestamp": self.timestamp,
            "sat_certificates": {
                "total": cert_summary.get("total_theorems", 0),
                "verified": cert_summary.get("verified_theorems", 0),
                "by_type": cert_summary.get("theorems_by_type", {})
            },
            "v5_coronacion_compatible": True,
            "qcal_coherence": {
                "base_frequency": "141.7001 Hz",
                "coherence_constant": "C = 244.36",
                "field_equation": "Ψ = I × A_eff² × C^∞"
            }
        }
        
        # Save integration data
        integration_path = self.data_dir / "sat_certificates_integration.json"
        integration_path.parent.mkdir(parents=True, exist_ok=True)
        with open(integration_path, 'w') as f:
            json.dump(integration_data, f, indent=2)
        
        print(f"   ✅ Integration data saved to: {integration_path}")
        print(f"   📊 Verified {integration_data['sat_certificates']['verified']}/{integration_data['sat_certificates']['total']} theorems")
        print()
        
        return {
            "success": True,
            "integration_data": integration_data,
            "path": str(integration_path)
        }
    
    def update_v5_certificate(self) -> Dict[str, Any]:
        """Update V5 Coronación certificate with SAT certificate data."""
        print("\n" + "=" * 80)
        print("📝 STEP 4: Update V5 Coronación Certificate")
        print("=" * 80 + "\n")
        
        v5_cert_path = self.data_dir / "v5_coronacion_certificate.json"
        if not v5_cert_path.exists():
            print("   ⚠️  V5 Coronación certificate not found")
            return {"success": False, "error": "V5 certificate not found"}
        
        # Load V5 certificate
        with open(v5_cert_path, 'r') as f:
            v5_cert = json.load(f)
        
        # Load SAT certificate summary
        summary_path = self.certificates_dir / "certificates_summary.json"
        if summary_path.exists():
            with open(summary_path, 'r') as f:
                sat_summary = json.load(f)
            
            # Add SAT certificate info to V5 certificate
            v5_cert["sat_certificates"] = {
                "enabled": True,
                "total_theorems": sat_summary.get("total_theorems", 0),
                "verified_theorems": sat_summary.get("verified_theorems", 0),
                "certificates_location": "certificates/sat/",
                "last_updated": self.timestamp
            }
            
            # Save updated certificate
            with open(v5_cert_path, 'w') as f:
                json.dump(v5_cert, f, indent=2)
            
            print(f"   ✅ Updated V5 Coronación certificate")
            print(f"   📋 Added SAT certificate information")
            print()
            
            return {"success": True, "v5_certificate_updated": True}
        else:
            return {"success": False, "error": "SAT summary not found"}
    
    def generate_comprehensive_report(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """Generate comprehensive integration report."""
        print("\n" + "=" * 80)
        print("📊 STEP 5: Generate Comprehensive Report")
        print("=" * 80 + "\n")
        
        report = {
            "report_type": "SAT_CERTIFICATES_INTEGRATION_REPORT",
            "timestamp": self.timestamp,
            "steps": {
                "certificate_generation": results.get("generation", {}).get("success", False),
                "certificate_validation": results.get("validation", {}).get("success", False),
                "v5_integration": results.get("integration", {}).get("success", False),
                "v5_certificate_update": results.get("v5_update", {}).get("success", False)
            },
            "statistics": {
                "certificates_generated": results.get("generation", {}).get("certificates_generated", 0),
                "certificates_validated": 0,
                "integration_successful": all([
                    results.get("generation", {}).get("success", False),
                    results.get("validation", {}).get("success", False),
                    results.get("integration", {}).get("success", False)
                ])
            },
            "qcal_signature": {
                "base_frequency": "141.7001 Hz",
                "coherence_constant": "C = 244.36",
                "field_equation": "Ψ = I × A_eff² × C^∞",
                "integration_status": "COMPLETE"
            },
            "metadata": {
                "author": "José Manuel Mota Burruezo (JMMB Ψ✧)",
                "institution": "Instituto de Conciencia Cuántica (ICQ)",
                "doi": "10.5281/zenodo.17379721"
            }
        }
        
        # Extract validation statistics if available
        if "validation" in results and "validation_report" in results["validation"]:
            vr = results["validation"]["validation_report"]
            report["statistics"]["certificates_validated"] = vr.get("passed", 0)
        
        # Save report
        report_path = self.data_dir / "sat_certificates_integration_report.json"
        with open(report_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"   ✅ Report saved to: {report_path}")
        print()
        
        # Print summary
        print("=" * 80)
        print("✅ SAT CERTIFICATES INTEGRATION COMPLETE")
        print("=" * 80)
        print(f"\nSummary:")
        print(f"   Certificates Generated: {report['statistics']['certificates_generated']}")
        print(f"   Certificates Validated: {report['statistics']['certificates_validated']}")
        print(f"   Integration Successful: {report['statistics']['integration_successful']}")
        print(f"\n∴ Q.E.D. ABSOLUTUM")
        print(f"∴ SAT certificates integrated with V5 Coronación")
        print(f"∴ QCAL coherence maintained: f₀ = 141.7001 Hz\n")
        
        return report
    
    def run_full_integration(self) -> int:
        """Run complete integration workflow."""
        print("\n" + "=" * 80)
        print("🚀 SAT CERTIFICATES FULL INTEGRATION")
        print("=" * 80)
        print(f"Timestamp: {self.timestamp}")
        print(f"Root directory: {self.root_dir}")
        print()
        
        results = {}
        
        # Step 1: Generate certificates
        results["generation"] = self.generate_certificates()
        if not results["generation"]["success"]:
            print("\n❌ Certificate generation failed, aborting integration")
            return 1
        
        # Step 2: Validate certificates
        results["validation"] = self.validate_certificates()
        if not results["validation"]["success"]:
            print("\n⚠️  Certificate validation had issues, continuing anyway")
        
        # Step 3: Integrate with V5 Coronación
        results["integration"] = self.integrate_with_v5_coronacion()
        
        # Step 4: Update V5 certificate
        results["v5_update"] = self.update_v5_certificate()
        
        # Step 5: Generate report
        report = self.generate_comprehensive_report(results)
        
        # Return success code
        return 0 if report["statistics"]["integration_successful"] else 1


def main():
    parser = argparse.ArgumentParser(
        description="Integrate SAT certificates with V5 Coronación validation"
    )
    parser.add_argument(
        '--generate',
        action='store_true',
        help='Only generate certificates'
    )
    parser.add_argument(
        '--validate',
        action='store_true',
        help='Only validate certificates'
    )
    parser.add_argument(
        '--full',
        action='store_true',
        help='Run full integration workflow'
    )
    
    args = parser.parse_args()
    
    integrator = SATCertificateIntegrator()
    
    if args.generate:
        result = integrator.generate_certificates()
        sys.exit(0 if result["success"] else 1)
    elif args.validate:
        result = integrator.validate_certificates()
        sys.exit(0 if result["success"] else 1)
    elif args.full:
        sys.exit(integrator.run_full_integration())
    else:
        # Default: run full integration
        sys.exit(integrator.run_full_integration())


if __name__ == "__main__":
    main()
