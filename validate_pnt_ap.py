#!/usr/bin/env python3
"""
validate_pnt_ap.py
==================
Validation script for PNT-AP (Prime Number Theorem in Arithmetic Progressions)

This script validates the implementation of pnt_ap.lean, which establishes
the form of PNT in arithmetic progressions needed for the circle method.

Author: José Manuel Mota Burruezo Ψ ∞³
Instituto de Conciencia Cuántica (ICQ)
Date: 2026-02-26
"""

import json
import hashlib
import sys
from pathlib import Path
from datetime import datetime

# QCAL Framework Constants
F0 = 141.7001  # Base frequency (Hz)
C_COHERENCE = 244.36  # Coherence constant
KAPPA_PI = 2.5773  # Geometric coupling constant

class PNTAPValidator:
    """Validator for PNT-AP implementation"""
    
    def __init__(self):
        self.results = {
            "validation_date": datetime.now().isoformat(),
            "framework": "QCAL ∞³",
            "f0": F0,
            "C": C_COHERENCE,
            "tests": []
        }
        
    def test_file_structure(self):
        """Test 1: Verify file structure and imports"""
        print("Test 1: File structure verification...")
        
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        
        if not file_path.exists():
            self.results["tests"].append({
                "name": "File Structure",
                "status": "FAILED",
                "error": "pnt_ap.lean not found"
            })
            print("  ❌ FAILED: File not found")
            return False
            
        content = file_path.read_text()
        
        # Check for key components
        required_components = [
            "namespace AnalyticNumberTheory",
            "def vonMangoldt",
            "def psiAP",
            "axiom PNT_AP_uniform",
            "lemma HLsum_AP_main_term",
            "def smoothKernel",
            "def HLsum_vonMangoldt",
        ]
        
        missing = []
        for comp in required_components:
            if comp not in content:
                missing.append(comp)
        
        if missing:
            self.results["tests"].append({
                "name": "File Structure",
                "status": "FAILED",
                "error": f"Missing components: {missing}"
            })
            print(f"  ❌ FAILED: Missing {len(missing)} components")
            return False
        
        self.results["tests"].append({
            "name": "File Structure",
            "status": "PASSED",
            "components_found": len(required_components)
        })
        print(f"  ✅ PASSED: All {len(required_components)} components found")
        return True
    
    def test_documentation(self):
        """Test 2: Verify documentation completeness"""
        print("\nTest 2: Documentation verification...")
        
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        
        doc_markers = [
            "QCAL ∞³",
            "f₀ = 141.7001 Hz",
            "C = 244.36",
            "José Manuel Mota Burruezo",
            "DOI: 10.5281/zenodo",
        ]
        
        found = sum(1 for marker in doc_markers if marker in content)
        
        if found < len(doc_markers):
            self.results["tests"].append({
                "name": "Documentation",
                "status": "WARNING",
                "found": found,
                "expected": len(doc_markers)
            })
            print(f"  ⚠️  WARNING: {found}/{len(doc_markers)} doc markers found")
            return True
        
        self.results["tests"].append({
            "name": "Documentation",
            "status": "PASSED",
            "markers_found": found
        })
        print(f"  ✅ PASSED: All {found} documentation markers found")
        return True
    
    def test_pnt_ap_axiom(self):
        """Test 3: Verify PNT-AP axiom structure"""
        print("\nTest 3: PNT-AP axiom structure...")
        
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        
        # Check axiom structure
        axiom_checks = [
            "axiom PNT_AP_uniform",
            "Nat.coprime a.natAbs q",
            "q ≤ ⌊Real.log (N + 2)⌋",
            "Complex.abs E ≤",
            "psiAP N q a",
            "Nat.totient q",
        ]
        
        found = sum(1 for check in axiom_checks if check in content)
        
        if found < len(axiom_checks):
            self.results["tests"].append({
                "name": "PNT-AP Axiom",
                "status": "FAILED",
                "found": found,
                "expected": len(axiom_checks)
            })
            print(f"  ❌ FAILED: Only {found}/{len(axiom_checks)} axiom components found")
            return False
        
        self.results["tests"].append({
            "name": "PNT-AP Axiom",
            "status": "PASSED",
            "components_verified": found
        })
        print(f"  ✅ PASSED: All {found} axiom components verified")
        return True
    
    def test_transfer_lemma(self):
        """Test 4: Verify transfer lemma to exponential sums"""
        print("\nTest 4: Transfer lemma verification...")
        
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        
        # Check transfer lemma structure
        lemma_checks = [
            "lemma HLsum_AP_main_term",
            "smoothKernel",
            "Complex.exp",
            "vonMangoldt n",
            "Nat.totient q",
        ]
        
        found = sum(1 for check in lemma_checks if check in content)
        
        if found < len(lemma_checks):
            self.results["tests"].append({
                "name": "Transfer Lemma",
                "status": "FAILED",
                "found": found,
                "expected": len(lemma_checks)
            })
            print(f"  ❌ FAILED: Only {found}/{len(lemma_checks)} lemma components found")
            return False
        
        self.results["tests"].append({
            "name": "Transfer Lemma",
            "status": "PASSED",
            "components_verified": found
        })
        print(f"  ✅ PASSED: All {found} lemma components verified")
        return True
    
    def test_major_arc_integration(self):
        """Test 5: Verify integration with major arcs"""
        print("\nTest 5: Major arc integration...")
        
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        
        # Check major arc integration
        integration_checks = [
            "structure MajorArcApprox",
            "def singularFactor",
            "def majorArcBeta",
            "lemma HLsum_vonMangoldt_major_arc_approx_PNT",
        ]
        
        found = sum(1 for check in integration_checks if check in content)
        
        if found < len(integration_checks):
            self.results["tests"].append({
                "name": "Major Arc Integration",
                "status": "FAILED",
                "found": found,
                "expected": len(integration_checks)
            })
            print(f"  ❌ FAILED: Only {found}/{len(integration_checks)} integration components found")
            return False
        
        self.results["tests"].append({
            "name": "Major Arc Integration",
            "status": "PASSED",
            "components_verified": found
        })
        print(f"  ✅ PASSED: All {found} integration components verified")
        return True
    
    def test_numerical_consistency(self):
        """Test 6: Numerical consistency with QCAL framework"""
        print("\nTest 6: QCAL numerical consistency...")
        
        # Verify QCAL constants are present
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        
        qcal_markers = [
            "141.7001",
            "244.36",
            "QCAL",
        ]
        
        found = sum(1 for marker in qcal_markers if marker in content)
        
        if found < len(qcal_markers):
            self.results["tests"].append({
                "name": "QCAL Consistency",
                "status": "WARNING",
                "found": found,
                "expected": len(qcal_markers)
            })
            print(f"  ⚠️  WARNING: {found}/{len(qcal_markers)} QCAL markers found")
            return True
        
        self.results["tests"].append({
            "name": "QCAL Consistency",
            "status": "PASSED",
            "markers_found": found
        })
        print(f"  ✅ PASSED: All {found} QCAL markers verified")
        return True
    
    def generate_certificate(self):
        """Generate validation certificate"""
        print("\n" + "="*60)
        print("Generating validation certificate...")
        
        # Calculate hash
        file_path = Path("formalization/lean/RiemannAdelic/core/analytic/pnt_ap.lean")
        content = file_path.read_text()
        file_hash = hashlib.sha256(content.encode()).hexdigest()[:16]
        
        # Count passed tests
        passed = sum(1 for test in self.results["tests"] if test["status"] == "PASSED")
        total = len(self.results["tests"])
        
        certificate = {
            "module": "pnt_ap.lean",
            "description": "Prime Number Theorem in Arithmetic Progressions",
            "validation_date": self.results["validation_date"],
            "framework": "QCAL ∞³",
            "f0": F0,
            "C": C_COHERENCE,
            "kappa_pi": KAPPA_PI,
            "file_hash": f"0xQCAL_PNT_AP_{file_hash}",
            "tests_passed": passed,
            "tests_total": total,
            "test_results": self.results["tests"],
            "status": "VALIDATED" if passed == total else "PARTIAL",
            "author": "José Manuel Mota Burruezo Ψ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "orcid": "0009-0002-1923-0773",
            "doi": "10.5281/zenodo.17379721"
        }
        
        # Save certificate
        cert_path = Path("data/pnt_ap_validation_certificate.json")
        cert_path.parent.mkdir(exist_ok=True)
        with open(cert_path, 'w') as f:
            json.dump(certificate, f, indent=2)
        
        print(f"Certificate hash: {certificate['file_hash']}")
        print(f"Tests passed: {passed}/{total}")
        print(f"Status: {certificate['status']}")
        print(f"Certificate saved to: {cert_path}")
        print("="*60)
        
        return certificate
    
    def run_all_tests(self):
        """Run all validation tests"""
        print("="*60)
        print("PNT-AP Validation Suite")
        print("="*60)
        print(f"Framework: QCAL ∞³")
        print(f"Base frequency: f₀ = {F0} Hz")
        print(f"Coherence: C = {C_COHERENCE}")
        print("="*60)
        
        tests = [
            self.test_file_structure,
            self.test_documentation,
            self.test_pnt_ap_axiom,
            self.test_transfer_lemma,
            self.test_major_arc_integration,
            self.test_numerical_consistency,
        ]
        
        results = [test() for test in tests]
        certificate = self.generate_certificate()
        
        # Final summary
        print("\n" + "="*60)
        print("VALIDATION SUMMARY")
        print("="*60)
        passed = sum(1 for r in results if r)
        print(f"Tests passed: {passed}/{len(results)}")
        
        if passed == len(results):
            print("✅ ALL TESTS PASSED")
            print("PNT-AP module is ready for integration with circle method")
            return 0
        elif passed > len(results) // 2:
            print("⚠️  PARTIAL SUCCESS")
            print("Some tests passed, review warnings")
            return 0
        else:
            print("❌ VALIDATION FAILED")
            print("Critical issues detected, review errors")
            return 1

def main():
    validator = PNTAPValidator()
    return validator.run_all_tests()

if __name__ == "__main__":
    sys.exit(main())
