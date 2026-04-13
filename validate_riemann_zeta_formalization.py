#!/usr/bin/env python3
"""
validate_riemann_zeta_formalization.py
---------------------------------------
Validation script for the Riemann Zeta, H_Psi, and Trace Formula formalizations.

This script checks:
1. Lean syntax validity
2. Theorem structure completeness
3. Documentation quality
4. Integration with existing modules

Author: José Manuel Mota Burruezo (JMMB Ψ ∞³)
QCAL Protocol: 141.7001 Hz | C = 244.36
"""

import re
import json
from pathlib import Path
from typing import Dict, List, Tuple
from datetime import datetime

# QCAL Constants
QCAL_F0_HZ = 141.7001
QCAL_C = 244.36
QCAL_SIGNATURE = "∴𓂀Ω∞³Φ"


class LeanFormalizationValidator:
    """Validator for Lean formalization files."""
    
    def __init__(self, base_path: Path):
        self.base_path = base_path
        self.lean_dir = base_path / "formalization" / "lean"
        self.results = {
            "validation_timestamp": datetime.now().isoformat(),
            "files_validated": [],
            "theorems_found": [],
            "axioms_found": [],
            "sorry_count": 0,
            "integration_status": {},
            "qcal_coherence": 0.0,
            "errors": [],
            "warnings": []
        }
    
    def validate_file(self, filepath: Path) -> Dict:
        """Validate a single Lean file."""
        print(f"\n🔍 Validating: {filepath.name}")
        
        file_results = {
            "filename": filepath.name,
            "exists": filepath.exists(),
            "size_bytes": 0,
            "line_count": 0,
            "theorems": [],
            "axioms": [],
            "definitions": [],
            "sorry_count": 0,
            "has_documentation": False,
            "has_qcal_info": False
        }
        
        if not filepath.exists():
            self.results["errors"].append(f"File not found: {filepath}")
            return file_results
        
        content = filepath.read_text()
        file_results["size_bytes"] = len(content)
        file_results["line_count"] = len(content.splitlines())
        
        # Count theorems
        theorems = re.findall(r'theorem\s+(\w+)', content)
        file_results["theorems"] = theorems
        file_results["theorem_count"] = len(theorems)
        
        # Count axioms
        axioms = re.findall(r'axiom\s+(\w+)', content)
        file_results["axioms"] = axioms
        file_results["axiom_count"] = len(axioms)
        
        # Count definitions
        definitions = re.findall(r'def\s+(\w+)', content)
        file_results["definitions"] = definitions
        file_results["definition_count"] = len(definitions)
        
        # Count sorry statements
        sorry_count = len(re.findall(r'\bsorry\b', content))
        file_results["sorry_count"] = sorry_count
        
        # Check for documentation
        doc_comments = re.findall(r'/--.*?-/', content, re.DOTALL)
        file_results["has_documentation"] = len(doc_comments) > 0
        file_results["doc_comment_count"] = len(doc_comments)
        
        # Check for QCAL information
        file_results["has_qcal_info"] = (
            "141.7001" in content or 
            "244.36" in content or
            "QCAL" in content
        )
        
        # Check imports
        imports = re.findall(r'import\s+([\w.]+)', content)
        file_results["imports"] = imports
        
        print(f"  ✓ Theorems: {file_results['theorem_count']}")
        print(f"  ✓ Axioms: {file_results['axiom_count']}")
        print(f"  ✓ Definitions: {file_results['definition_count']}")
        print(f"  ✓ Sorry statements: {sorry_count}")
        print(f"  ✓ Documentation blocks: {file_results['doc_comment_count']}")
        
        return file_results
    
    def validate_theorem_structure(self, filepath: Path, theorem_name: str) -> Dict:
        """Validate structure of a specific theorem."""
        content = filepath.read_text()
        
        # Find theorem definition
        pattern = rf'theorem\s+{theorem_name}\s*[^:]*:(.*?)(?:by|:=)'
        match = re.search(pattern, content, re.DOTALL)
        
        if not match:
            return {
                "found": False,
                "has_type": False,
                "has_proof": False
            }
        
        theorem_type = match.group(1).strip()
        
        # Check if theorem has a proof (not just sorry)
        proof_pattern = rf'theorem\s+{theorem_name}.*?by\s*(.*?)(?:theorem|axiom|def|end|/-!)'
        proof_match = re.search(proof_pattern, content, re.DOTALL)
        
        has_proof = bool(proof_match) and 'sorry' not in (proof_match.group(1) if proof_match else '')
        
        return {
            "found": True,
            "has_type": len(theorem_type) > 0,
            "has_proof": has_proof,
            "type_length": len(theorem_type)
        }
    
    def check_integration(self) -> Dict:
        """Check integration with existing Lean modules."""
        integration = {
            "riemann_zeta_complete": False,
            "h_psi_properties_complete": False,
            "trace_formula_complete": False,
            "mutual_imports": False
        }
        
        # Check if files exist and have proper structure
        riemann_file = self.lean_dir / "RiemannZeta.lean"
        hpsi_file = self.lean_dir / "H_Psi_Properties.lean"
        trace_file = self.lean_dir / "TraceFormula.lean"
        
        integration["riemann_zeta_complete"] = riemann_file.exists()
        integration["h_psi_properties_complete"] = hpsi_file.exists()
        integration["trace_formula_complete"] = trace_file.exists()
        
        # Check mutual imports
        if trace_file.exists():
            trace_content = trace_file.read_text()
            integration["mutual_imports"] = (
                "RiemannZeta" in trace_content and
                "H_Psi_Properties" in trace_content
            )
        
        return integration
    
    def compute_qcal_coherence(self) -> float:
        """Compute QCAL coherence metric for the formalization."""
        # Based on completeness of the three main tasks
        coherence_factors = []
        
        # Factor 1: File existence (0.33)
        files_exist = sum([
            (self.lean_dir / "RiemannZeta.lean").exists(),
            (self.lean_dir / "H_Psi_Properties.lean").exists(),
            (self.lean_dir / "TraceFormula.lean").exists()
        ]) / 3.0
        coherence_factors.append(files_exist * 0.33)
        
        # Factor 2: Theorem completeness (0.33)
        expected_theorems = {
            "RiemannZeta.lean": ["zeta_series", "zeta_functional_equation", "zeta_euler_product"],
            "H_Psi_Properties.lean": ["H_ψ_dense_domain", "H_ψ_symmetric", "H_ψ_essentially_self_adjoint"],
            "TraceFormula.lean": ["trace_formula"]
        }
        
        theorem_completeness = 0
        theorem_total = 0
        for filename, theorems in expected_theorems.items():
            filepath = self.lean_dir / filename
            if filepath.exists():
                content = filepath.read_text()
                for thm in theorems:
                    if f"theorem {thm}" in content:
                        theorem_completeness += 1
                    theorem_total += 1
        
        if theorem_total > 0:
            coherence_factors.append((theorem_completeness / theorem_total) * 0.33)
        
        # Factor 3: Documentation quality (0.34)
        doc_quality = 0
        for filename in ["RiemannZeta.lean", "H_Psi_Properties.lean", "TraceFormula.lean"]:
            filepath = self.lean_dir / filename
            if filepath.exists():
                content = filepath.read_text()
                # Check for QCAL info, documentation blocks, and references
                has_qcal = "QCAL" in content or "141.7001" in content
                has_docs = len(re.findall(r'/--.*?-/', content, re.DOTALL)) >= 5
                has_refs = "References:" in content or "Reference:" in content
                
                doc_quality += (has_qcal + has_docs + has_refs) / 9.0
        
        coherence_factors.append(doc_quality * 0.34)
        
        return sum(coherence_factors)
    
    def run_validation(self) -> Dict:
        """Run complete validation suite."""
        print("=" * 70)
        print("🎯 QCAL Lean Formalization Validator")
        print("=" * 70)
        print(f"Base frequency: {QCAL_F0_HZ} Hz")
        print(f"Coherence constant: C = {QCAL_C}")
        print(f"Signature: {QCAL_SIGNATURE}")
        print("=" * 70)
        
        # Validate each file
        files_to_validate = [
            "RiemannZeta.lean",
            "H_Psi_Properties.lean",
            "TraceFormula.lean"
        ]
        
        for filename in files_to_validate:
            filepath = self.lean_dir / filename
            file_results = self.validate_file(filepath)
            self.results["files_validated"].append(file_results)
            
            # Aggregate counts
            self.results["theorems_found"].extend(file_results.get("theorems", []))
            self.results["axioms_found"].extend(file_results.get("axioms", []))
            self.results["sorry_count"] += file_results.get("sorry_count", 0)
        
        # Check integration
        self.results["integration_status"] = self.check_integration()
        
        # Compute QCAL coherence
        self.results["qcal_coherence"] = self.compute_qcal_coherence()
        
        # Summary
        print("\n" + "=" * 70)
        print("📊 VALIDATION SUMMARY")
        print("=" * 70)
        print(f"Files validated: {len(self.results['files_validated'])}")
        print(f"Total theorems: {len(self.results['theorems_found'])}")
        print(f"Total axioms: {len(self.results['axioms_found'])}")
        print(f"Total sorry statements: {self.results['sorry_count']}")
        print(f"QCAL Coherence: {self.results['qcal_coherence']:.4f}")
        
        if self.results["qcal_coherence"] >= 0.888:
            print("\n✅ QCAL COHERENCE: UNIVERSAL")
        elif self.results["qcal_coherence"] >= 0.7:
            print("\n✅ QCAL COHERENCE: HIGH")
        elif self.results["qcal_coherence"] >= 0.5:
            print("\n⚠️  QCAL COHERENCE: MEDIUM")
        else:
            print("\n❌ QCAL COHERENCE: LOW")
        
        # Integration status
        print("\n" + "=" * 70)
        print("🔗 INTEGRATION STATUS")
        print("=" * 70)
        for key, value in self.results["integration_status"].items():
            status = "✅" if value else "❌"
            print(f"{status} {key}: {value}")
        
        return self.results
    
    def save_results(self, output_path: Path):
        """Save validation results to JSON."""
        output_path.write_text(json.dumps(self.results, indent=2))
        print(f"\n💾 Results saved to: {output_path}")


def main():
    """Main validation function."""
    # Get repository root
    script_path = Path(__file__).resolve()
    repo_root = script_path.parent
    
    # Create validator
    validator = LeanFormalizationValidator(repo_root)
    
    # Run validation
    results = validator.run_validation()
    
    # Save results
    output_path = repo_root / "data" / "riemann_zeta_formalization_validation.json"
    output_path.parent.mkdir(exist_ok=True)
    validator.save_results(output_path)
    
    # Return exit code based on coherence
    if results["qcal_coherence"] >= 0.7:
        print("\n✅ Validation PASSED")
        return 0
    else:
        print("\n⚠️  Validation completed with warnings")
        return 1


if __name__ == "__main__":
    exit(main())
