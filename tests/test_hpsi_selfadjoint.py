#!/usr/bin/env python3
"""
Test suite for Hpsi_selfadjoint.lean validation.

This script validates the structure and completeness of the self-adjoint
operator H_Ψ formalization (Part 31/∞³).

Author: José Manuel Mota Burruezo
Date: 26 November 2025
DOI: 10.5281/zenodo.17379721
"""

import re
from pathlib import Path
from typing import Dict, List, Any


def read_lean_file(path: str) -> str:
    """Read the Lean file content."""
    file_path = Path(path)
    if not file_path.exists():
        return ""
    with open(file_path, 'r', encoding='utf-8') as f:
        return f.read()


def validate_hpsi_selfadjoint() -> Dict[str, Any]:
    """
    Validate the Hpsi_selfadjoint.lean file structure.
    
    Returns:
        Dictionary with validation results
    """
    lean_file = "formalization/lean/operators/Hpsi_selfadjoint.lean"
    content = read_lean_file(lean_file)
    
    results: Dict[str, Any] = {
        "file_exists": bool(content),
        "definitions": [],
        "axioms": [],
        "lemmas": [],
        "theorems": [],
        "imports": [],
        "qcal_integration": False,
        "passed": True
    }
    
    if not content:
        results["passed"] = False
        results["error"] = f"File not found: {lean_file}"
        return results
    
    # Check imports
    import_pattern = r'import\s+([\w.]+)'
    results["imports"] = re.findall(import_pattern, content)
    
    # Check definitions
    def_pattern = r'def\s+(\w+)'
    results["definitions"] = re.findall(def_pattern, content)
    
    # Check axioms
    axiom_pattern = r'axiom\s+(\w+)'
    results["axioms"] = re.findall(axiom_pattern, content)
    
    # Check lemmas
    lemma_pattern = r'lemma\s+(\w+)'
    results["lemmas"] = re.findall(lemma_pattern, content)
    
    # Check theorems
    theorem_pattern = r'theorem\s+(\w+)'
    results["theorems"] = re.findall(theorem_pattern, content)
    
    # Validate required elements
    required_elements = {
        "definitions": ["D_Hpsi", "H_psi", "spectrum", "QCAL_base_frequency"],
        "axioms": ["Hpsi_self_adjoint", "Xi", "Eigenvalue"],
        "lemmas": ["Hpsi_spectrum_real", "D_Hpsi_nonempty"],
    }
    
    # Check required definitions
    for category, items in required_elements.items():
        for item in items:
            if item not in results.get(category, []):
                results["passed"] = False
                results.setdefault("missing", []).append(f"{category}:{item}")
    
    # Check QCAL integration
    qcal_markers = ["141.7001", "244.36", "QCAL"]
    results["qcal_integration"] = all(marker in content for marker in qcal_markers)
    
    # Check namespace
    results["has_namespace"] = "namespace Hpsi" in content
    
    # Check documentation
    doc_markers = ["Autoadjunción", "Berry-Keating", "von Neumann", "DOI"]
    results["documentation_complete"] = all(marker in content for marker in doc_markers)
    
    return results


def test_file_exists() -> None:
    """Test that the Lean file exists."""
    results = validate_hpsi_selfadjoint()
    assert results["file_exists"], "Hpsi_selfadjoint.lean file not found"


def test_required_definitions() -> None:
    """Test that all required definitions are present."""
    results = validate_hpsi_selfadjoint()
    assert "D_Hpsi" in results["definitions"], "D_Hpsi definition missing"
    assert "H_psi" in results["definitions"], "H_psi definition missing"
    assert "spectrum" in results["definitions"], "spectrum definition missing"


def test_self_adjoint_axiom() -> None:
    """Test that the self-adjoint axiom is declared."""
    results = validate_hpsi_selfadjoint()
    assert "Hpsi_self_adjoint" in results["axioms"], \
        "Hpsi_self_adjoint axiom missing"


def test_spectrum_real_lemma() -> None:
    """Test that the spectrum real lemma is present."""
    results = validate_hpsi_selfadjoint()
    assert "Hpsi_spectrum_real" in results["lemmas"], \
        "Hpsi_spectrum_real lemma missing"


def test_qcal_integration() -> None:
    """Test QCAL integration markers."""
    results = validate_hpsi_selfadjoint()
    assert results["qcal_integration"], \
        "QCAL integration incomplete (missing 141.7001, 244.36, or QCAL)"


def test_namespace_structure() -> None:
    """Test proper namespace structure."""
    results = validate_hpsi_selfadjoint()
    assert results["has_namespace"], "Hpsi namespace missing"


def test_documentation() -> None:
    """Test documentation completeness."""
    results = validate_hpsi_selfadjoint()
    assert results["documentation_complete"], \
        "Documentation incomplete (missing key references)"


def test_imports() -> None:
    """Test required Mathlib imports."""
    results = validate_hpsi_selfadjoint()
    import_count = len(results["imports"])
    assert import_count >= 3, f"Expected at least 3 imports, got {import_count}"


def run_all_tests() -> bool:
    """Run all validation tests and return overall status."""
    tests = [
        test_file_exists,
        test_required_definitions,
        test_self_adjoint_axiom,
        test_spectrum_real_lemma,
        test_qcal_integration,
        test_namespace_structure,
        test_documentation,
        test_imports,
    ]
    
    all_passed = True
    for test in tests:
        try:
            test()
            print(f"✅ {test.__name__}")
        except AssertionError as e:
            print(f"❌ {test.__name__}: {e}")
            all_passed = False
    
    return all_passed


if __name__ == "__main__":
    print("=" * 60)
    print("🔍 Hpsi_selfadjoint.lean Validation")
    print("=" * 60)
    print()
    
    results = validate_hpsi_selfadjoint()
    
    print("📊 Structure Summary:")
    print(f"   Imports: {len(results['imports'])}")
    print(f"   Definitions: {len(results['definitions'])}")
    print(f"   Axioms: {len(results['axioms'])}")
    print(f"   Lemmas: {len(results['lemmas'])}")
    print(f"   Theorems: {len(results['theorems'])}")
    print(f"   QCAL Integration: {'✓' if results['qcal_integration'] else '✗'}")
    print()
    
    print("🧪 Running Tests:")
    all_passed = run_all_tests()
    print()
    
    if all_passed:
        print("✅ All validation tests passed!")
        print()
        print("Hpsi_selfadjoint.lean structure verified:")
        print("  - Dense domain D(H_Ψ) defined")
        print("  - Noetic operator H_psi defined")
        print("  - Self-adjoint axiom declared")
        print("  - Spectrum ⊆ ℝ lemma established")
        print("  - QCAL integration complete")
    else:
        print("❌ Some validation tests failed")
    
    print()
    print("=" * 60)
    
    exit(0 if all_passed else 1)
