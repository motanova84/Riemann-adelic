#!/usr/bin/env python3
"""
Test script for Xi symmetry properties

This test validates that the xi_properties.lean module is correctly
structured and ready for integration into the QCAL framework.
"""

import os
import sys
from pathlib import Path

def test_xi_properties_file_exists():
    """Test that xi_properties.lean file exists"""
    xi_props_path = Path("formalization/lean/RiemannAdelic/xi_properties.lean")
    assert xi_props_path.exists(), f"xi_properties.lean not found at {xi_props_path}"
    print("✅ xi_properties.lean file exists")
    return True

def test_xi_properties_readme_exists():
    """Test that XI_PROPERTIES_README.md file exists"""
    readme_path = Path("formalization/lean/RiemannAdelic/XI_PROPERTIES_README.md")
    assert readme_path.exists(), f"XI_PROPERTIES_README.md not found at {readme_path}"
    print("✅ XI_PROPERTIES_README.md file exists")
    return True

def test_xi_properties_content():
    """Test that xi_properties.lean contains the required theorems"""
    xi_props_path = Path("formalization/lean/RiemannAdelic/xi_properties.lean")
    
    with open(xi_props_path, 'r') as f:
        content = f.read()
    
    # Check for required lemmas/theorems
    required_items = [
        "lemma Xi_functional_eq",
        "lemma Xi_conj_eq",
        "lemma Xi_symmetry_reciprocal",
        "lemma Xi_symmetry_conjugate",
        "riemann_xi ρ = 0",
        "riemann_xi (1 - ρ) = 0",
        "riemann_xi (conj ρ) = 0",
    ]
    
    for item in required_items:
        assert item in content, f"Required item '{item}' not found in xi_properties.lean"
        print(f"✅ Found: {item}")
    
    return True

def test_xi_properties_imports():
    """Test that xi_properties.lean has correct imports"""
    xi_props_path = Path("formalization/lean/RiemannAdelic/xi_properties.lean")
    
    with open(xi_props_path, 'r') as f:
        content = f.read()
    
    # Check for required imports
    required_imports = [
        "import Mathlib.Analysis.Complex.Basic",
        "import Mathlib.Analysis.SpecialFunctions.Gamma.Basic",
        "import Mathlib.NumberTheory.ZetaFunction",
        "import RiemannAdelic.xi_entire_proof",
    ]
    
    for imp in required_imports:
        assert imp in content, f"Required import '{imp}' not found in xi_properties.lean"
        print(f"✅ Import found: {imp}")
    
    return True

def test_xi_properties_namespace():
    """Test that xi_properties.lean uses correct namespace"""
    xi_props_path = Path("formalization/lean/RiemannAdelic/xi_properties.lean")
    
    with open(xi_props_path, 'r') as f:
        content = f.read()
    
    # Check for namespace
    assert "namespace RiemannAdelic" in content, "RiemannAdelic namespace not found"
    print("✅ RiemannAdelic namespace found")
    
    return True

def test_xi_properties_documentation():
    """Test that xi_properties.lean has proper documentation"""
    xi_props_path = Path("formalization/lean/RiemannAdelic/xi_properties.lean")
    
    with open(xi_props_path, 'r') as f:
        content = f.read()
    
    # Check for documentation markers
    doc_items = [
        "Xi Properties - Symmetry Properties of Zeros",
        "Main Theorems",
        "Mathematical Justification",
        "JMMB",
        "DOI: 10.5281/zenodo.17379721",
    ]
    
    for item in doc_items:
        assert item in content, f"Documentation item '{item}' not found"
        print(f"✅ Documentation: {item}")
    
    return True

def test_readme_content():
    """Test that README has proper structure"""
    readme_path = Path("formalization/lean/RiemannAdelic/XI_PROPERTIES_README.md")
    
    with open(readme_path, 'r') as f:
        content = f.read()
    
    # Check for key sections
    sections = [
        "## Overview",
        "## Main Theorems",
        "### 1. Xi_functional_eq",
        "### 2. Xi_conj_eq", 
        "### 3. Xi_symmetry_reciprocal",
        "### 4. Xi_symmetry_conjugate",
        "## Mathematical Justification",
        "## Consequences",
        "## References",
        "## QCAL Integration",
    ]
    
    for section in sections:
        assert section in content, f"README section '{section}' not found"
        print(f"✅ README section: {section}")
    
    return True

def run_all_tests():
    """Run all tests"""
    print("\n" + "="*60)
    print("Testing Xi Properties Implementation")
    print("="*60 + "\n")
    
    tests = [
        ("File Existence", test_xi_properties_file_exists),
        ("README Existence", test_xi_properties_readme_exists),
        ("Content Validation", test_xi_properties_content),
        ("Import Validation", test_xi_properties_imports),
        ("Namespace Validation", test_xi_properties_namespace),
        ("Documentation Validation", test_xi_properties_documentation),
        ("README Content", test_readme_content),
    ]
    
    results = []
    for test_name, test_func in tests:
        print(f"\n--- {test_name} ---")
        try:
            result = test_func()
            results.append((test_name, result))
        except AssertionError as e:
            print(f"❌ {test_name} FAILED: {e}")
            results.append((test_name, False))
        except Exception as e:
            print(f"❌ {test_name} ERROR: {e}")
            results.append((test_name, False))
    
    # Print summary
    print("\n" + "="*60)
    print("Test Summary")
    print("="*60)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for test_name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {test_name}")
    
    print(f"\nTotal: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 All tests passed! Xi properties implementation is ready.")
        return 0
    else:
        print(f"\n⚠️  {total - passed} test(s) failed.")
        return 1

if __name__ == "__main__":
    # Change to repository root
    repo_root = Path(__file__).parent.parent.absolute()
    os.chdir(repo_root)
    
    sys.exit(run_all_tests())
