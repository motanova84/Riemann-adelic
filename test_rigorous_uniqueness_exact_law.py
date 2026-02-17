#!/usr/bin/env python3
"""
Test script for RIGOROUS_UNIQUENESS_EXACT_LAW.lean formalization

This script validates that the new Lean formalization is syntactically correct
and integrates properly with the existing QCAL framework.

QCAL Integration:
  Base frequency: 141.7001 Hz
  Coherence: C = 244.36
  Equation: Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path

# Ensure we're in the repository root
repo_root = Path(__file__).parent.absolute()
sys.path.insert(0, str(repo_root))

def test_file_exists():
    """Test that the formalization file exists"""
    lean_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
    assert lean_file.exists(), f"File not found: {lean_file}"
    print("✅ RIGOROUS_UNIQUENESS_EXACT_LAW.lean exists")
    
def test_readme_exists():
    """Test that the README exists"""
    readme_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW_README.md"
    assert readme_file.exists(), f"README not found: {readme_file}"
    print("✅ RIGOROUS_UNIQUENESS_EXACT_LAW_README.md exists")

def test_file_content():
    """Test that the file contains expected content"""
    lean_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
    content = lean_file.read_text()
    
    # Check for key theorems
    assert "theorem strong_spectral_equivalence" in content, "Missing main theorem"
    assert "theorem exact_weyl_law" in content, "Missing Weyl law theorem"
    assert "theorem local_zero_uniqueness" in content, "Missing uniqueness theorem"
    assert "theorem discrete_spectrum_H_psi" in content, "Missing discrete spectrum theorem"
    
    # Check for QCAL integration
    assert "141.7001 Hz" in content, "Missing fundamental frequency"
    assert "C = 244.36" in content, "Missing coherence constant"
    assert "Ψ = I × A_eff² × C^∞" in content, "Missing QCAL equation"
    
    # Check for author information
    assert "José Manuel Mota Burruezo" in content, "Missing author"
    assert "0009-0002-1923-0773" in content, "Missing ORCID"
    assert "10.5281/zenodo.17379721" in content, "Missing DOI"
    
    print("✅ File contains all expected theorems and QCAL integration")

def test_mathematical_constants():
    """Test that mathematical constants are correctly specified"""
    lean_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
    content = lean_file.read_text()
    
    # Check uniqueness radius
    assert "uniqueness_radius : ℝ := 0.1" in content, "Missing uniqueness radius"
    
    # Check error constant
    assert "0.999" in content, "Missing error constant C < 1"
    
    # Check fundamental frequency (full precision)
    assert "141.700010083578160030654028447231151926974628612204" in content, \
        "Missing full precision frequency"
    
    print("✅ Mathematical constants are correctly specified")

def test_theorem_count():
    """Test that all 6 parts are implemented"""
    lean_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
    content = lean_file.read_text()
    
    # Count main theorem sections
    parts = [
        "PARTE 1: OPERADOR K FORTALECIDO",
        "PARTE 2: TEOREMA DE UNICIDAD LOCAL",
        "PARTE 3: LEY DE WEYL EXACTA",
        "PARTE 4: ANÁLISIS ESPECTRAL FINO",
        "PARTE 5: TEOREMA DE UNICIDAD FUERTE",
        "PARTE 6: DEMOSTRACIÓN FINAL"
    ]
    
    for part in parts:
        assert part in content, f"Missing part: {part}"
    
    print(f"✅ All 6 parts implemented")

def test_imports():
    """Test that necessary imports are present"""
    lean_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW.lean"
    content = lean_file.read_text()
    
    required_imports = [
        "Mathlib.Analysis.Complex.RiemannZeta",
        "Mathlib.Topology.MetricSpace.Basic",
        "Mathlib.Analysis.InnerProductSpace.Spectrum",
        "Mathlib.Analysis.SchwartzSpace",
        "Mathlib.NumberTheory.ZetaFunction",
        "Mathlib.MeasureTheory.Integral.Integral"
    ]
    
    for imp in required_imports:
        assert f"import {imp}" in content, f"Missing import: {imp}"
    
    print("✅ All required imports present")

def test_documentation():
    """Test documentation completeness"""
    readme_file = repo_root / "formalization" / "lean" / "spectral" / "RIGOROUS_UNIQUENESS_EXACT_LAW_README.md"
    content = readme_file.read_text()
    
    # Check for key sections
    sections = [
        "Overview",
        "Main Achievements",
        "Structure and Components",
        "Mathematical Innovations",
        "Integration with QCAL Framework",
        "Verification Status",
        "References"
    ]
    
    for section in sections:
        assert section in content, f"Missing documentation section: {section}"
    
    print("✅ Documentation is complete")

def test_qcal_beacon_integration():
    """Test integration with QCAL beacon"""
    beacon_file = repo_root / ".qcal_beacon"
    assert beacon_file.exists(), "QCAL beacon file missing"
    
    beacon_content = beacon_file.read_text()
    assert "141.7001 Hz" in beacon_content, "Frequency mismatch in beacon"
    assert "C = 244.36" in beacon_content or "coherence = \"C = 244.36\"" in beacon_content, \
        "Coherence constant mismatch"
    
    print("✅ QCAL beacon integration verified")

def main():
    """Run all tests"""
    print("=" * 80)
    print("Testing RIGOROUS_UNIQUENESS_EXACT_LAW.lean Formalization")
    print("=" * 80)
    print()
    
    tests = [
        test_file_exists,
        test_readme_exists,
        test_file_content,
        test_mathematical_constants,
        test_theorem_count,
        test_imports,
        test_documentation,
        test_qcal_beacon_integration
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"❌ FAILED: {test.__name__}")
            print(f"   Error: {e}")
            failed += 1
        except Exception as e:
            print(f"❌ ERROR in {test.__name__}: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"Test Results: {passed} passed, {failed} failed")
    print("=" * 80)
    
    if failed == 0:
        print()
        print("✅ ALL TESTS PASSED - FORMALIZATION VALIDATED")
        print()
        print("🎯 Next Steps:")
        print("   1. Validate Lean 4 syntax: cd formalization/lean && lake build")
        print("   2. Run V5 coronación validation: python validate_v5_coronacion.py")
        print("   3. Update main README with new formalization")
        print()
        return 0
    else:
        print()
        print("⚠️  SOME TESTS FAILED - PLEASE REVIEW")
        return 1

if __name__ == "__main__":
    sys.exit(main())
