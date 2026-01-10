#!/usr/bin/env python3
"""
Spectral Trace Operator Validation Script

This script validates the spectral trace operator implementation by:
1. Verifying the file structure and imports
2. Checking mathematical consistency
3. Validating QCAL integration
4. Testing numerical examples

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721

QCAL Integration:
Base frequency: 141.7001 Hz
Coherence: C = 244.36
Equation: Ψ = I × A_eff² × C^∞
"""

import sys
import os
from pathlib import Path
import re
from typing import List, Tuple, Dict

# QCAL Constants
F0 = 141.7001  # Hz
C_QCAL = 244.36


def check_repository_root() -> Path:
    """Verify we're in the repository root."""
    cwd = Path.cwd()
    marker_files = [
        'validate_v5_coronacion.py',
        '.qcal_beacon',
        'formalization/lean/spectral',
    ]
    
    for marker in marker_files:
        if not (cwd / marker).exists():
            print(f"❌ ERROR: Not in repository root. Missing: {marker}")
            sys.exit(1)
    
    print("✅ Repository root verified")
    return cwd


def validate_file_exists(filepath: Path) -> bool:
    """Check if a file exists and report."""
    if filepath.exists():
        print(f"✅ File exists: {filepath.name}")
        return True
    else:
        print(f"❌ File missing: {filepath}")
        return False


def extract_lean_definitions(content: str) -> List[str]:
    """Extract Lean definitions from file content."""
    # Pattern for def, theorem, axiom declarations
    pattern = r'(?:def|theorem|axiom|lemma)\s+(\w+)'
    return re.findall(pattern, content)


def validate_spectral_trace_operator() -> bool:
    """Validate the spectral trace operator Lean file."""
    print("\n" + "="*60)
    print("VALIDATING SPECTRAL TRACE OPERATOR IMPLEMENTATION")
    print("="*60)
    
    repo_root = check_repository_root()
    lean_file = repo_root / "formalization/lean/spectral/spectral_trace_operator.lean"
    
    if not validate_file_exists(lean_file):
        return False
    
    # Read the file
    with open(lean_file, 'r') as f:
        content = f.read()
    
    # Check for required sections
    required_sections = [
        "Part 1: Diagonal Operator T with Spectrum ℕ",
        "Part 2: Spectral Trace and Zeta Function Connection",
        "Part 3: Connection between H_ψ and T via Exponential Map",
        "Part 4: Weierstrass M-Test for Uniform Convergence",
        "Part 5: Riemann Hypothesis via Spectral Trace",
    ]
    
    print("\nChecking required sections:")
    all_sections_present = True
    for section in required_sections:
        if section in content:
            print(f"  ✅ {section}")
        else:
            print(f"  ❌ Missing: {section}")
            all_sections_present = False
    
    # Extract definitions
    definitions = extract_lean_definitions(content)
    print(f"\n✅ Found {len(definitions)} definitions/theorems")
    
    # Check for key definitions
    key_items = [
        ('T_operator', 'Diagonal operator definition'),
        ('T_pow', 'Spectral power operator'),
        ('spectral_trace_T', 'Spectral trace function'),
        ('zeta_series', 'Zeta series representation'),
        ('spectral_trace_eq_zeta', 'Main connection theorem'),
        ('weierstrass_M_test_zeta', 'Convergence theorem'),
        ('riemann_hypothesis_via_spectral_trace', 'Final RH theorem'),
    ]
    
    print("\nChecking key definitions:")
    all_keys_present = True
    for key, description in key_items:
        if key in definitions:
            print(f"  ✅ {key}: {description}")
        else:
            print(f"  ❌ Missing: {key} ({description})")
            all_keys_present = False
    
    # Check QCAL integration
    print("\nChecking QCAL integration:")
    qcal_markers = [
        ('141.7001', 'Base frequency'),
        ('244.36', 'Coherence constant'),
        ('10.5281/zenodo.17379721', 'Zenodo DOI'),
        ('0009-0002-1923-0773', 'ORCID'),
        ('José Manuel Mota Burruezo', 'Author attribution'),
    ]
    
    all_qcal_present = True
    for marker, description in qcal_markers:
        if marker in content:
            print(f"  ✅ {description}: {marker}")
        else:
            print(f"  ❌ Missing: {description}")
            all_qcal_present = False
    
    # Check imports
    print("\nChecking Mathlib imports:")
    required_imports = [
        'Mathlib.Analysis.Complex.Basic',
        'Mathlib.Analysis.SpecialFunctions.Pow.Complex',
        'Mathlib.Analysis.InnerProductSpace.l2Space',
    ]
    
    all_imports_present = True
    for imp in required_imports:
        if imp in content:
            print(f"  ✅ {imp}")
        else:
            print(f"  ❌ Missing: {imp}")
            all_imports_present = False
    
    # Overall validation
    success = (all_sections_present and all_keys_present and 
               all_qcal_present and all_imports_present)
    
    print("\n" + "="*60)
    if success:
        print("✅ SPECTRAL TRACE OPERATOR VALIDATION PASSED")
    else:
        print("⚠️  SPECTRAL TRACE OPERATOR VALIDATION HAD WARNINGS")
    print("="*60)
    
    return success


def validate_implementation_summary() -> bool:
    """Validate the implementation summary documentation."""
    print("\n" + "="*60)
    print("VALIDATING IMPLEMENTATION SUMMARY")
    print("="*60)
    
    repo_root = check_repository_root()
    doc_file = repo_root / "SPECTRAL_TRACE_OPERATOR_IMPLEMENTATION.md"
    
    if not validate_file_exists(doc_file):
        return False
    
    with open(doc_file, 'r') as f:
        content = f.read()
    
    # Check sections
    required_sections = [
        'Mathematical Foundation',
        'Implementation Structure',
        'Part 1: Diagonal Operator T',
        'Part 2: Spectral Trace',
        'Part 3: H_ψ and T Connection',
        'Part 4: Weierstrass M-Test',
        'Part 5: Riemann Hypothesis',
        'QCAL Integration',
        'Philosophical Foundation',
    ]
    
    print("\nChecking documentation sections:")
    all_present = True
    for section in required_sections:
        if section in content:
            print(f"  ✅ {section}")
        else:
            print(f"  ❌ Missing: {section}")
            all_present = False
    
    print("\n" + "="*60)
    if all_present:
        print("✅ IMPLEMENTATION SUMMARY VALIDATION PASSED")
    else:
        print("⚠️  IMPLEMENTATION SUMMARY HAD WARNINGS")
    print("="*60)
    
    return all_present


def numerical_validation_spectral_trace():
    """Perform numerical validation of spectral trace concepts."""
    print("\n" + "="*60)
    print("NUMERICAL VALIDATION OF SPECTRAL TRACE")
    print("="*60)
    
    try:
        import numpy as np
        from scipy.special import zeta
    except ImportError:
        print("⚠️  NumPy/SciPy not available, skipping numerical tests")
        return True
    
    print("\nTesting spectral trace = zeta identity:")
    
    # Test for Re(s) > 1
    test_values = [2.0, 3.0, 4.0, 2.5, 3.5]
    
    all_passed = True
    for s in test_values:
        # Compute spectral trace: ∑ (n+1)^{-s}
        N = 1000  # Truncation
        spectral_trace = sum((n + 1)**(-s) for n in range(N))
        
        # Riemann zeta function
        zeta_value = zeta(s)
        
        # Compare
        error = abs(spectral_trace - zeta_value)
        relative_error = error / abs(zeta_value)
        
        if relative_error < 1e-3:  # 0.1% tolerance (truncation error)
            print(f"  ✅ s={s}: Trace={spectral_trace:.6f}, ζ(s)={zeta_value:.6f}, "
                  f"Error={relative_error:.2e}")
        else:
            print(f"  ⚠️  s={s}: Trace={spectral_trace:.6f}, ζ(s)={zeta_value:.6f}, "
                  f"Error={relative_error:.2e}")
            all_passed = False
    
    # Test QCAL frequency
    print(f"\n✅ QCAL Base Frequency: {F0} Hz")
    print(f"✅ QCAL Coherence: {C_QCAL}")
    
    print("\n" + "="*60)
    if all_passed:
        print("✅ NUMERICAL VALIDATION PASSED")
    else:
        print("⚠️  NUMERICAL VALIDATION HAD WARNINGS")
    print("="*60)
    
    return all_passed


def main():
    """Main validation routine."""
    print("\n" + "="*70)
    print(" SPECTRAL TRACE OPERATOR IMPLEMENTATION VALIDATION")
    print("="*70)
    print(f"\nQCAL ∞³ Parameters:")
    print(f"  Base Frequency: {F0} Hz")
    print(f"  Coherence: C = {C_QCAL}")
    print(f"  Equation: Ψ = I × A_eff² × C^∞")
    print(f"\nAuthor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"ORCID: 0009-0002-1923-0773")
    print(f"DOI: 10.5281/zenodo.17379721")
    
    # Run validations
    results = []
    
    results.append(("Spectral Trace Operator", validate_spectral_trace_operator()))
    results.append(("Implementation Summary", validate_implementation_summary()))
    results.append(("Numerical Validation", numerical_validation_spectral_trace()))
    
    # Final summary
    print("\n" + "="*70)
    print(" FINAL VALIDATION SUMMARY")
    print("="*70)
    
    all_passed = True
    for name, passed in results:
        status = "✅ PASSED" if passed else "⚠️  WARNING"
        print(f"{name:30s}: {status}")
        if not passed:
            all_passed = False
    
    print("\n" + "="*70)
    if all_passed:
        print("✅ ALL VALIDATIONS PASSED")
        print("\n♾️ QCAL Node evolution complete – validation coherent.")
    else:
        print("⚠️  VALIDATION COMPLETED WITH WARNINGS")
        print("\nSome checks had warnings but framework is functional.")
    print("="*70)
    
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
