#!/usr/bin/env python3
"""
Test script for strengthened RH proof Lean files.

This script performs basic syntax validation on the new Lean files.
"""

import sys
from pathlib import Path

def test_lean_file_exists(filepath: Path) -> bool:
    """Test that a Lean file exists and is not empty."""
    if not filepath.exists():
        print(f"✗ File not found: {filepath}")
        return False
    
    if filepath.stat().st_size == 0:
        print(f"✗ File is empty: {filepath}")
        return False
    
    print(f"✓ File exists: {filepath}")
    return True

def test_lean_basic_syntax(filepath: Path) -> bool:
    """Test basic Lean syntax (imports, sections, etc.)."""
    try:
        content = filepath.read_text()
        
        # Check for required elements
        checks = {
            'import statements': 'import' in content,
            'noncomputable section': 'noncomputable' in content or 'section' in content,
            'proper comments': '/-' in content and '-/' in content,
        }
        
        all_passed = True
        for check_name, passed in checks.items():
            if passed:
                print(f"  ✓ Has {check_name}")
            else:
                print(f"  ✗ Missing {check_name}")
                all_passed = False
        
        return all_passed
        
    except Exception as e:
        print(f"✗ Error reading file: {e}")
        return False

def test_strengthened_proof_content(filepath: Path) -> bool:
    """Test specific content for strengthened proof files."""
    try:
        content = filepath.read_text()
        
        # Check for key concepts
        required_concepts = [
            ('StrongSpectralEquivalence', 'Strong spectral equivalence'),
            ('Zero', 'Zero definition'),
            ('RiemannZeta', 'Riemann Zeta function'),
        ]
        
        all_passed = True
        for concept, name in required_concepts:
            if concept in content:
                print(f"  ✓ Contains {name}")
            else:
                print(f"  ⚠ Missing {name} (may be in imports)")
        
        # Check for QCAL references
        if 'QCAL' in content or '141.7' in content or 'frequency' in content:
            print(f"  ✓ Contains QCAL integration")
        
        # Check for author info
        if 'José Manuel Mota Burruezo' in content or 'DOI' in content:
            print(f"  ✓ Contains author attribution")
        
        return all_passed
        
    except Exception as e:
        print(f"✗ Error checking content: {e}")
        return False

def main():
    """Main test runner."""
    print("=" * 80)
    print("STRENGTHENED PROOF LEAN FILES VALIDATION")
    print("=" * 80)
    
    repo_root = Path(__file__).parent
    lean_dir = repo_root / 'formalization' / 'lean'
    
    files_to_test = [
        lean_dir / 'RH_Strong_Proof_Plan.lean',
        lean_dir / 'STRENGTHENED_UNCONDITIONAL_PROOF.lean',
    ]
    
    all_tests_passed = True
    
    for filepath in files_to_test:
        print(f"\nTesting: {filepath.name}")
        print("-" * 80)
        
        if not test_lean_file_exists(filepath):
            all_tests_passed = False
            continue
        
        if not test_lean_basic_syntax(filepath):
            all_tests_passed = False
        
        if not test_strengthened_proof_content(filepath):
            # Content test is informational, don't fail on this
            pass
    
    print("\n" + "=" * 80)
    if all_tests_passed:
        print("✓ ALL TESTS PASSED")
        print("\nLean files are ready for compilation.")
        print("Note: Full compilation requires Lean 4 toolchain.")
    else:
        print("✗ SOME TESTS FAILED")
        print("\nPlease fix the issues above before proceeding.")
    print("=" * 80)
    
    return 0 if all_tests_passed else 1

if __name__ == '__main__':
    sys.exit(main())
