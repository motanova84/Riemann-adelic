#!/usr/bin/env python3
"""
Validation script for H_psi spectrum and spectral trace Lean files.

This script performs basic syntax validation and structure checks
for the newly created Lean formalization files.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-10
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple

def check_file_exists(filepath: Path) -> bool:
    """Check if file exists."""
    return filepath.exists()

def check_imports(content: str) -> Tuple[bool, List[str]]:
    """Check for required Mathlib imports."""
    required_imports = [
        'Mathlib.Analysis.SchwartzSpace',
        'Mathlib.Analysis.Complex.Basic',
        'Mathlib.Topology.Algebra.InfiniteSum.Basic'
    ]
    
    found_imports = []
    missing_imports = []
    
    for imp in required_imports:
        if imp in content:
            found_imports.append(imp)
        else:
            missing_imports.append(imp)
    
    return len(missing_imports) == 0, missing_imports

def check_definitions(content: str, expected_defs: List[str]) -> Tuple[bool, List[str]]:
    """Check for expected definitions."""
    missing_defs = []
    
    for def_name in expected_defs:
        # Match def, axiom, or theorem
        pattern = rf'\b(def|axiom|theorem)\s+{re.escape(def_name)}\b'
        if not re.search(pattern, content):
            missing_defs.append(def_name)
    
    return len(missing_defs) == 0, missing_defs

def check_qcal_constants(content: str) -> Tuple[bool, str]:
    """Check for QCAL constants."""
    freq_pattern = r'141\.7001'
    coherence_pattern = r'244\.36'
    
    has_freq = bool(re.search(freq_pattern, content))
    has_coherence = bool(re.search(coherence_pattern, content))
    
    if has_freq and has_coherence:
        return True, "✓ Both QCAL constants found"
    elif has_freq:
        return False, "✗ Missing coherence constant (244.36)"
    elif has_coherence:
        return False, "✗ Missing frequency constant (141.7001)"
    else:
        return False, "✗ Missing both QCAL constants"

def check_namespace(content: str, expected_namespace: str) -> bool:
    """Check for proper namespace."""
    pattern = rf'namespace\s+{re.escape(expected_namespace)}'
    return bool(re.search(pattern, content))

def validate_lean_file(filepath: Path, checks: dict) -> dict:
    """Validate a single Lean file."""
    results = {
        'file': filepath.name,
        'exists': False,
        'imports': {'status': False, 'missing': []},
        'definitions': {'status': False, 'missing': []},
        'qcal': {'status': False, 'message': ''},
        'namespace': False,
        'overall': False
    }
    
    if not check_file_exists(filepath):
        return results
    
    results['exists'] = True
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check imports
    has_imports, missing = check_imports(content)
    results['imports'] = {'status': has_imports, 'missing': missing}
    
    # Check definitions
    has_defs, missing_defs = check_definitions(content, checks['definitions'])
    results['definitions'] = {'status': has_defs, 'missing': missing_defs}
    
    # Check QCAL constants
    has_qcal, msg = check_qcal_constants(content)
    results['qcal'] = {'status': has_qcal, 'message': msg}
    
    # Check namespace
    results['namespace'] = check_namespace(content, checks['namespace'])
    
    # Overall status
    results['overall'] = all([
        results['exists'],
        results['imports']['status'],
        results['definitions']['status'],
        results['qcal']['status'],
        results['namespace']
    ])
    
    return results

def print_results(results: dict) -> None:
    """Print validation results."""
    print(f"\n{'='*70}")
    print(f"Validation Results for: {results['file']}")
    print(f"{'='*70}")
    
    # File exists
    status = "✓" if results['exists'] else "✗"
    print(f"{status} File exists: {results['exists']}")
    
    if not results['exists']:
        return
    
    # Imports
    status = "✓" if results['imports']['status'] else "✗"
    print(f"{status} Required imports: {results['imports']['status']}")
    if results['imports']['missing']:
        print(f"   Missing: {', '.join(results['imports']['missing'])}")
    
    # Definitions
    status = "✓" if results['definitions']['status'] else "✗"
    print(f"{status} Expected definitions: {results['definitions']['status']}")
    if results['definitions']['missing']:
        print(f"   Missing: {', '.join(results['definitions']['missing'])}")
    
    # QCAL constants
    status = "✓" if results['qcal']['status'] else "✗"
    print(f"{status} QCAL constants: {results['qcal']['message']}")
    
    # Namespace
    status = "✓" if results['namespace'] else "✗"
    print(f"{status} Proper namespace: {results['namespace']}")
    
    # Overall
    print(f"\n{'='*70}")
    if results['overall']:
        print("✓ OVERALL: PASSED")
    else:
        print("✗ OVERALL: FAILED")
    print(f"{'='*70}\n")

def main():
    """Main validation routine."""
    base_path = Path('/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/spectral')
    
    # Files to validate
    files_to_check = {
        'H_psi_spectral_trace.lean': {
            'namespace': 'HΨSpectralTrace',
            'definitions': [
                'H_psi',
                'spectrum_H_psi',
                'spectral_trace',
                'spectral_determinant',
                'RiemannHypothesis_spectral',
                'qcal_frequency',
                'qcal_coherence'
            ]
        },
        'H_psi_spectrum_properties.lean': {
            'namespace': 'HΨSpectrumProperties',
            'definitions': [
                'λₙ',
                'eigenvalue_count',
                'spectral_gap',
                'RiemannHypothesis',
                'spectrum_critical_line_iff_RH',
                'qcal_base_freq',
                'qcal_coherence'
            ]
        }
    }
    
    all_passed = True
    
    for filename, checks in files_to_check.items():
        filepath = base_path / filename
        results = validate_lean_file(filepath, checks)
        print_results(results)
        
        if not results['overall']:
            all_passed = False
    
    # Summary
    print(f"\n{'='*70}")
    print("VALIDATION SUMMARY")
    print(f"{'='*70}")
    
    if all_passed:
        print("✓ All files passed validation!")
        print("\nNext steps:")
        print("  1. Compile with: lake build")
        print("  2. Run Lean on individual files to check for errors")
        print("  3. Integrate with existing spectral modules")
        return 0
    else:
        print("✗ Some files failed validation")
        print("\nPlease review the errors above and fix them.")
        return 1

if __name__ == '__main__':
    sys.exit(main())
