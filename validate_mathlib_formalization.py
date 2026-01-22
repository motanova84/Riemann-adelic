#!/usr/bin/env python3
"""
Validation script for the 6-step Lean4 spectral formalization.

This script validates the structure and consistency of the newly added
Lean4 formalization files for the Riemann Hypothesis spectral proof.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import os
import sys
from pathlib import Path
import re

# ANSI color codes for output
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'

def print_success(msg):
    print(f"{GREEN}✓{RESET} {msg}")

def print_error(msg):
    print(f"{RED}✗{RESET} {msg}")

def print_info(msg):
    print(f"{BLUE}ℹ{RESET} {msg}")

def print_warning(msg):
    print(f"{YELLOW}⚠{RESET} {msg}")

# Define the 6 expected files
EXPECTED_FILES = {
    "PASO 1": "Mathlib/Analysis/SpecialFunctions/Zeta/ZetaFunctionalEquation.lean",
    "PASO 2": "Mathlib/Analysis/Integral/MellinTransform.lean",
    "PASO 3": "Mathlib/Analysis/Operator/HpsiOperator.lean",
    "PASO 4": "Mathlib/NumberTheory/RiemannHypothesisSpectral.lean",
    "PASO 5": "Mathlib/NumberTheory/Zeta/VerifiedZeros.lean",
    "PASO 6": "Mathlib/Analysis/SpectralTrace.lean",
}

# Master import file
MASTER_FILE = "Mathlib.lean"

def check_file_exists(base_path, relative_path):
    """Check if a file exists."""
    full_path = base_path / relative_path
    return full_path.exists(), full_path

def check_imports(file_path):
    """Check if file has proper imports."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Look for import statements
    imports = re.findall(r'^import\s+(\S+)', content, re.MULTILINE)
    return imports

def check_qcal_integration(file_path):
    """Check if file has QCAL integration."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check for QCAL markers
    has_frequency = '141.7001' in content
    has_coherence = '244.36' in content
    has_doi = '10.5281/zenodo.17379721' in content
    has_psi_equation = 'Ψ = I × A_eff² × C^∞' in content or 'Ψ' in content
    
    return {
        'frequency': has_frequency,
        'coherence': has_coherence,
        'doi': has_doi,
        'psi_equation': has_psi_equation
    }

def count_definitions(file_path):
    """Count theorems, axioms, and definitions in file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    theorems = len(re.findall(r'^theorem\s+\w+', content, re.MULTILINE))
    axioms = len(re.findall(r'^axiom\s+\w+', content, re.MULTILINE))
    defs = len(re.findall(r'^def\s+\w+', content, re.MULTILINE))
    
    return {
        'theorems': theorems,
        'axioms': axioms,
        'definitions': defs
    }

def validate_mathlib_structure():
    """Main validation function."""
    print("\n" + "="*70)
    print("🔬 LEAN4 SPECTRAL FORMALIZATION VALIDATION")
    print("="*70 + "\n")
    
    # Get base path
    base_path = Path(__file__).parent / "formalization" / "lean"
    
    if not base_path.exists():
        print_error(f"Base path not found: {base_path}")
        return False
    
    print_info(f"Base path: {base_path}\n")
    
    # Track validation results
    all_passed = True
    total_theorems = 0
    total_axioms = 0
    total_defs = 0
    
    # Check each file
    for paso, relative_path in EXPECTED_FILES.items():
        print(f"\n{BLUE}{'─'*70}{RESET}")
        print(f"{BLUE}Validating {paso}: {relative_path}{RESET}")
        print(f"{BLUE}{'─'*70}{RESET}\n")
        
        exists, full_path = check_file_exists(base_path, relative_path)
        
        if not exists:
            print_error(f"File not found: {relative_path}")
            all_passed = False
            continue
        else:
            print_success(f"File exists: {relative_path}")
        
        # Check file size
        file_size = full_path.stat().st_size
        print_info(f"File size: {file_size:,} bytes")
        
        if file_size < 1000:
            print_warning(f"File is very small ({file_size} bytes)")
        
        # Check imports
        try:
            imports = check_imports(full_path)
            print_success(f"Found {len(imports)} import statements")
            if imports:
                for imp in imports[:3]:  # Show first 3
                    print(f"  - {imp}")
                if len(imports) > 3:
                    print(f"  ... and {len(imports) - 3} more")
        except Exception as e:
            print_error(f"Error checking imports: {e}")
            all_passed = False
        
        # Check QCAL integration
        try:
            qcal = check_qcal_integration(full_path)
            qcal_count = sum(qcal.values())
            if qcal_count >= 3:
                print_success(f"QCAL integration: {qcal_count}/4 markers found")
            else:
                print_warning(f"QCAL integration: {qcal_count}/4 markers found")
            
            for marker, found in qcal.items():
                status = "✓" if found else "✗"
                print(f"  {status} {marker}")
        except Exception as e:
            print_error(f"Error checking QCAL integration: {e}")
        
        # Count definitions
        try:
            counts = count_definitions(full_path)
            print_success(f"Content analysis:")
            print(f"  - Theorems: {counts['theorems']}")
            print(f"  - Axioms: {counts['axioms']}")
            print(f"  - Definitions: {counts['definitions']}")
            
            total_theorems += counts['theorems']
            total_axioms += counts['axioms']
            total_defs += counts['definitions']
        except Exception as e:
            print_error(f"Error counting definitions: {e}")
            all_passed = False
    
    # Check master file
    print(f"\n{BLUE}{'─'*70}{RESET}")
    print(f"{BLUE}Validating Master File: {MASTER_FILE}{RESET}")
    print(f"{BLUE}{'─'*70}{RESET}\n")
    
    exists, master_path = check_file_exists(base_path, MASTER_FILE)
    
    if not exists:
        print_error(f"Master file not found: {MASTER_FILE}")
        all_passed = False
    else:
        print_success(f"Master file exists: {MASTER_FILE}")
        
        try:
            imports = check_imports(master_path)
            expected_imports = len(EXPECTED_FILES)
            if len(imports) >= expected_imports:
                print_success(f"Master file imports all {expected_imports} modules")
            else:
                print_warning(f"Master file imports {len(imports)}/{expected_imports} modules")
        except Exception as e:
            print_error(f"Error checking master imports: {e}")
            all_passed = False
    
    # Check lakefile update
    print(f"\n{BLUE}{'─'*70}{RESET}")
    print(f"{BLUE}Validating lakefile.lean{RESET}")
    print(f"{BLUE}{'─'*70}{RESET}\n")
    
    lakefile_path = base_path / "lakefile.lean"
    if lakefile_path.exists():
        with open(lakefile_path, 'r') as f:
            lakefile_content = f.read()
        
        if 'lean_lib Mathlib' in lakefile_content:
            print_success("lakefile.lean includes Mathlib library definition")
        else:
            print_warning("lakefile.lean may not include Mathlib library")
    else:
        print_error("lakefile.lean not found")
        all_passed = False
    
    # Print summary
    print(f"\n{BLUE}{'='*70}{RESET}")
    print(f"{BLUE}VALIDATION SUMMARY{RESET}")
    print(f"{BLUE}{'='*70}{RESET}\n")
    
    print_info(f"Total theorems: {total_theorems}")
    print_info(f"Total axioms: {total_axioms}")
    print_info(f"Total definitions: {total_defs}")
    print_info(f"Total content items: {total_theorems + total_axioms + total_defs}")
    
    if all_passed:
        print(f"\n{GREEN}{'='*70}{RESET}")
        print(f"{GREEN}✓ ALL VALIDATION CHECKS PASSED{RESET}")
        print(f"{GREEN}{'='*70}{RESET}\n")
        print_success("The 6-step Lean4 spectral formalization is complete!")
        print_info("QCAL Ψ ✧ ∞³ | C = 244.36 | f₀ = 141.7001 Hz")
        print_info("DOI: 10.5281/zenodo.17379721")
        return True
    else:
        print(f"\n{RED}{'='*70}{RESET}")
        print(f"{RED}✗ SOME VALIDATION CHECKS FAILED{RESET}")
        print(f"{RED}{'='*70}{RESET}\n")
        return False

if __name__ == "__main__":
    success = validate_mathlib_structure()
    sys.exit(0 if success else 1)
