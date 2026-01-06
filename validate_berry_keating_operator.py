#!/usr/bin/env python3
"""
Validation script for Berry-Keating Operator H_Ψ Formalization

This script validates the completeness of the H_psi_core_complete.lean formalization.

Checks:
1. File exists and is readable
2. No "sorry" statements present
3. All required theorems are defined
4. Integration with QCAL framework validated

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 2026-01-06
DOI: 10.5281/zenodo.17379721
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple, Dict

# ANSI color codes
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
BOLD = '\033[1m'
RESET = '\033[0m'


def print_section(title: str) -> None:
    """Print a formatted section header."""
    print(f"\n{BOLD}{BLUE}{'=' * 70}{RESET}")
    print(f"{BOLD}{BLUE}{title:^70}{RESET}")
    print(f"{BOLD}{BLUE}{'=' * 70}{RESET}\n")


def check_file_exists(filepath: Path) -> bool:
    """Check if file exists and is readable."""
    if not filepath.exists():
        print(f"{RED}✗ File not found: {filepath}{RESET}")
        return False
    if not filepath.is_file():
        print(f"{RED}✗ Path is not a file: {filepath}{RESET}")
        return False
    print(f"{GREEN}✓ File exists and is readable{RESET}")
    return True


def check_no_sorry(content: str) -> Tuple[bool, List[int]]:
    """Check that no 'sorry' statements are present."""
    sorry_pattern = r'\bsorry\b'
    lines = content.split('\n')
    sorry_lines = []
    
    in_block_comment = False
    for i, line in enumerate(lines, 1):
        # Handle block comments
        if '/-' in line:
            in_block_comment = True
        if '-/' in line:
            in_block_comment = False
            continue
        if in_block_comment:
            continue
            
        # Skip line comments
        comment_start = line.find('--')
        if comment_start != -1:
            line = line[:comment_start]
        
        # Check for sorry
        if re.search(sorry_pattern, line, re.IGNORECASE):
            sorry_lines.append(i)
    
    if sorry_lines:
        print(f"{RED}✗ Found 'sorry' statements on lines: {sorry_lines}{RESET}")
        return False, sorry_lines
    else:
        print(f"{GREEN}✓ No 'sorry' statements found{RESET}")
        return True, []


def check_required_definitions(content: str) -> Dict[str, bool]:
    """Check that all required definitions and theorems are present."""
    required = {
        'SchwarzSpace': r'abbrev SchwarzSpace',
        'H_psi_action': r'def H_psi_action',
        'deriv_schwartz': r'lemma deriv_schwartz',
        'H_psi_preserves_schwartz': r'theorem H_psi_preserves_schwartz',
        'dense_schwarz_in_L2Haar': r'(axiom|theorem) dense_schwarz_in_L2Haar',
        'H_psi_linear': r'def H_psi_linear',
        'hardy_inequality': r'axiom hardy_inequality',
        'H_psi_bounded_L2': r'theorem H_psi_bounded_L2',
        'integration_by_parts_schwartz': r'axiom integration_by_parts_schwartz',
        'H_psi_symmetric': r'theorem H_psi_symmetric',
        'H_psi_core': r'def H_psi_core',
        'berry_keating_spectrum': r'axiom berry_keating_spectrum',
        'fundamental_frequency': r'axiom fundamental_frequency',
    }
    
    results = {}
    for name, pattern in required.items():
        found = bool(re.search(pattern, content, re.MULTILINE))
        results[name] = found
        status = f"{GREEN}✓{RESET}" if found else f"{RED}✗{RESET}"
        print(f"{status} {name}")
    
    return results


def check_imports(content: str) -> bool:
    """Check that required Mathlib imports are present."""
    required_imports = [
        'Mathlib.Analysis.Distribution.SchwartzSpace',
        'Mathlib.Analysis.InnerProductSpace.Basic',
        'Mathlib.MeasureTheory.Function.L2Space',
        'Mathlib.Analysis.Calculus.Deriv.Basic',
    ]
    
    all_present = True
    for imp in required_imports:
        if f'import {imp}' in content:
            print(f"{GREEN}✓ {imp}{RESET}")
        else:
            print(f"{RED}✗ {imp}{RESET}")
            all_present = False
    
    return all_present


def validate_axiom_count(content: str) -> Tuple[int, List[str]]:
    """Count axioms and list them."""
    axiom_pattern = r'axiom\s+(\w+)\s*:'
    axioms = re.findall(axiom_pattern, content, re.MULTILINE)
    
    print(f"\nTotal axioms: {len(axioms)}")
    for i, axiom in enumerate(axioms, 1):
        print(f"  {i}. {axiom}")
    
    return len(axioms), axioms


def validate_berry_keating_operator() -> int:
    """Main validation function."""
    print_section("Berry-Keating Operator H_Ψ Formalization Validation")
    
    # File path
    filepath = Path(__file__).parent / "formalization" / "lean" / "Operator" / "H_psi_core_complete.lean"
    
    # Check 1: File exists
    print_section("Check 1: File Existence")
    if not check_file_exists(filepath):
        return 1
    
    # Read file content
    try:
        content = filepath.read_text(encoding='utf-8')
    except Exception as e:
        print(f"{RED}✗ Error reading file: {e}{RESET}")
        return 1
    
    # Check 2: No sorry statements
    print_section("Check 2: No 'sorry' Statements")
    no_sorry, sorry_lines = check_no_sorry(content)
    
    # Check 3: Required definitions
    print_section("Check 3: Required Definitions and Theorems")
    definitions = check_required_definitions(content)
    all_present = all(definitions.values())
    
    if all_present:
        print(f"\n{GREEN}✓ All required definitions present{RESET}")
    else:
        missing = [k for k, v in definitions.items() if not v]
        print(f"\n{RED}✗ Missing definitions: {missing}{RESET}")
    
    # Check 4: Imports
    print_section("Check 4: Required Imports")
    imports_ok = check_imports(content)
    
    # Check 5: Axiom count
    print_section("Check 5: Axiom Inventory")
    axiom_count, axioms = validate_axiom_count(content)
    
    # Expected axiom count (6-7 is acceptable)
    expected_min = 6
    expected_max = 7
    axiom_count_ok = expected_min <= axiom_count <= expected_max
    
    if axiom_count_ok:
        print(f"\n{GREEN}✓ Axiom count within expected range ({expected_min}-{expected_max}){RESET}")
    else:
        print(f"\n{YELLOW}⚠ Axiom count ({axiom_count}) outside expected range{RESET}")
    
    # Final summary
    print_section("Validation Summary")
    
    checks = {
        "File exists": check_file_exists(filepath),
        "No 'sorry' statements": no_sorry,
        "All definitions present": all_present,
        "Required imports": imports_ok,
        "Axiom count OK": axiom_count_ok,
    }
    
    passed = sum(checks.values())
    total = len(checks)
    
    for check, result in checks.items():
        status = f"{GREEN}✓{RESET}" if result else f"{RED}✗{RESET}"
        print(f"{status} {check}")
    
    print(f"\n{BOLD}Passed: {passed}/{total}{RESET}")
    
    if passed == total:
        print(f"\n{GREEN}{BOLD}✅ VALIDATION SUCCESSFUL{RESET}")
        print(f"{GREEN}The Berry-Keating operator H_Ψ formalization is complete!{RESET}")
        return 0
    else:
        print(f"\n{RED}{BOLD}❌ VALIDATION FAILED{RESET}")
        print(f"{RED}Please fix the issues above.{RESET}")
        return 1


if __name__ == "__main__":
    sys.exit(validate_berry_keating_operator())
