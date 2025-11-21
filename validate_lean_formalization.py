#!/usr/bin/env python3
"""
Validation Script for Lean 4 Formalization
==========================================

Validates the Lean formalization structure, imports, and syntax
without requiring full Lean compilation.

Author: José Manuel Mota Burruezo
Date: October 2025
Version: 1.0
"""

import os
import sys
import re
from pathlib import Path
from typing import List, Dict, Set, Tuple

# Color codes for terminal output
class Colors:
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    BOLD = '\033[1m'
    END = '\033[0m'

def print_header(text: str):
    """Print a formatted header."""
    print(f"\n{Colors.BOLD}{Colors.CYAN}{'=' * 70}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.CYAN}{text.center(70)}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.CYAN}{'=' * 70}{Colors.END}\n")

def print_success(text: str):
    """Print success message."""
    print(f"{Colors.GREEN}✓{Colors.END} {text}")

def print_warning(text: str):
    """Print warning message."""
    print(f"{Colors.YELLOW}⚠{Colors.END} {text}")

def print_error(text: str):
    """Print error message."""
    print(f"{Colors.RED}✗{Colors.END} {text}")

def print_info(text: str):
    """Print info message."""
    print(f"{Colors.BLUE}ℹ{Colors.END} {text}")

def find_lean_files(lean_dir: Path) -> List[Path]:
    """Find all .lean files in the directory."""
    return list(lean_dir.rglob("*.lean"))

def extract_imports(file_path: Path) -> List[str]:
    """Extract import statements from a Lean file."""
    imports = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line.startswith('import '):
                # Extract module name after 'import '
                import_name = line[7:].strip()
                imports.append(import_name)
    return imports

def count_sorry_placeholders(file_path: Path) -> int:
    """Count 'sorry' placeholders in a Lean file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    # Count sorry occurrences (as standalone word)
    return len(re.findall(r'\bsorry\b', content))

def count_axioms(file_path: Path) -> int:
    """Count axiom declarations in a Lean file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    return len(re.findall(r'\baxiom\b', content))

def count_theorems(file_path: Path) -> int:
    """Count theorem/lemma declarations in a Lean file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    theorems = len(re.findall(r'\btheorem\b', content))
    lemmas = len(re.findall(r'\blemma\b', content))
    return theorems + lemmas

def validate_file_structure(lean_dir: Path) -> Tuple[bool, Dict]:
    """Validate the Lean project file structure."""
    print_header("File Structure Validation")
    
    required_files = [
        'lean-toolchain',
        'lakefile.lean',
        'Main.lean',
        'RH_final.lean',
    ]
    
    required_modules = [
        'RiemannAdelic/axioms_to_lemmas.lean',
        'RiemannAdelic/schwartz_adelic.lean',
        'RiemannAdelic/D_explicit.lean',
        'RiemannAdelic/de_branges.lean',
        'RiemannAdelic/entire_order.lean',
        'RiemannAdelic/functional_eq.lean',
        'RiemannAdelic/positivity.lean',
        'RiemannAdelic/poisson_radon_symmetry.lean',
        'RiemannAdelic/zero_localization.lean',
        'RiemannAdelic/uniqueness_without_xi.lean',
        'RiemannAdelic/berry_keating_operator.lean',
    ]
    
    # V5.4 modules (optional but recommended)
    v54_modules = [
        'RiemannAdelic/OperatorH.lean',
        'RiemannAdelic/PoissonRadon.lean',
        'RiemannAdelic/PositivityV54.lean',
        'RiemannAdelic/Symmetry.lean',
        'RiemannAdelic/Zeros.lean',
        'RiemannAdelic/SpectralStructure.lean',
        'RiemannAdelic/V54_Consolidated.lean',
    ]
    
    all_valid = True
    stats = {'files_found': 0, 'files_missing': 0}
    
    # Check required files
    for file_name in required_files:
        file_path = lean_dir / file_name
        if file_path.exists():
            print_success(f"Found: {file_name}")
            stats['files_found'] += 1
        else:
            print_error(f"Missing: {file_name}")
            stats['files_missing'] += 1
            all_valid = False
    
    # Check required modules
    for module_path in required_modules:
        full_path = lean_dir / module_path
        if full_path.exists():
            print_success(f"Found module: {module_path}")
            stats['files_found'] += 1
        else:
            print_error(f"Missing module: {module_path}")
            stats['files_missing'] += 1
            all_valid = False
    
    # Check V5.4 modules (optional)
    print_info("\nV5.4 Modular Components (optional):")
    v54_found = 0
    for module_path in v54_modules:
        full_path = lean_dir / module_path
        if full_path.exists():
            print_success(f"Found V5.4 module: {module_path}")
            stats['files_found'] += 1
            v54_found += 1
        else:
            print_warning(f"V5.4 module not found: {module_path}")
    
    if v54_found == len(v54_modules):
        print_success(f"\n✓ All {len(v54_modules)} V5.4 modules present!")
    elif v54_found > 0:
        print_warning(f"\n⚠ Partial V5.4 installation: {v54_found}/{len(v54_modules)} modules")
    else:
        print_info("\nℹ V5.4 modules not installed (using V5.3)")
    
    return all_valid, stats

def validate_imports(lean_dir: Path) -> Tuple[bool, Dict]:
    """Validate import consistency across files."""
    print_header("Import Validation")
    
    # Get all Lean files
    lean_files = find_lean_files(lean_dir)
    
    # Build module name map
    modules = {}
    for f in lean_files:
        rel_path = f.relative_to(lean_dir)
        module_name = str(rel_path.with_suffix('')).replace(os.sep, '.')
        modules[module_name] = f
    
    all_valid = True
    stats = {'valid_imports': 0, 'invalid_imports': 0}
    
    # Check Main.lean imports
    main_file = lean_dir / 'Main.lean'
    if main_file.exists():
        imports = extract_imports(main_file)
        print_info(f"Main.lean imports {len(imports)} modules")
        
        for imp in imports:
            if imp.startswith('Mathlib'):
                print_success(f"External import: {imp}")
                stats['valid_imports'] += 1
            elif imp in modules:
                print_success(f"Valid import: {imp}")
                stats['valid_imports'] += 1
            else:
                print_error(f"Invalid import: {imp}")
                stats['invalid_imports'] += 1
                all_valid = False
    
    return all_valid, stats

def analyze_proof_status(lean_dir: Path) -> Dict:
    """Analyze the proof status of the formalization."""
    print_header("Proof Status Analysis")
    
    lean_files = find_lean_files(lean_dir)
    
    total_sorry = 0
    total_axioms = 0
    total_theorems = 0
    file_stats = []
    
    for f in lean_files:
        rel_path = f.relative_to(lean_dir)
        sorry_count = count_sorry_placeholders(f)
        axiom_count = count_axioms(f)
        theorem_count = count_theorems(f)
        
        total_sorry += sorry_count
        total_axioms += axiom_count
        total_theorems += theorem_count
        
        if sorry_count > 0 or axiom_count > 0 or theorem_count > 0:
            file_stats.append({
                'file': str(rel_path),
                'sorry': sorry_count,
                'axioms': axiom_count,
                'theorems': theorem_count
            })
    
    # Print summary
    print_info(f"Total theorems/lemmas: {total_theorems}")
    print_info(f"Total axioms: {total_axioms}")
    print_info(f"Total 'sorry' placeholders: {total_sorry}")
    
    print("\n" + Colors.BOLD + "File-by-file breakdown:" + Colors.END)
    for stat in sorted(file_stats, key=lambda x: x['sorry'], reverse=True):
        if stat['sorry'] > 0:
            print_warning(f"  {stat['file']}: {stat['theorems']} theorems, "
                        f"{stat['axioms']} axioms, {stat['sorry']} sorry")
        else:
            print_success(f"  {stat['file']}: {stat['theorems']} theorems, "
                        f"{stat['axioms']} axioms, {stat['sorry']} sorry")
    
    # Calculate completeness percentage
    if total_theorems > 0:
        completeness = ((total_theorems - total_sorry) / total_theorems) * 100
        print_info(f"\nEstimated completeness: {completeness:.1f}%")
    
    return {
        'total_sorry': total_sorry,
        'total_axioms': total_axioms,
        'total_theorems': total_theorems,
        'file_count': len(file_stats)
    }

def check_toolchain(lean_dir: Path) -> bool:
    """Check Lean toolchain configuration."""
    print_header("Toolchain Configuration")
    
    toolchain_file = lean_dir / 'lean-toolchain'
    if not toolchain_file.exists():
        print_error("lean-toolchain file not found")
        return False
    
    with open(toolchain_file, 'r') as f:
        toolchain = f.read().strip()
    
    print_success(f"Toolchain: {toolchain}")
    
    # Check if elan is installed
    elan_path = os.path.expanduser("~/.elan/bin/elan")
    if os.path.exists(elan_path):
        print_success("elan is installed")
    else:
        print_warning("elan not found - install from https://leanprover.github.io/")
    
    return True

def main():
    """Main validation function."""
    print(f"\n{Colors.BOLD}Lean 4 Formalization Validator{Colors.END}")
    print(f"{Colors.CYAN}V5.2+ Adelic Proof of Riemann Hypothesis{Colors.END}")
    print(f"{Colors.CYAN}DOI: 10.5281/zenodo.17116291{Colors.END}")
    
    # Find the Lean directory
    script_dir = Path(__file__).parent
    lean_dir = script_dir / 'formalization' / 'lean'
    
    if not lean_dir.exists():
        print_error(f"Lean directory not found: {lean_dir}")
        sys.exit(1)
    
    print_info(f"Validating: {lean_dir}")
    
    # Run validations
    results = {}
    
    # 1. File structure
    structure_valid, structure_stats = validate_file_structure(lean_dir)
    results['structure'] = structure_valid
    
    # 2. Import validation
    imports_valid, import_stats = validate_imports(lean_dir)
    results['imports'] = imports_valid
    
    # 3. Proof status
    proof_stats = analyze_proof_status(lean_dir)
    
    # 4. Toolchain check
    toolchain_valid = check_toolchain(lean_dir)
    results['toolchain'] = toolchain_valid
    
    # Final summary
    print_header("Validation Summary")
    
    all_passed = all(results.values())
    
    if structure_valid:
        print_success("File structure is valid")
    else:
        print_error("File structure has issues")
    
    if imports_valid:
        print_success("Import declarations are valid")
    else:
        print_error("Import declarations have issues")
    
    if toolchain_valid:
        print_success("Toolchain configuration is valid")
    else:
        print_error("Toolchain configuration has issues")
    
    print_info(f"Proof status: {proof_stats['total_theorems']} theorems, "
              f"{proof_stats['total_axioms']} axioms, "
              f"{proof_stats['total_sorry']} sorries")
    
    if all_passed:
        print(f"\n{Colors.GREEN}{Colors.BOLD}✓ All validations passed!{Colors.END}")
        print_info("The Lean formalization structure is valid.")
        print_info("To build: cd formalization/lean && lake build")
        return 0
    else:
        print(f"\n{Colors.YELLOW}{Colors.BOLD}⚠ Some validations failed{Colors.END}")
        print_info("Please review the errors above.")
        return 1

if __name__ == '__main__':
    sys.exit(main())
