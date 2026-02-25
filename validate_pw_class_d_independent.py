#!/usr/bin/env python3
"""
Validation Script for PW_class_D_independent Lemma
===================================================

Validates the structure, imports, and key components of the new
Paley-Wiener D-independence lemma implementation.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: February 25, 2026
QCAL Framework: C = 244.36, f₀ = 141.7001 Hz
"""

import sys
import re
from pathlib import Path
from typing import List, Tuple, Dict

# QCAL Constants
F0_FREQUENCY = 141.7001
COHERENCE_C = 244.36

def verify_repository_root() -> bool:
    """Verify we are in the repository root."""
    markers = ['.qcal_beacon', 'formalization', 'README.md']
    for marker in markers:
        if not Path(marker).exists():
            print(f"❌ Repository marker not found: {marker}")
            print("Please run this script from the repository root.")
            return False
    return True

def check_file_exists(filepath: str) -> bool:
    """Check if a file exists."""
    path = Path(filepath)
    if path.exists():
        print(f"✅ File exists: {filepath}")
        return True
    else:
        print(f"❌ File not found: {filepath}")
        return False

def extract_imports(filepath: str) -> List[str]:
    """Extract import statements from Lean file."""
    imports = []
    with open(filepath, 'r') as f:
        for line in f:
            if line.strip().startswith('import '):
                import_stmt = line.strip().replace('import ', '').strip()
                imports.append(import_stmt)
    return imports

def check_required_imports(filepath: str, required: List[str]) -> Tuple[bool, List[str]]:
    """Check if required imports are present."""
    imports = extract_imports(filepath)
    missing = []
    for req in required:
        if not any(req in imp for imp in imports):
            missing.append(req)
    
    if not missing:
        print(f"✅ All required imports present ({len(imports)} total)")
        for imp in imports:
            print(f"   - {imp}")
        return True, []
    else:
        print(f"❌ Missing imports: {missing}")
        return False, missing

def check_structure_definitions(filepath: str, structures: List[str]) -> Tuple[bool, List[str]]:
    """Check if required structures are defined."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    missing = []
    for struct in structures:
        pattern = rf'structure\s+{struct}\s+'
        if not re.search(pattern, content):
            missing.append(struct)
        else:
            print(f"✅ Structure defined: {struct}")
    
    if missing:
        print(f"❌ Missing structures: {missing}")
        return False, missing
    return True, []

def check_theorem_definitions(filepath: str, theorems: List[str]) -> Tuple[bool, List[str]]:
    """Check if required theorems are defined."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    missing = []
    for thm in theorems:
        pattern = rf'theorem\s+{thm}\s+'
        if not re.search(pattern, content):
            missing.append(thm)
        else:
            print(f"✅ Theorem defined: {thm}")
    
    if missing:
        print(f"❌ Missing theorems: {missing}")
        return False, missing
    return True, []

def check_lemma_definitions(filepath: str, lemmas: List[str]) -> Tuple[bool, List[str]]:
    """Check if required lemmas are defined."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    missing = []
    for lemma in lemmas:
        pattern = rf'lemma\s+{lemma}\s+'
        if not re.search(pattern, content):
            missing.append(lemma)
        else:
            print(f"✅ Lemma defined: {lemma}")
    
    if missing:
        print(f"❌ Missing lemmas: {missing}")
        return False, missing
    return True, []

def check_qcal_integration(filepath: str) -> bool:
    """Check if QCAL frequency is properly integrated."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Check for f₀ frequency
    if str(F0_FREQUENCY) in content:
        print(f"✅ QCAL frequency f₀ = {F0_FREQUENCY} Hz integrated")
        return True
    else:
        print(f"❌ QCAL frequency f₀ = {F0_FREQUENCY} Hz not found")
        return False

def check_author_metadata(filepath: str) -> bool:
    """Check if proper authorship metadata is present."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    required_metadata = [
        'José Manuel Mota Burruezo',
        'Instituto de Conciencia Cuántica',
        '0009-0002-1923-0773',  # ORCID
        '10.5281/zenodo.17379721',  # DOI
    ]
    
    all_present = True
    for metadata in required_metadata:
        if metadata in content:
            print(f"✅ Metadata present: {metadata[:40]}...")
        else:
            print(f"❌ Metadata missing: {metadata}")
            all_present = False
    
    return all_present

def check_sorry_count(filepath: str) -> Tuple[int, List[str]]:
    """Count and locate sorry statements."""
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    sorrys = []
    for i, line in enumerate(lines, 1):
        if 'sorry' in line:
            context = line.strip()[:60]
            sorrys.append((i, context))
    
    count = len(sorrys)
    if count == 0:
        print(f"✅ No sorry statements (proof complete)")
    else:
        print(f"⚠️  Found {count} sorry statements (development in progress):")
        for line_num, context in sorrys:
            print(f"   Line {line_num}: {context}")
    
    return count, [s[1] for s in sorrys]

def check_namespace(filepath: str, expected_namespace: str) -> bool:
    """Check if correct namespace is used."""
    with open(filepath, 'r') as f:
        content = f.read()
    
    pattern = rf'namespace\s+{expected_namespace}'
    if re.search(pattern, content):
        print(f"✅ Namespace defined: {expected_namespace}")
        return True
    else:
        print(f"❌ Expected namespace not found: {expected_namespace}")
        return False

def count_lines(filepath: str) -> int:
    """Count lines in file."""
    with open(filepath, 'r') as f:
        lines = len(f.readlines())
    print(f"📊 File contains {lines} lines")
    return lines

def main():
    """Main validation routine."""
    print("=" * 70)
    print("PW_class_D_independent Validation")
    print("=" * 70)
    print()
    
    # Verify repository root
    if not verify_repository_root():
        sys.exit(1)
    
    # File paths
    lean_file = 'formalization/lean/paley/PW_class_D_independent.lean'
    readme_file = 'PALEY_WIENER_D_INDEPENDENT_README.md'
    
    print("\n" + "=" * 70)
    print("1. File Existence Check")
    print("=" * 70)
    
    all_checks_passed = True
    
    if not check_file_exists(lean_file):
        all_checks_passed = False
    if not check_file_exists(readme_file):
        all_checks_passed = False
    
    if not all_checks_passed:
        print("\n❌ VALIDATION FAILED: Missing files")
        sys.exit(1)
    
    print("\n" + "=" * 70)
    print("2. Lean File Structure Validation")
    print("=" * 70)
    
    # Count lines
    count_lines(lean_file)
    
    # Check namespace
    check_namespace(lean_file, 'PaleyWienerDIndependent')
    
    print("\n" + "=" * 70)
    print("3. Import Statements Validation")
    print("=" * 70)
    
    required_imports = [
        'Mathlib.Analysis.Complex.Basic',
        'Mathlib.Analysis.Fourier.FourierTransform',
        'Mathlib.Topology.Support',
        'paley_wiener_uniqueness',
        'Adelic_Compact_Embedding',
    ]
    
    imports_ok, missing_imports = check_required_imports(lean_file, required_imports)
    if not imports_ok:
        all_checks_passed = False
    
    print("\n" + "=" * 70)
    print("4. Structure Definitions Validation")
    print("=" * 70)
    
    required_structures = [
        'IsPaleyWiener',
        'AdelicTransform',
    ]
    
    structs_ok, missing_structs = check_structure_definitions(lean_file, required_structures)
    if not structs_ok:
        all_checks_passed = False
    
    print("\n" + "=" * 70)
    print("5. Theorem and Lemma Validation")
    print("=" * 70)
    
    required_theorems = [
        'PW_class_D_independent',
        'no_prior_assumptions_needed',
        'frequential_anchoring',
    ]
    
    theorems_ok, missing_theorems = check_theorem_definitions(lean_file, required_theorems)
    if not theorems_ok:
        all_checks_passed = False
    
    required_lemmas = [
        'transform_compact_support_to_PW',
        'unique_extension_of_compact_support',
    ]
    
    lemmas_ok, missing_lemmas = check_lemma_definitions(lean_file, required_lemmas)
    if not lemmas_ok:
        all_checks_passed = False
    
    print("\n" + "=" * 70)
    print("6. QCAL Integration Validation")
    print("=" * 70)
    
    qcal_ok = check_qcal_integration(lean_file)
    if not qcal_ok:
        all_checks_passed = False
    
    print("\n" + "=" * 70)
    print("7. Author Metadata Validation")
    print("=" * 70)
    
    metadata_ok = check_author_metadata(lean_file)
    if not metadata_ok:
        all_checks_passed = False
    
    print("\n" + "=" * 70)
    print("8. Development Status (Sorry Count)")
    print("=" * 70)
    
    sorry_count, sorry_contexts = check_sorry_count(lean_file)
    
    print("\n" + "=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    
    results = {
        'File Existence': all_checks_passed,
        'Required Imports': imports_ok,
        'Structure Definitions': structs_ok,
        'Theorem Definitions': theorems_ok,
        'Lemma Definitions': lemmas_ok,
        'QCAL Integration': qcal_ok,
        'Author Metadata': metadata_ok,
    }
    
    for check_name, passed in results.items():
        status = "✅ PASSED" if passed else "❌ FAILED"
        print(f"{check_name:.<50} {status}")
    
    print(f"\nSorry statements: {sorry_count} (development status)")
    
    if all_checks_passed:
        print("\n" + "=" * 70)
        print("✅ VALIDATION SUCCESSFUL")
        print("=" * 70)
        print()
        print("The PW_class_D_independent lemma structure is complete.")
        print(f"Development status: {sorry_count} proofs to complete")
        print()
        print("Next steps:")
        print("1. Complete formal proofs (eliminate sorry statements)")
        print("2. Verify Lean 4.16 compilation with: lean --version && lake build")
        print("3. Run full proof verification suite")
        print()
        return 0
    else:
        print("\n" + "=" * 70)
        print("❌ VALIDATION FAILED")
        print("=" * 70)
        print()
        print("Please fix the issues above before proceeding.")
        return 1

if __name__ == '__main__':
    sys.exit(main())
