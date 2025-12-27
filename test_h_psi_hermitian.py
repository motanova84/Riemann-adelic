#!/usr/bin/env python3
"""
Test script for HΨ Hermitian operator implementation

This script validates the structure and basic properties of the
HΨ operator implementation in Lean.

Author: José Manuel Mota Burruezo
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17116291
"""

import re
from pathlib import Path


def check_lean_file_structure(filepath: Path) -> dict:
    """Check the structure of a Lean file."""
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    results = {
        'file': filepath.name,
        'checks': {},
        'errors': [],
        'warnings': []
    }
    
    # Check 1: Namespace structure
    namespace_opens = re.findall(r'^namespace\s+([\w.]+)', content, re.MULTILINE)
    namespace_ends = re.findall(r'^end\s+([\w.]+)', content, re.MULTILINE)
    
    if len(namespace_opens) == len(namespace_ends):
        results['checks']['namespace_balanced'] = True
        if namespace_opens:
            results['namespace'] = namespace_opens[0]
    else:
        results['checks']['namespace_balanced'] = False
        results['errors'].append(
            f"Namespace mismatch: {len(namespace_opens)} opens vs {len(namespace_ends)} ends"
        )
    
    # Check 2: Key definitions present
    key_terms = [
        'V_resonant',
        'HΨ_operator',
        'HΨ',
        'HΨ_is_hermitian',
        'change_of_var',
        'integral_deriv_eq_sub'
    ]
    
    for term in key_terms:
        if term in content:
            results['checks'][f'has_{term}'] = True
        else:
            results['checks'][f'has_{term}'] = False
            results['warnings'].append(f"Missing key term: {term}")
    
    # Check 3: Theorem statement
    theorem_pattern = r'theorem\s+HΨ_is_hermitian.*?:.*?IsSymmetric'
    if re.search(theorem_pattern, content, re.DOTALL):
        results['checks']['main_theorem'] = True
    else:
        results['checks']['main_theorem'] = False
        results['errors'].append("Main theorem HΨ_is_hermitian not found or malformed")
    
    # Check 4: Documentation
    doc_markers = ['/-!', 'Author:', 'DOI:', 'References:']
    doc_count = sum(1 for marker in doc_markers if marker in content)
    results['checks']['documentation'] = doc_count >= 3
    results['doc_markers_found'] = doc_count
    
    # Check 5: Imports
    imports = re.findall(r'^import\s+([\w.]+)', content, re.MULTILINE)
    results['imports'] = imports
    results['checks']['has_imports'] = len(imports) > 0
    
    # Check 6: Sorry count (skeleton proofs)
    sorry_count = content.count('sorry')
    results['sorry_count'] = sorry_count
    results['checks']['skeleton_proof'] = sorry_count > 0
    
    # Check 7: Axioms
    axioms = re.findall(r'^axiom\s+([\w_]+)', content, re.MULTILINE)
    results['axioms'] = axioms
    
    # Check 8: Lemmas and theorems
    lemmas = re.findall(r'^lemma\s+([\w_]+)', content, re.MULTILINE)
    theorems = re.findall(r'^theorem\s+([\w_]+)', content, re.MULTILINE)
    results['lemmas'] = lemmas
    results['theorems'] = theorems
    
    return results


def print_results(results: dict):
    """Print validation results in a readable format."""
    
    print("=" * 70)
    print(f"HΨ Hermitian Operator - Validation Results")
    print("=" * 70)
    print()
    
    print(f"File: {results['file']}")
    if 'namespace' in results:
        print(f"Namespace: {results['namespace']}")
    print()
    
    # Print checks
    print("Structure Checks:")
    for check, passed in results['checks'].items():
        status = "✅" if passed else "❌"
        print(f"  {status} {check.replace('_', ' ').title()}")
    print()
    
    # Print statistics
    print("Statistics:")
    print(f"  • Imports: {len(results.get('imports', []))}")
    print(f"  • Axioms: {len(results.get('axioms', []))}")
    print(f"  • Lemmas: {len(results.get('lemmas', []))}")
    print(f"  • Theorems: {len(results.get('theorems', []))}")
    print(f"  • Sorry placeholders: {results.get('sorry_count', 0)}")
    print(f"  • Documentation markers: {results.get('doc_markers_found', 0)}/4")
    print()
    
    # Print key components
    if results.get('axioms'):
        print("Axioms defined:")
        for axiom in results['axioms']:
            print(f"  • {axiom}")
        print()
    
    if results.get('theorems'):
        print("Theorems:")
        for theorem in results['theorems']:
            print(f"  • {theorem}")
        print()
    
    if results.get('lemmas'):
        print("Lemmas:")
        for lemma in results['lemmas'][:10]:  # Show first 10
            print(f"  • {lemma}")
        if len(results['lemmas']) > 10:
            print(f"  ... and {len(results['lemmas']) - 10} more")
        print()
    
    # Print errors and warnings
    if results['errors']:
        print("❌ Errors:")
        for error in results['errors']:
            print(f"  • {error}")
        print()
    
    if results['warnings']:
        print("⚠️  Warnings:")
        for warning in results['warnings']:
            print(f"  • {warning}")
        print()
    
    # Overall assessment
    passed_checks = sum(1 for v in results['checks'].values() if v)
    total_checks = len(results['checks'])
    
    print("=" * 70)
    print(f"Overall: {passed_checks}/{total_checks} checks passed")
    
    if not results['errors']:
        print("✅ File structure is valid!")
    else:
        print("❌ File has structural issues that need attention")
    
    if results.get('sorry_count', 0) > 0:
        print(f"ℹ️  Note: {results['sorry_count']} 'sorry' placeholders found (expected for skeleton proofs)")
    
    print("=" * 70)


def main():
    """Main validation function."""
    
    # Path to the H_psi_hermitian.lean file
    lean_file = Path(__file__).parent / 'formalization/lean/RiemannAdelic/H_psi_hermitian.lean'
    
    if not lean_file.exists():
        print(f"❌ Error: File not found: {lean_file}")
        return 1
    
    # Validate the file
    results = check_lean_file_structure(lean_file)
    
    # Print results
    print_results(results)
    
    # Return exit code
    return 0 if not results['errors'] else 1


if __name__ == '__main__':
    exit(main())
