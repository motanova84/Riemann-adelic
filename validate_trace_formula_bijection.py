#!/usr/bin/env python3
"""
Test/Validation Script for TraceFormulaBijection.lean

This script validates that the Lean file follows the expected structure
and contains the required theorems and definitions.
"""

import re
from pathlib import Path


def validate_trace_formula_bijection():
    """
    Validate the TraceFormulaBijection.lean file structure.
    """
    print("=" * 80)
    print("Validating TraceFormulaBijection.lean Structure")
    print("=" * 80)
    print()
    
    lean_file = Path("formalization/lean/spectral/TraceFormulaBijection.lean")
    
    if not lean_file.exists():
        print("❌ ERROR: TraceFormulaBijection.lean not found!")
        return False
    
    content = lean_file.read_text()
    
    # Check for key sections
    sections = {
        "TraceFormulaSetup": False,
        "BijectionEvidence": False,
        "ConstructiveTrace": False,
        "Consequences": False,
    }
    
    for section in sections:
        if f"namespace {section}" in content:
            sections[section] = True
            print(f"✓ Found namespace: {section}")
        else:
            print(f"✗ Missing namespace: {section}")
    
    print()
    
    # Check for key definitions
    definitions = [
        "heat_trace",
        "spectral_sum",
        "mellin_heat_trace",
        "H_psi_kernel",
        "is_zeta_zero_imaginary_part",
    ]
    
    print("Checking key definitions:")
    for defn in definitions:
        if f"def {defn}" in content:
            print(f"  ✓ {defn}")
        else:
            print(f"  ✗ {defn}")
    
    print()
    
    # Check for key theorems
    theorems = [
        "heat_trace_converges",
        "mellin_heat_trace_eq_spectral_sum",
        "weil_explicit_formula_analogy",
        "guinand_weil_formula",
        "montgomery_pair_correlation_agreement",
        "kernel_spectral_properties",
        "RH_iff_self_adjoint",
        "eigenvalue_moments_match",
    ]
    
    print("Checking key theorems:")
    found_count = 0
    for thm in theorems:
        if f"theorem {thm}" in content:
            print(f"  ✓ {thm}")
            found_count += 1
        else:
            print(f"  ✗ {thm}")
    
    print()
    
    # Check for axioms
    axioms = [
        "eigenvalue_sequence",
        "eigenvalue_sequence_pos",
        "eigenvalue_sequence_unbounded",
        "heat_trace_asymptotics",
        "spectrum_zeta_bijection_conjecture",
        "numerical_evidence",
    ]
    
    print("Checking axioms (conjectural statements):")
    for ax in axioms:
        if f"axiom {ax}" in content:
            print(f"  ✓ {ax}")
        else:
            print(f"  ✗ {ax}")
    
    print()
    
    # Check for proper imports
    required_imports = [
        "Mathlib.Analysis.SpecialFunctions.Zeta",
        "Mathlib.NumberTheory.ZetaFunction",
        "Mathlib.Analysis.Fourier.FourierTransform",
    ]
    
    print("Checking required imports:")
    for imp in required_imports:
        if f"import {imp}" in content:
            print(f"  ✓ {imp}")
        else:
            print(f"  ✗ {imp}")
    
    print()
    
    # Check for QCAL references
    qcal_markers = [
        "141.7001 Hz",
        "C = 244.36",
        "Ψ = I × A_eff² × C^∞",
        "DOI: 10.5281/zenodo.17379721",
        "ORCID: 0009-0002-1923-0773",
    ]
    
    print("Checking QCAL framework integration:")
    qcal_count = 0
    for marker in qcal_markers:
        if marker in content:
            print(f"  ✓ {marker}")
            qcal_count += 1
        else:
            print(f"  ✗ {marker}")
    
    print()
    
    # Count sorry statements
    sorry_count = content.count("sorry")
    print(f"Total 'sorry' statements: {sorry_count}")
    print("(These represent proof obligations to be completed)")
    
    print()
    
    # Define success threshold constant
    THEOREM_MATCH_THRESHOLD = 0.9  # 90% of theorems must be found
    
    # Summary
    print("=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    all_sections = all(sections.values())
    print(f"All sections present: {'✓' if all_sections else '✗'}")
    print(f"Theorems found: {found_count}/{len(theorems)}")
    print(f"QCAL integration: {qcal_count}/{len(qcal_markers)} markers")
    
    if all_sections and found_count >= len(theorems) * THEOREM_MATCH_THRESHOLD:
        print()
        print("✓ VALIDATION PASSED")
        print()
        print("The TraceFormulaBijection.lean file is properly structured and")
        print("contains the required mathematical content for the trace formula")
        print("approach to the Riemann Hypothesis via the Hilbert-Pólya conjecture.")
        return True
    else:
        print()
        print("⚠ VALIDATION INCOMPLETE")
        print("Some expected content is missing. Review the file structure.")
        return False


def print_file_statistics():
    """
    Print statistics about the Lean file.
    """
    lean_file = Path("formalization/lean/spectral/TraceFormulaBijection.lean")
    
    if not lean_file.exists():
        return
    
    content = lean_file.read_text()
    lines = content.split('\n')
    
    print()
    print("=" * 80)
    print("FILE STATISTICS")
    print("=" * 80)
    
    # Count different types of declarations
    theorem_count = content.count("theorem ")
    axiom_count = content.count("axiom ")
    def_count = content.count("def ")
    class_count = content.count("class ")
    
    # Count comment lines
    comment_lines = sum(1 for line in lines if line.strip().startswith("--") or 
                                                 line.strip().startswith("/-") or
                                                 line.strip().startswith("-/"))
    
    # Count documentation lines (in /-! ... -/ blocks)
    doc_blocks = re.findall(r'/-!.*?-/', content, re.DOTALL)
    doc_chars = sum(len(block) for block in doc_blocks)
    
    print(f"Total lines: {len(lines)}")
    print(f"Comment lines: {comment_lines}")
    print(f"Documentation characters: {doc_chars}")
    print()
    print(f"Theorems: {theorem_count}")
    print(f"Axioms: {axiom_count}")
    print(f"Definitions: {def_count}")
    print(f"Classes: {class_count}")
    print()
    
    # List all theorem names
    theorem_names = re.findall(r'theorem\s+(\w+)', content)
    print(f"Theorem names ({len(theorem_names)}):")
    for name in theorem_names:
        print(f"  - {name}")


def main():
    """Main validation function."""
    success = validate_trace_formula_bijection()
    print_file_statistics()
    
    print()
    print("=" * 80)
    print("NEXT STEPS")
    print("=" * 80)
    print()
    print("1. Review the README: formalization/lean/spectral/TRACE_FORMULA_BIJECTION_README.md")
    print("2. Check the file: formalization/lean/spectral/TraceFormulaBijection.lean")
    print("3. Fill in 'sorry' proofs using Mathlib4 theorems")
    print("4. Add numerical verification code if desired")
    print("5. Integrate with existing spectral formalization files")
    print()
    
    return 0 if success else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
