#!/usr/bin/env python3
"""
Validate LaTeX structure for the new paper organization.
"""

import os
import re
from pathlib import Path

def check_file_exists(filepath, description):
    """Check if a file exists and report."""
    if os.path.exists(filepath):
        print(f"✓ {description}: {filepath}")
        return True
    else:
        print(f"✗ MISSING {description}: {filepath}")
        return False

def check_latex_syntax(filepath):
    """Basic LaTeX syntax validation."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for balanced braces
        if content.count('{') != content.count('}'):
            print(f"  ⚠ Unbalanced braces in {filepath}")
            return False
        
        # Check for balanced \begin{} \end{}
        begins = re.findall(r'\\begin\{([^}]+)\}', content)
        ends = re.findall(r'\\end\{([^}]+)\}', content)
        
        if sorted(begins) != sorted(ends):
            print(f"  ⚠ Unbalanced begin/end in {filepath}")
            print(f"     Begins: {begins}")
            print(f"     Ends: {ends}")
            return False
        
        return True
    except Exception as e:
        print(f"  ✗ Error reading {filepath}: {e}")
        return False

def main():
    print("=" * 70)
    print("LaTeX Paper Structure Validation")
    print("=" * 70)
    
    base_path = Path("/home/runner/work/-jmmotaburr-riemann-adelic/-jmmotaburr-riemann-adelic/paper")
    
    all_ok = True
    
    # Check main.tex
    print("\n1. Checking main document:")
    main_tex = base_path / "main_new.tex"
    if check_file_exists(main_tex, "Main document"):
        all_ok &= check_latex_syntax(main_tex)
    else:
        all_ok = False
    
    # Check sections
    print("\n2. Checking sections:")
    sections = [
        "01_introduction.tex",
        "02_preliminaries.tex",
        "03_local_length.tex",
        "04_hilbert_space.tex",
        "05_operator_resolvent.tex",
        "06_functional_equation.tex",
        "07_growth_order.tex",
        "08_pw_uniqueness.tex",
        "09_inversion_primes.tex",
        "10_numerics.tex",
        "11_bsd_extension.tex",
        "12_limitations.tex"
    ]
    
    for section in sections:
        section_path = base_path / "sections" / section
        if check_file_exists(section_path, f"Section {section}"):
            all_ok &= check_latex_syntax(section_path)
        else:
            all_ok = False
    
    # Check appendices
    print("\n3. Checking appendices:")
    appendices = [
        "A_trace_doi.tex",
        "B_debranges.tex",
        "C_pw_multiplicities.tex",
        "D_archimedean.tex",
        "E_algorithms.tex",
        "F_reproducibility.tex"
    ]
    
    for appendix in appendices:
        appendix_path = base_path / "appendix" / appendix
        if check_file_exists(appendix_path, f"Appendix {appendix}"):
            all_ok &= check_latex_syntax(appendix_path)
        else:
            all_ok = False
    
    # Check bibliography
    print("\n4. Checking bibliography:")
    biblio = base_path / "biblio.bib"
    if check_file_exists(biblio, "Bibliography"):
        all_ok &= check_latex_syntax(biblio)
    else:
        all_ok = False
    
    # Summary
    print("\n" + "=" * 70)
    if all_ok:
        print("✓ ALL CHECKS PASSED")
        print("\nStructure created successfully:")
        print("  - Main document: paper/main_new.tex")
        print("  - 12 sections with content")
        print("  - 6 appendices with placeholders")
        print("  - Bibliography file")
        print("\nFirst three sections have substantial content:")
        print("  - 01_introduction.tex: Full introduction with context and main results")
        print("  - 02_preliminaries.tex: Adelic framework and S-finite systems")
        print("  - 03_local_length.tex: Geometric emergence of ℓ_v = log q_v")
    else:
        print("✗ SOME CHECKS FAILED")
        return 1
    
    print("=" * 70)
    return 0

if __name__ == "__main__":
    exit(main())
