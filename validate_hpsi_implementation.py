#!/usr/bin/env python3
"""
Validation script for HPsi_selfadjoint.lean implementation
Verifies the structure and completeness of the RHOperator module
"""

import os
from pathlib import Path

def main():
    print("=" * 70)
    print("RHOperator Module Validation")
    print("=" * 70)
    print()
    
    rhoperator_dir = Path(__file__).parent / "formalization/lean/RHOperator"
    
    if not rhoperator_dir.exists():
        print("❌ RHOperator directory not found!")
        return 1
    
    # Expected files
    expected_files = {
        "K_determinant.lean": "K operator and eigenfunction definitions",
        "HPsi_selfadjoint.lean": "Main H_Ψ operator formalization",
        "README.md": "Module documentation"
    }
    
    print("Checking for required files:")
    all_present = True
    for filename, description in expected_files.items():
        filepath = rhoperator_dir / filename
        if filepath.exists():
            size = filepath.stat().st_size
            print(f"  ✅ {filename:30} ({size:5} bytes) - {description}")
        else:
            print(f"  ❌ {filename:30} MISSING - {description}")
            all_present = False
    
    print()
    
    if not all_present:
        print("❌ Some required files are missing!")
        return 1
    
    # Check HPsi_selfadjoint.lean content
    hpsi_file = rhoperator_dir / "HPsi_selfadjoint.lean"
    content = hpsi_file.read_text()
    
    print("Verifying HPsi_selfadjoint.lean content:")
    
    required_elements = {
        "namespace RHOperator": "Namespace declaration",
        "def H_dom": "Domain definition",
        "def HPsi": "Operator definition",
        "axiom HPsi_hermitian": "Hermitian symmetry axiom",
        "axiom HPsi_self_adjoint": "Self-adjoint axiom",
        "axiom HPsi_diagonalizes_K": "K diagonalization axiom",
        "theorem HPsi_symmetry_axis": "Symmetry theorem"
    }
    
    all_elements_present = True
    for element, description in required_elements.items():
        if element in content:
            print(f"  ✅ {description:40} - Found")
        else:
            print(f"  ❌ {description:40} - MISSING")
            all_elements_present = False
    
    print()
    
    # Check imports
    print("Verifying imports:")
    required_imports = [
        "Mathlib.Analysis.InnerProductSpace.Adjoint",
        "Mathlib.Analysis.NormedSpace.OperatorNorm",
        "Mathlib.Topology.Algebra.Module.Basic",
        "Mathlib.Analysis.SpecialFunctions.Zeta",
        "RHOperator.K_determinant"
    ]
    
    all_imports_present = True
    for imp in required_imports:
        if f"import {imp}" in content:
            print(f"  ✅ {imp}")
        else:
            print(f"  ❌ {imp} - MISSING")
            all_imports_present = False
    
    print()
    
    # Check K_determinant.lean
    k_file = rhoperator_dir / "K_determinant.lean"
    k_content = k_file.read_text()
    
    print("Verifying K_determinant.lean content:")
    k_required = {
        "def K_op": "K operator definition",
        "def Eigenfunction": "Eigenfunction property definition"
    }
    
    all_k_present = True
    for element, description in k_required.items():
        if element in k_content:
            print(f"  ✅ {description:40} - Found")
        else:
            print(f"  ❌ {description:40} - MISSING")
            all_k_present = False
    
    print()
    
    # Check lakefile.lean update
    lakefile = Path(__file__).parent / "formalization/lean/lakefile.lean"
    if lakefile.exists():
        lake_content = lakefile.read_text()
        if "lean_lib RHOperator" in lake_content:
            print("✅ lakefile.lean updated with RHOperator library")
        else:
            print("⚠️  lakefile.lean may need RHOperator library configuration")
    else:
        print("❌ lakefile.lean not found")
    
    print()
    print("=" * 70)
    
    if all_present and all_elements_present and all_imports_present and all_k_present:
        print("✅ All validations passed!")
        print()
        print("Module Structure:")
        print("  RHOperator/")
        print("    ├── K_determinant.lean       (Support definitions)")
        print("    ├── HPsi_selfadjoint.lean    (Main formalization)")
        print("    └── README.md                (Documentation)")
        print()
        print("Next steps:")
        print("  1. Install Lean 4 if not already installed")
        print("  2. Run 'lake build RHOperator' to compile")
        print("  3. Integrate with existing proof modules")
        return 0
    else:
        print("⚠️  Some validations failed - review output above")
        return 1

if __name__ == "__main__":
    exit(main())
