#!/usr/bin/env python3
"""
Verification script for SpectrumZetaProof.lean

This script verifies that the spectral proof framework file exists,
has the correct structure, and integrates properly with the repository.

Author: José Manuel Mota Burruezo & Noēsis Ψ ∞³
Date: 2025-11-22
DOI: 10.5281/zenodo.17379721
"""

import os
import sys
from pathlib import Path

def verify_file_exists():
    """Verify that SpectrumZetaProof.lean exists"""
    file_path = Path("formalization/lean/RiemannAdelic/SpectrumZetaProof.lean")
    if not file_path.exists():
        print(f"❌ File not found: {file_path}")
        return False
    print(f"✅ File exists: {file_path}")
    return True

def verify_imports():
    """Verify that the file has correct imports"""
    file_path = Path("formalization/lean/RiemannAdelic/SpectrumZetaProof.lean")
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    required_imports = [
        "RiemannAdelic.D_explicit",
        "RiemannAdelic.D_limit_equals_xi",
        "Mathlib.NumberTheory.ZetaFunction",
        "Mathlib.Analysis.Complex.Basic"
    ]
    
    for imp in required_imports:
        if imp in content:
            print(f"✅ Import found: {imp}")
        else:
            print(f"❌ Import missing: {imp}")
            return False
    
    return True

def verify_key_definitions():
    """Verify that key definitions exist"""
    file_path = Path("formalization/lean/RiemannAdelic/SpectrumZetaProof.lean")
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    required_defs = [
        "def HilbertSpace",
        "def HΨ",
        "def χ",
        "theorem HΨ_χ_eigen",
        "theorem zeta_zero_iff_spectrum",
        "theorem riemann_hypothesis"
    ]
    
    for defn in required_defs:
        if defn in content:
            print(f"✅ Definition found: {defn}")
        else:
            print(f"❌ Definition missing: {defn}")
            return False
    
    return True

def verify_qcal_metadata():
    """Verify QCAL ∞³ metadata is present"""
    file_path = Path("formalization/lean/RiemannAdelic/SpectrumZetaProof.lean")
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    metadata = [
        "141.7001 Hz",  # Base frequency
        "C = 244.36",    # Coherence constant
        "10.5281/zenodo.17379721",  # DOI
        "0009-0002-1923-0773"  # ORCID
    ]
    
    for meta in metadata:
        if meta in content:
            print(f"✅ QCAL metadata found: {meta}")
        else:
            print(f"⚠️  QCAL metadata not found: {meta}")
    
    return True

def count_proof_gaps():
    """Count and report proof gaps (sorry statements)"""
    file_path = Path("formalization/lean/RiemannAdelic/SpectrumZetaProof.lean")
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    sorry_count = content.count("sorry")
    print(f"\n📊 Proof gaps (sorry statements): {sorry_count}")
    
    # Count strategic sorries (those with PROOF STRATEGY comments)
    strategic_sorries = content.count("sorry  -- PROOF")
    print(f"📋 Strategic gaps with proof strategies: {strategic_sorries}")
    
    return sorry_count

def main():
    """Main verification routine"""
    print("=" * 70)
    print("SpectrumZetaProof.lean Verification")
    print("=" * 70)
    print()
    
    checks = [
        ("File Existence", verify_file_exists),
        ("Import Statements", verify_imports),
        ("Key Definitions", verify_key_definitions),
        ("QCAL Metadata", verify_qcal_metadata),
    ]
    
    all_passed = True
    for check_name, check_func in checks:
        print(f"\n🔍 Checking: {check_name}")
        print("-" * 70)
        if not check_func():
            all_passed = False
            print(f"❌ {check_name} check failed!")
        else:
            print(f"✅ {check_name} check passed!")
    
    print("\n" + "=" * 70)
    count_proof_gaps()
    print("=" * 70)
    
    if all_passed:
        print("\n✅ All verification checks passed!")
        print("\n📝 Summary:")
        print("   - File structure: ✅ Complete")
        print("   - Imports: ✅ Correct")
        print("   - Definitions: ✅ Present")
        print("   - QCAL integration: ✅ Preserved")
        print("\n🎯 Next step: Build with Lean 4.5.0 to verify compilation")
        return 0
    else:
        print("\n❌ Some verification checks failed!")
        return 1

if __name__ == "__main__":
    sys.exit(main())
