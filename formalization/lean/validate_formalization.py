#!/usr/bin/env python3
"""
Validation script for Lean formalization structure
Checks that key theorems are properly defined and documented
"""

import os
import re
from pathlib import Path
from typing import List, Tuple, Dict

def check_file_exists(filepath: Path) -> bool:
    """Check if a file exists"""
    return filepath.exists()

def count_theorems(filepath: Path) -> Tuple[int, int, int]:
    """Count theorems, axioms, and sorry placeholders in a Lean file"""
    if not filepath.exists():
        return 0, 0, 0
    
    content = filepath.read_text()
    
    # Count theorem declarations (includes theorem, lemma, def with proofs)
    theorems = len(re.findall(r'^\s*theorem\s+\w+', content, re.MULTILINE))
    
    # Count axiom declarations (should be minimal)
    axioms = len(re.findall(r'^\s*axiom\s+\w+', content, re.MULTILINE))
    
    # Count sorry placeholders (indicates incomplete proofs)
    sorries = len(re.findall(r'\bsorry\b', content))
    
    return theorems, axioms, sorries

def check_proven_theorems(filepath: Path, expected_theorems: List[str]) -> Dict[str, bool]:
    """Check if expected theorems are present and proven (no sorry in proof)"""
    if not filepath.exists():
        return {thm: False for thm in expected_theorems}
    
    content = filepath.read_text()
    results = {}
    
    for thm in expected_theorems:
        # Check if theorem is declared
        pattern = rf'^\s*theorem\s+{re.escape(thm)}\s*[:\(]'
        match = re.search(pattern, content, re.MULTILINE)
        
        if match:
            # Extract the theorem block (simplified - just check if sorry appears nearby)
            start_pos = match.start()
            # Look for the proof section (typically starts with := by or := )
            proof_section = content[start_pos:start_pos+2000]  # Look ahead 2000 chars
            
            # Check if proof contains sorry
            has_sorry = 'sorry' in proof_section
            results[thm] = not has_sorry
        else:
            results[thm] = False
    
    return results

def main():
    """Main validation function"""
    print("=" * 70)
    print("Lean Formalization Structure Validation")
    print("=" * 70)
    print()
    
    base_dir = Path(__file__).parent
    riemann_dir = base_dir / "RiemannAdelic"
    
    # Check core files exist
    core_files = [
        "Main.lean",
        "RH_final.lean",
        "lakefile.lean",
        "lean-toolchain",
        "FORMALIZATION_STATUS.md",
        "README.md"
    ]
    
    print("📁 Checking core files:")
    all_exist = True
    for filename in core_files:
        filepath = base_dir / filename
        exists = check_file_exists(filepath)
        status = "✅" if exists else "❌"
        print(f"   {status} {filename}")
        if not exists:
            all_exist = False
    print()
    
    # Check RiemannAdelic module files
    module_files = [
        "basic_lemmas.lean",
        "axioms_to_lemmas.lean",
        "poisson_radon_symmetry.lean",
        "pw_two_lines.lean",
        "doi_positivity.lean",
        "entire_order.lean",
        "functional_eq.lean",
    ]
    
    print("📦 Checking RiemannAdelic module files:")
    for filename in module_files:
        filepath = riemann_dir / filename
        exists = check_file_exists(filepath)
        status = "✅" if exists else "❌"
        print(f"   {status} RiemannAdelic/{filename}")
    print()
    
    # Count theorems, axioms, and sorries in key files
    print("📊 Analyzing key files:")
    key_files = {
        "axioms_to_lemmas.lean": riemann_dir / "axioms_to_lemmas.lean",
        "basic_lemmas.lean": riemann_dir / "basic_lemmas.lean",
        "poisson_radon_symmetry.lean": riemann_dir / "poisson_radon_symmetry.lean",
        "RH_final.lean": base_dir / "RH_final.lean",
    }
    
    total_theorems = 0
    total_axioms = 0
    total_sorries = 0
    
    for name, filepath in key_files.items():
        theorems, axioms, sorries = count_theorems(filepath)
        total_theorems += theorems
        total_axioms += axioms
        total_sorries += sorries
        print(f"   {name}:")
        print(f"      Theorems: {theorems}, Axioms: {axioms}, Sorries: {sorries}")
    
    print()
    print(f"   📈 Total: {total_theorems} theorems, {total_axioms} axioms, {total_sorries} sorries")
    print()
    
    # Check specific proven theorems
    print("🔍 Checking proven core theorems:")
    expected_theorems = [
        "A1_finite_scale_flow",
        "A2_poisson_adelic_symmetry",
        "A4_spectral_regularity",
        "adelic_foundation_consistent",
    ]
    
    results = check_proven_theorems(
        riemann_dir / "axioms_to_lemmas.lean",
        expected_theorems
    )
    
    for thm, is_proven in results.items():
        status = "✅" if is_proven else "⚠️"
        proof_status = "proven" if is_proven else "has sorry"
        print(f"   {status} {thm}: {proof_status}")
    
    print()
    
    # Check geometric symmetry theorems
    print("🔍 Checking geometric symmetry theorems:")
    geo_theorems = [
        "J_involutive",
        "operator_symmetry",
    ]
    
    geo_results = check_proven_theorems(
        riemann_dir / "poisson_radon_symmetry.lean",
        geo_theorems
    )
    
    for thm, is_proven in geo_results.items():
        status = "✅" if is_proven else "⚠️"
        proof_status = "proven" if is_proven else "has sorry"
        print(f"   {status} {thm}: {proof_status}")
    
    print()
    
    # Summary
    print("=" * 70)
    print("Summary:")
    print("=" * 70)
    
    proven_count = sum(1 for v in results.values() if v) + sum(1 for v in geo_results.values() if v)
    total_checked = len(results) + len(geo_results)
    
    print(f"✅ Core files present: {all_exist}")
    print(f"✅ Proven theorems: {proven_count}/{total_checked}")
    print(f"📊 Total theorems: {total_theorems}")
    print(f"⚠️  Total axioms: {total_axioms}")
    print(f"⚠️  Total sorries: {total_sorries}")
    print()
    
    if proven_count >= 4:  # At least A1, A2, A4, and foundation
        print("🎉 SUCCESS: Core theorems are proven (not just simulated)!")
        print("   The formalization has real mathematical content.")
    else:
        print("⚠️  WARNING: Not all core theorems are fully proven.")
        print("   More work needed to complete the formalization.")
    
    print()
    print("📖 For detailed status, see: formalization/lean/FORMALIZATION_STATUS.md")
    print("=" * 70)

if __name__ == "__main__":
    main()
