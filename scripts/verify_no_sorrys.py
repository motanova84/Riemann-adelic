#!/usr/bin/env python3
"""
Verification script for Lean formalization modules
Checks for 'sorry' statements in specified Lean files

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Date: 2025-11-22
"""

import sys
import re
from pathlib import Path
import re

def count_sorrys(file_path: Path) -> tuple[int, list[int]]:
    """
    Count sorrys in a Lean file, excluding those in comments.
    Returns: (count, line_numbers)
    """
    if not file_path.exists():
        return -1, []
    
    content = file_path.read_text()
    lines = content.split('\n')
    
    sorry_count = 0
    sorry_lines = []
    in_block_comment = False
    
    for i, line in enumerate(lines, start=1):
        # Track block comments
        if '/-' in line:
            in_block_comment = True
        if '-/' in line:
            in_block_comment = False
            continue
        
        # Skip if in block comment or line comment
        if in_block_comment:
            continue
        
        # Check for line comments
        comment_pos = line.find('--')
        sorry_pos = line.find('sorry')
        
        # If sorry appears before comment or no comment, count it
        if sorry_pos != -1:
            if comment_pos == -1 or sorry_pos < comment_pos:
                sorry_count += 1
                sorry_lines.append(i)
    
    return sorry_count, sorry_lines


def main():
    print("=" * 70)
    print("Verification: Lean Modules - Sorry Statement Check")
    print("=" * 70)
    
    base_path = Path(__file__).parent.parent / "formalization" / "lean" / "RH_final_v6"
    
    modules = [
        "NuclearityExplicit.lean",
        "FredholmDetEqualsXi.lean",
        "UniquenessWithoutRH.lean",
        "RHComplete.lean"
    ]
    
    results = {}
    total_sorrys = 0
    all_passed = True
    
    print("\nChecking modules:")
    print("-" * 70)
    
    for module in modules:
        file_path = base_path / module
        count, lines = count_sorrys(file_path)
        
        if count == -1:
            print(f"❌ {module}: FILE NOT FOUND")
            all_passed = False
            results[module] = ("NOT FOUND", [])
        elif count == 0:
            print(f"✅ {module}: 0 sorrys")
            results[module] = ("COMPLETE", [])
        else:
            print(f"⚠️  {module}: {count} sorry(s) at lines {lines}")
            all_passed = False
            results[module] = (f"{count} sorrys", lines)
            total_sorrys += count
    
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    # Table format
    print(f"\n{'Module':<35} {'sorry':<10} {'Estado':<15}")
    print("-" * 70)
    for module in modules:
        status, lines = results[module]
        if status == "COMPLETE":
            print(f"{module:<35} {'0':<10} ✅ CERRADO")
        elif status == "NOT FOUND":
            print(f"{module:<35} {'N/A':<10} ❌ NO ENCONTRADO")
        else:
            sorry_count = status.split()[0]
            print(f"{module:<35} {sorry_count:<10} ⚠️  PENDIENTE")
    
    print("\n" + "=" * 70)
    
    if all_passed:
        print("🎉 ¡LISTO! Todos los módulos sin sorrys")
        print("\n✅ Verificación inmediata completada exitosamente")
        print("✅ Los 4 módulos están completos y sin sorrys")
        return 0
    else:
        print(f"⚠️  Total de sorrys restantes: {total_sorrys}")
        print(f"⚠️  Se necesita trabajo adicional en los módulos marcados")
        return 1


if __name__ == "__main__":
    sys.exit(main())
