#!/usr/bin/env python3
"""
Verification script to check for 'sorry' statements in Lean files.

This script verifies that specific Lean modules have zero sorry statements,
indicating complete formal proofs.

Usage:
    python scripts/verify_no_sorrys.py [file_path]
    
If no file path is provided, checks FredholmDetEqualsXi.lean by default.
"""

import sys
import re
from pathlib import Path


def count_sorrys(file_path: Path) -> int:
    """
    Count the number of 'sorry' statements in a Lean file.
    Excludes comments and string literals.
    
    Args:
        file_path: Path to the Lean file
        
    Returns:
        Number of sorry statements found
    """
    if not file_path.exists():
        print(f"❌ Error: File not found: {file_path}")
        return -1
    
    content = file_path.read_text(encoding='utf-8')
    
    # Remove block comments /-  -/
    content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
    
    # Remove line comments --
    lines = content.split('\n')
    code_lines = []
    for line in lines:
        # Remove everything after --
        if '--' in line:
            line = line[:line.index('--')]
        code_lines.append(line)
    
    code_content = '\n'.join(code_lines)
    
    # Count sorry statements (word boundary to avoid 'nosorry' etc)
    sorries = len(re.findall(r'\bsorry\b', code_content))
    
    return sorries


def verify_file(file_path: Path) -> bool:
    """
    Verify a Lean file has zero sorrys.
    
    Args:
        file_path: Path to the Lean file
        
    Returns:
        True if file has 0 sorrys, False otherwise
    """
    print(f"Checking: {file_path}")
    
    if not file_path.exists():
        print(f"❌ File not found: {file_path}")
        return False
    
    sorry_count = count_sorrys(file_path)
    
    if sorry_count < 0:
        return False
    
    file_size = file_path.stat().st_size
    print(f"   Size: {file_size} bytes")
    print(f"   Sorrys: {sorry_count}")
    
    if sorry_count == 0:
        print(f"✅ {file_path.name}: ✅ 0 sorrys")
        return True
    else:
        print(f"❌ {file_path.name}: ⚠️  {sorry_count} sorrys found")
        return False


def main():
    """Main entry point for the verification script."""
    
    # Determine which file to check
    if len(sys.argv) > 1:
        file_path = Path(sys.argv[1])
    else:
        # Default to FredholmDetEqualsXi.lean
        file_path = Path("formalization/lean/RH_final_v6/FredholmDetEqualsXi.lean")
    
    print("=" * 70)
    print("VERIFICATION: Lean Sorry Counter")
    print("=" * 70)
    print()
    
    success = verify_file(file_path)
    
    print()
    print("=" * 70)
    if success:
        print("✅ VERIFICATION PASSED: No sorrys found!")
    else:
        print("❌ VERIFICATION FAILED: Sorrys detected or file error")
    print("=" * 70)
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
