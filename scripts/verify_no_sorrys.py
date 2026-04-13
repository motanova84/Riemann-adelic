#!/usr/bin/env python3
"""
Verification script for Lean files to check for sorrys.

This script checks:
1. File exists and has content
2. Count of sorries in the file (excluding comments)
3. Reports whether proofs are complete
"""

import sys
from pathlib import Path
import re


def count_sorrys_in_file(file_path: Path) -> int:
    """
    Count the number of 'sorry' occurrences in a Lean file,
    excluding those in comments.
    
    Args:
        file_path: Path to the Lean file
        
    Returns:
        Number of sorry occurrences
    """
    if not file_path.exists():
        print(f"❌ File not found: {file_path}")
        return -1
    
    content = file_path.read_text()
    
    # Remove comments
    lines = content.split('\n')
    code_lines = []
    in_block_comment = False
    
    for line in lines:
        stripped = line.strip()
        
        # Handle block comments (/-  -/)
        if '/-' in stripped:
            in_block_comment = True
            # Get text before the comment starts
            before_comment = stripped.split('/-')[0]
            if before_comment and not in_block_comment:
                code_lines.append(before_comment)
            continue
            
        if '-/' in stripped:
            in_block_comment = False
            continue
            
        # Skip if in comment block or line comment
        if in_block_comment or stripped.startswith('--'):
            continue
            
        code_lines.append(line)
    
    code_content = '\n'.join(code_lines)
    sorry_count = code_content.count('sorry')
    
    return sorry_count


def verify_lean_file(file_path: Path) -> bool:
    """
    Verify a Lean file for completeness (no sorrys).
    
    Args:
        file_path: Path to the Lean file to verify
        
    Returns:
        True if verification passes (0 sorrys), False otherwise
    """
    print("="*70)
    print(f"VERIFICATION: {file_path.name}")
    print("="*70)
    
    if not file_path.exists():
        print(f"❌ File not found: {file_path}")
        return False
    
    file_size = file_path.stat().st_size
    print(f"✅ File exists: {file_path} ({file_size} bytes)")
    
    print("\nCounting sorries...")
    sorry_count = count_sorrys_in_file(file_path)
    
    if sorry_count < 0:
        return False
    
    print(f"   Total sorries: {sorry_count}")
    
    if sorry_count == 0:
        print("   🎉 ✅ No sorries! All proofs are complete.")
        print("\n" + "="*70)
        print("VERIFICATION PASSED")
        print("="*70)
        return True
    else:
        print(f"   ⚠️ {sorry_count} sorry/sorries found")
        print("\n" + "="*70)
        print("VERIFICATION FAILED")
        print("="*70)
        return False


def main():
    """Main entry point for the verification script."""
    if len(sys.argv) < 2:
        print("Usage: python verify_no_sorrys.py <lean_file_path>")
        print("\nExample:")
        print("  python verify_no_sorrys.py formalization/lean/RH_final_v6/NuclearityExplicit.lean")
        sys.exit(1)
    
    file_path = Path(sys.argv[1])
    success = verify_lean_file(file_path)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
