#!/usr/bin/env python3
"""
Lean Syntax Validator

This script performs basic syntax validation on Lean 4 files to check for
common errors before compilation.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple

def check_balanced_parens(content: str, filename: str) -> List[str]:
    """Check if parentheses, brackets, and braces are balanced."""
    errors = []
    
    pairs = {
        '(': ')',
        '[': ']',
        '{': '}',
        '⟨': '⟩'
    }
    
    for open_char, close_char in pairs.items():
        open_count = content.count(open_char)
        close_count = content.count(close_char)
        if open_count != close_count:
            errors.append(
                f"{filename}: Unbalanced {open_char}{close_char}: "
                f"{open_count} open vs {close_count} close"
            )
    
    return errors

def check_namespace_structure(content: str, filename: str) -> List[str]:
    """Check namespace structure."""
    errors = []
    
    # Check namespace definitions
    namespace_opens = re.findall(r'^namespace\s+(\w+)', content, re.MULTILINE)
    namespace_ends = re.findall(r'^end\s+(\w+)', content, re.MULTILINE)
    
    # For simple check, just count them
    open_count = len(namespace_opens)
    end_count = len(namespace_ends)
    
    if open_count != end_count:
        errors.append(
            f"{filename}: Namespace mismatch: {open_count} opens vs {end_count} ends"
        )
    
    return errors

def check_imports(content: str, filename: str) -> List[str]:
    """Check import statements."""
    errors = []
    
    lines = content.split('\n')
    first_non_comment_line = None
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped and not stripped.startswith('--') and not stripped.startswith('/-'):
            first_non_comment_line = i
            break
    
    if first_non_comment_line is not None:
        # Check if imports come before other code
        seen_import = False
        seen_other = False
        
        for line in lines[first_non_comment_line:]:
            stripped = line.strip()
            if not stripped or stripped.startswith('--'):
                continue
            if stripped.startswith('import '):
                if seen_other:
                    errors.append(
                        f"{filename}: Import statement after other code"
                    )
                seen_import = True
            else:
                seen_other = True
    
    return errors

def check_theorem_structure(content: str, filename: str) -> List[str]:
    """Check theorem and lemma structure."""
    errors = []
    
    # Find theorem/lemma declarations
    theorems = re.finditer(
        r'(theorem|lemma|def|axiom)\s+(\w+)[^:]*:(.*?)(?=\n(?:theorem|lemma|def|axiom|\Z))',
        content,
        re.DOTALL | re.MULTILINE
    )
    
    for match in theorems:
        kind = match.group(1)
        name = match.group(2)
        body = match.group(3)
        
        # Check for unclosed := by
        if ':=' in body and 'by' in body:
            # Simple check: should have balanced structure
            pass  # More complex check would be needed
    
    return errors

def validate_lean_file(filepath: Path) -> Tuple[bool, List[str]]:
    """Validate a single Lean file."""
    errors = []
    
    try:
        content = filepath.read_text()
        filename = filepath.name
        
        # Run checks
        errors.extend(check_balanced_parens(content, filename))
        errors.extend(check_namespace_structure(content, filename))
        errors.extend(check_imports(content, filename))
        errors.extend(check_theorem_structure(content, filename))
        
        # Check for common syntax errors
        if re.search(r':=\s*$', content, re.MULTILINE):
            errors.append(f"{filename}: Declaration ends with ':=' without body")
        
        # Check for unterminated comments
        multiline_comments = re.findall(r'/\*.*?\*/', content, re.DOTALL)
        open_comments = content.count('/*')
        close_comments = content.count('*/')
        if open_comments != close_comments:
            errors.append(
                f"{filename}: Unterminated multi-line comment: "
                f"{open_comments} open vs {close_comments} close"
            )
        
    except Exception as e:
        errors.append(f"{filepath}: Error reading file: {e}")
    
    return len(errors) == 0, errors

def main():
    """Main validation routine."""
    lean_dir = Path(__file__).parent
    
    print("=" * 70)
    print("Lean 4 Syntax Validator")
    print("=" * 70)
    print()
    
    # Find all .lean files
    lean_files = list(lean_dir.rglob("*.lean"))
    
    if not lean_files:
        print("❌ No Lean files found!")
        return 1
    
    print(f"Found {len(lean_files)} Lean files to validate")
    print()
    
    all_errors = []
    valid_count = 0
    
    for filepath in sorted(lean_files):
        relative_path = filepath.relative_to(lean_dir)
        is_valid, errors = validate_lean_file(filepath)
        
        if is_valid:
            print(f"✅ {relative_path}")
            valid_count += 1
        else:
            print(f"⚠️  {relative_path}")
            for error in errors:
                print(f"   - {error}")
            all_errors.extend(errors)
    
    print()
    print("=" * 70)
    print(f"Validation Results: {valid_count}/{len(lean_files)} files valid")
    print("=" * 70)
    
    if all_errors:
        print()
        print("Errors found:")
        for error in all_errors:
            print(f"  - {error}")
        return 1
    else:
        print()
        print("✅ All files passed basic syntax validation!")
        print()
        print("Note: This is a basic syntax check. Full compilation with")
        print("      'lake build' is needed for complete verification.")
        return 0

if __name__ == "__main__":
    sys.exit(main())
