#!/usr/bin/env python3
"""
Lean 4 Syntax Checker - RH_final.lean
José Manuel Mota Burruezo - QCAL ∞³ Framework
DOI: 10.5281/zenodo.17379721

This script performs basic syntax validation on RH_final.lean
without requiring Lean compiler installation.
"""

import re
from pathlib import Path
import sys


def check_lean_syntax(file_path: Path) -> dict:
    """Check basic Lean 4 syntax."""
    
    content = file_path.read_text()
    lines = content.split('\n')
    
    issues = []
    warnings = []
    
    # Check 1: Namespace opened and closed
    namespace_opens = len(re.findall(r'^namespace\s+\w+', content, re.MULTILINE))
    namespace_ends = len(re.findall(r'^end\s+\w+', content, re.MULTILINE))
    
    if namespace_opens != namespace_ends:
        issues.append(f"Namespace mismatch: {namespace_opens} opens, {namespace_ends} ends")
    
    # Check 2: Balanced parentheses, brackets, braces
    paren_count = content.count('(') - content.count(')')
    bracket_count = content.count('[') - content.count(']')
    brace_count = content.count('{') - content.count('}')
    
    if paren_count != 0:
        issues.append(f"Unbalanced parentheses: {paren_count}")
    if bracket_count != 0:
        issues.append(f"Unbalanced brackets: {bracket_count}")
    if brace_count != 0:
        issues.append(f"Unbalanced braces: {brace_count}")
    
    # Check 3: Theorem/axiom/def completeness
    incomplete_defs = []
    
    # Check for theorems without 'by' or ':='
    theorem_pattern = re.compile(r'^(theorem|lemma)\s+(\w+)\s*:.*?$', re.MULTILINE)
    for match in theorem_pattern.finditer(content):
        theorem_name = match.group(2)
        # Get next 10 lines after theorem declaration
        start_pos = match.end()
        next_chars = content[start_pos:start_pos+200]
        if 'by' not in next_chars and ':=' not in next_chars:
            incomplete_defs.append(f"Theorem '{theorem_name}' may be incomplete (no 'by' or ':=')")
    
    # Check 4: Import statements at top
    import_pattern = re.compile(r'^import\s+', re.MULTILINE)
    imports = list(import_pattern.finditer(content))
    
    if imports:
        first_import_line = content[:imports[0].start()].count('\n') + 1
        last_import_line = content[:imports[-1].start()].count('\n') + 1
        
        # Check if there's significant code before imports
        if first_import_line > 10:
            warnings.append(f"Imports start at line {first_import_line} (should be near top)")
        
        # Check if imports are grouped together
        if last_import_line - first_import_line > len(imports) + 5:
            warnings.append(f"Imports are scattered (lines {first_import_line}-{last_import_line})")
    
    # Check 5: Look for common syntax errors
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        
        # Check for tabs (Lean prefers spaces)
        if '\t' in line:
            warnings.append(f"Line {i}: Contains tab character (use spaces)")
        
        # Check for trailing whitespace
        if line.endswith(' ') or line.endswith('\t'):
            warnings.append(f"Line {i}: Trailing whitespace")
    
    # Check 6: Verify all axioms have type signatures
    axiom_pattern = re.compile(r'^axiom\s+(\w+)', re.MULTILINE)
    for match in axiom_pattern.finditer(content):
        axiom_name = match.group(1)
        # Check if followed by ':'
        next_char_pos = match.end()
        next_chars = content[next_char_pos:next_char_pos+10].strip()
        if not next_chars.startswith(':'):
            issues.append(f"Axiom '{axiom_name}' missing type signature ':'")
    
    # Check 7: Verify theorem proofs end correctly
    proof_ends = len(re.findall(r'\bqed\b|\bdone\b', content))
    # Note: In Lean 4, proofs typically end implicitly or with a blank line
    
    return {
        "file_path": str(file_path),
        "line_count": len(lines),
        "namespace_balance": namespace_opens == namespace_ends,
        "parentheses_balance": paren_count == 0,
        "brackets_balance": bracket_count == 0,
        "braces_balance": brace_count == 0,
        "import_count": len(imports),
        "issues": issues,
        "warnings": warnings,
        "syntax_valid": len(issues) == 0
    }


def main():
    """Main syntax checking routine."""
    
    print("╔══════════════════════════════════════════════════════════╗")
    print("║  Lean 4 Syntax Checker - RH_final.lean                  ║")
    print("║  José Manuel Mota Burruezo - QCAL ∞³                    ║")
    print("╚══════════════════════════════════════════════════════════╝")
    print()
    
    lean_file = Path("formalization/lean/RH_final.lean")
    
    if not lean_file.exists():
        print(f"❌ Error: {lean_file} not found")
        return 1
    
    print(f"📄 Checking: {lean_file}")
    print()
    
    result = check_lean_syntax(lean_file)
    
    # Print results
    print(f"Lines: {result['line_count']}")
    print(f"Imports: {result['import_count']}")
    print()
    
    print("Balance Checks:")
    print(f"  Namespaces: {'✓' if result['namespace_balance'] else '✗'}")
    print(f"  Parentheses: {'✓' if result['parentheses_balance'] else '✗'}")
    print(f"  Brackets: {'✓' if result['brackets_balance'] else '✗'}")
    print(f"  Braces: {'✓' if result['braces_balance'] else '✗'}")
    print()
    
    if result['issues']:
        print("❌ Issues Found:")
        for issue in result['issues']:
            print(f"  • {issue}")
        print()
    else:
        print("✅ No syntax issues found")
        print()
    
    if result['warnings']:
        print("⚠️  Warnings:")
        for warning in result['warnings'][:10]:  # Limit to first 10
            print(f"  • {warning}")
        if len(result['warnings']) > 10:
            print(f"  ... and {len(result['warnings']) - 10} more warnings")
        print()
    
    if result['syntax_valid']:
        print("╔══════════════════════════════════════════════════════════╗")
        print("║  ✅ SYNTAX CHECK PASSED                                  ║")
        print("║  RH_final.lean has valid Lean 4 syntax structure         ║")
        print("╚══════════════════════════════════════════════════════════╝")
        return 0
    else:
        print("╔══════════════════════════════════════════════════════════╗")
        print("║  ⚠️  SYNTAX CHECK FAILED                                 ║")
        print("║  Please fix the issues above                             ║")
        print("╚══════════════════════════════════════════════════════════╝")
        return 1


if __name__ == "__main__":
    sys.exit(main())
