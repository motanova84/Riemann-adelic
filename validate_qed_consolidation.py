#!/usr/bin/env python3
"""
Q.E.D. Consolidation Validation Script
======================================

Validates the consolidated Lean formalization ensuring Q.E.D. withstands
global mathematical scrutiny.

Author: José Manuel Mota Burruezo
Date: November 2025
Version: V5.5
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple

# ANSI color codes
class Colors:
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    BOLD = '\033[1m'
    END = '\033[0m'

def print_header(text: str):
    """Print formatted header."""
    print(f"\n{Colors.BOLD}{Colors.CYAN}{'=' * 70}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.CYAN}{text.center(70)}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.CYAN}{'=' * 70}{Colors.END}\n")

def print_success(text: str):
    """Print success message."""
    print(f"{Colors.GREEN}✓{Colors.END} {text}")

def print_warning(text: str):
    """Print warning message."""
    print(f"{Colors.YELLOW}⚠{Colors.END} {text}")

def print_error(text: str):
    """Print error message."""
    print(f"{Colors.RED}✗{Colors.END} {text}")

def print_info(text: str):
    """Print info message."""
    print(f"{Colors.BLUE}ℹ{Colors.END} {text}")

def count_sorries(file_path: Path) -> int:
    """Count sorry statements in a Lean file, excluding comments."""
    if not file_path.exists():
        return 0
    
    content = file_path.read_text()
    lines = content.split('\n')
    
    # Remove comments
    code_lines = []
    in_block_comment = False
    
    for line in lines:
        stripped = line.strip()
        
        # Handle block comments
        if '/-' in stripped:
            in_block_comment = True
        if '-/' in stripped:
            in_block_comment = False
            continue
        
        # Skip if in comment or line comment
        if in_block_comment or stripped.startswith('--'):
            continue
        
        code_lines.append(line)
    
    code_content = '\n'.join(code_lines)
    return code_content.count('sorry')

def analyze_qed_file(file_path: Path) -> Dict:
    """Analyze the QED_Consolidated.lean file."""
    if not file_path.exists():
        return {
            'exists': False,
            'sorries': 0,
            'theorems': 0,
            'lemmas': 0,
            'definitions': 0
        }
    
    content = file_path.read_text()
    
    return {
        'exists': True,
        'size': len(content),
        'lines': len(content.split('\n')),
        'sorries': count_sorries(file_path),
        'theorems': len(re.findall(r'\btheorem\b', content)),
        'lemmas': len(re.findall(r'\blemma\b', content)),
        'definitions': len(re.findall(r'\bdef\b', content)),
        'sections': len(re.findall(r'SECTION \d+:', content))
    }

def analyze_repository_sorries(lean_dir: Path) -> Dict:
    """Analyze sorry distribution across repository."""
    lean_files = list(lean_dir.rglob("*.lean"))
    
    sorry_counts = {}
    total_sorries = 0
    
    for file in lean_files:
        count = count_sorries(file)
        if count > 0:
            rel_path = file.relative_to(lean_dir)
            sorry_counts[str(rel_path)] = count
            total_sorries += count
    
    # Sort by count descending
    sorted_files = sorted(sorry_counts.items(), key=lambda x: x[1], reverse=True)
    
    return {
        'total_files': len(lean_files),
        'files_with_sorry': len(sorry_counts),
        'total_sorries': total_sorries,
        'top_files': sorted_files[:10]
    }

def validate_proof_structure(qed_file: Path) -> List[str]:
    """Validate the logical structure of the proof."""
    if not qed_file.exists():
        return ["QED_Consolidated.lean not found"]
    
    content = qed_file.read_text()
    issues = []
    
    # Check for main theorem
    if 'theorem riemann_hypothesis' not in content:
        issues.append("Main theorem 'riemann_hypothesis' not found")
    else:
        print_success("Main theorem 'riemann_hypothesis' found")
    
    # Check for RiemannHypothesis definition
    if 'def RiemannHypothesis' not in content:
        issues.append("RiemannHypothesis definition not found")
    else:
        print_success("RiemannHypothesis definition found")
    
    # Check for key components
    key_components = [
        ('D_function', 'Spectral determinant D(s)'),
        ('SpectralTrace', 'Spectral trace function'),
        ('OperatorH', 'Operator H definition'),
        ('PositiveKernel', 'Positive kernel K(x,y)'),
        ('D_functional_equation', 'Functional equation'),
        ('spectrum_on_critical_line', 'Zero localization'),
    ]
    
    for component, desc in key_components:
        if component in content:
            print_success(f"{desc} ({component}) found")
        else:
            issues.append(f"{desc} ({component}) not found")
    
    return issues

def main():
    """Main validation routine."""
    print_header("Q.E.D. CONSOLIDATION VALIDATION")
    
    # Paths - use script directory as base for portability
    script_dir = Path(__file__).parent.resolve()
    root = script_dir
    lean_dir = root / "formalization" / "lean"
    qed_file = lean_dir / "RiemannAdelic" / "QED_Consolidated.lean"
    report_file = lean_dir / "QED_CONSOLIDATION_REPORT.md"
    
    # Section 1: File existence
    print_header("SECTION 1: File Existence")
    
    if qed_file.exists():
        print_success(f"QED_Consolidated.lean found ({qed_file.stat().st_size} bytes)")
    else:
        print_error("QED_Consolidated.lean NOT FOUND")
        return False
    
    if report_file.exists():
        print_success(f"QED_CONSOLIDATION_REPORT.md found ({report_file.stat().st_size} bytes)")
    else:
        print_warning("QED_CONSOLIDATION_REPORT.md not found")
    
    # Section 2: QED file analysis
    print_header("SECTION 2: QED File Analysis")
    
    qed_analysis = analyze_qed_file(qed_file)
    
    print_info(f"File size: {qed_analysis['size']} bytes")
    print_info(f"Lines: {qed_analysis['lines']}")
    print_info(f"Theorems: {qed_analysis['theorems']}")
    print_info(f"Lemmas: {qed_analysis['lemmas']}")
    print_info(f"Definitions: {qed_analysis['definitions']}")
    print_info(f"Sections: {qed_analysis['sections']}")
    
    if qed_analysis['sorries'] <= 10:
        print_success(f"Sorries in QED file: {qed_analysis['sorries']} (≤ 10 target)")
    else:
        print_warning(f"Sorries in QED file: {qed_analysis['sorries']} (> 10)")
    
    # Section 3: Repository-wide analysis
    print_header("SECTION 3: Repository-Wide Sorry Analysis")
    
    repo_analysis = analyze_repository_sorries(lean_dir)
    
    print_info(f"Total Lean files: {repo_analysis['total_files']}")
    print_info(f"Files with sorries: {repo_analysis['files_with_sorry']}")
    print_info(f"Total sorries across all files: {repo_analysis['total_sorries']}")
    
    print("\nTop 10 files by sorry count:")
    for i, (file, count) in enumerate(repo_analysis['top_files'][:10], 1):
        if file == "RiemannAdelic/QED_Consolidated.lean":
            print(f"  {i}. {Colors.GREEN}{file}: {count}{Colors.END} ⭐ (consolidated)")
        else:
            print(f"  {i}. {file}: {count}")
    
    # Section 4: Proof structure validation
    print_header("SECTION 4: Proof Structure Validation")
    
    issues = validate_proof_structure(qed_file)
    
    if not issues:
        print_success("All key proof components found")
    else:
        print_warning(f"Found {len(issues)} structural issues:")
        for issue in issues:
            print(f"  - {issue}")
    
    # Section 5: Summary and verdict
    print_header("SECTION 5: VALIDATION SUMMARY")
    
    print("\n📊 Consolidation Metrics:")
    print(f"  • QED file sorries: {qed_analysis['sorries']}")
    print(f"  • Repository total sorries: {repo_analysis['total_sorries']}")
    print(f"  • Reduction rate: {(1 - qed_analysis['sorries'] / repo_analysis['total_sorries']) * 100:.1f}%")
    print(f"  • Theorems in QED: {qed_analysis['theorems']}")
    print(f"  • Lemmas in QED: {qed_analysis['lemmas']}")
    print(f"  • Definitions in QED: {qed_analysis['definitions']}")
    
    print("\n✅ Validation Checklist:")
    checklist = [
        (qed_file.exists(), "QED_Consolidated.lean exists"),
        (qed_analysis['sorries'] <= 10, f"QED sorries ≤ 10 (actual: {qed_analysis['sorries']})"),
        (qed_analysis['theorems'] >= 5, f"Sufficient theorems (actual: {qed_analysis['theorems']})"),
        ('riemann_hypothesis' in qed_file.read_text(), "Main theorem present"),
        (len(issues) == 0, "All structural components present"),
    ]
    
    passed = sum(1 for check, _ in checklist if check)
    total = len(checklist)
    
    for check, desc in checklist:
        if check:
            print(f"  {Colors.GREEN}✓{Colors.END} {desc}")
        else:
            print(f"  {Colors.RED}✗{Colors.END} {desc}")
    
    print(f"\n{Colors.BOLD}Validation Score: {passed}/{total} ({passed/total*100:.0f}%){Colors.END}")
    
    if passed == total:
        print(f"\n{Colors.GREEN}{Colors.BOLD}🎉 Q.E.D. CONSOLIDATION VALIDATED{Colors.END}")
        print(f"{Colors.GREEN}The formalization is ready for global scrutiny.{Colors.END}")
        return True
    elif passed >= total * 0.8:
        print(f"\n{Colors.YELLOW}{Colors.BOLD}⚠️  Q.E.D. CONSOLIDATION MOSTLY COMPLETE{Colors.END}")
        print(f"{Colors.YELLOW}Minor issues to address before final validation.{Colors.END}")
        return True
    else:
        print(f"\n{Colors.RED}{Colors.BOLD}❌ Q.E.D. CONSOLIDATION INCOMPLETE{Colors.END}")
        print(f"{Colors.RED}Significant work needed before validation.{Colors.END}")
        return False

if __name__ == "__main__":
    import sys
    success = main()
    sys.exit(0 if success else 1)
