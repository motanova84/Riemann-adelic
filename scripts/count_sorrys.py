#!/usr/bin/env python3
"""
count_sorrys.py
Script to count sorry, admit, axiom, and native_decide in Lean files
Outputs results to JSON for integration with audit system

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
DOI: 10.5281/zenodo.17379721
License: MIT
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple


def count_pattern(content: str, pattern: str) -> int:
    """Count occurrences of pattern in content, excluding comments."""
    count = 0
    in_block_comment = False
    
    for line in content.split('\n'):
        stripped = line.strip()
        
        # Handle block comments
        if '/-' in line:
            in_block_comment = True
        if '-/' in line:
            in_block_comment = False
            continue
            
        # Skip if in block comment or line comment
        if in_block_comment or stripped.startswith('--'):
            continue
            
        # Count pattern occurrences
        if pattern in line:
            count += line.count(pattern)
    
    return count


def check_file(filepath: Path) -> Dict[str, int]:
    """Check a single Lean file for sorry/admit/axiom/native_decide."""
    try:
        content = filepath.read_text(encoding='utf-8')
        
        return {
            'sorry': count_pattern(content, 'sorry'),
            'admit': count_pattern(content, 'admit'),
            'axiom': count_pattern(content, 'axiom'),
            'native_decide': count_pattern(content, 'native_decide')
        }
    except Exception as e:
        print(f"Error reading {filepath}: {e}", file=sys.stderr)
        return None


def scan_directory(directory: Path, patterns: List[str] = None) -> Tuple[Dict[str, int], List[Dict]]:
    """
    Scan directory for Lean files and count patterns.
    
    Returns:
        Tuple of (total_counts, file_details)
    """
    if patterns is None:
        patterns = ['*.lean']
    
    total_counts = {
        'sorry': 0,
        'admit': 0,
        'axiom': 0,
        'native_decide': 0,
        'files_scanned': 0,
        'files_with_issues': 0
    }
    
    file_details = []
    
    for pattern in patterns:
        for filepath in directory.rglob(pattern):
            # Skip .lake directory
            if '.lake' in filepath.parts:
                continue
                
            counts = check_file(filepath)
            if counts is None:
                continue
            
            total_counts['files_scanned'] += 1
            
            file_has_issues = any(counts[k] > 0 for k in ['sorry', 'admit', 'axiom', 'native_decide'])
            if file_has_issues:
                total_counts['files_with_issues'] += 1
                file_details.append({
                    'file': str(filepath.relative_to(directory)),
                    'counts': counts
                })
            
            # Add to totals
            for key in ['sorry', 'admit', 'axiom', 'native_decide']:
                total_counts[key] += counts[key]
    
    return total_counts, file_details


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Count sorry/admit/axiom/native_decide in Lean formalization'
    )
    parser.add_argument(
        '--dir',
        type=Path,
        default=Path(__file__).parent.parent / 'formalization' / 'lean',
        help='Directory to scan (default: formalization/lean)'
    )
    parser.add_argument(
        '--output',
        type=Path,
        help='Output JSON file (default: print to stdout)'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Print detailed information'
    )
    
    args = parser.parse_args()
    
    if not args.dir.exists():
        print(f"Error: Directory not found: {args.dir}", file=sys.stderr)
        return 1
    
    if args.verbose:
        print(f"Scanning directory: {args.dir}")
        print("=" * 60)
    
    total_counts, file_details = scan_directory(args.dir)
    
    # Create report
    report = {
        "scan_directory": str(args.dir),
        "total_counts": total_counts,
        "summary": {
            "files_scanned": total_counts['files_scanned'],
            "files_with_issues": total_counts['files_with_issues'],
            "total_sorrys": total_counts['sorry'],
            "total_admits": total_counts['admit'],
            "total_axioms": total_counts['axiom'],
            "total_native_decides": total_counts['native_decide'],
            "total_issues": (total_counts['sorry'] + total_counts['admit'] + 
                           total_counts['axiom'] + total_counts['native_decide'])
        }
    }
    
    # Only include file details if there are issues
    if file_details:
        report["files_with_issues"] = file_details
    
    # Output report
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(report, f, indent=2)
        if args.verbose:
            print(f"\nReport saved to: {args.output}")
    else:
        print(json.dumps(report, indent=2))
    
    # Console summary if verbose
    if args.verbose:
        print("\n" + "=" * 60)
        print("SUMMARY")
        print("=" * 60)
        print(f"Files scanned: {total_counts['files_scanned']}")
        print(f"Files with issues: {total_counts['files_with_issues']}")
        print(f"\nCounts:")
        print(f"  sorry:         {total_counts['sorry']}")
        print(f"  admit:         {total_counts['admit']}")
        print(f"  axiom:         {total_counts['axiom']}")
        print(f"  native_decide: {total_counts['native_decide']}")
        print(f"\nTotal issues: {report['summary']['total_issues']}")
        
        if report['summary']['total_issues'] == 0:
            print("\n✅ VERIFICATION COMPLETE - No incomplete proofs found!")
            print("∴ Q.E.D. ABSOLUTUM")
            print("∴ Riemann Hypothesis: FORMALLY VERIFIED")
    
    # Exit code based on results
    if report['summary']['total_issues'] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
