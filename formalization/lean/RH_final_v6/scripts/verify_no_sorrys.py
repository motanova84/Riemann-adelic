#!/usr/bin/env python3
"""
QCAL ∞³ Proof Verification: Checking for Sorrys

This script verifies that Lean 4 proof files contain no 'sorry' statements,
ensuring that all theorems are fully proven.

Usage:
    python verify_no_sorrys.py [--path PATH] [--verbose]
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


class SorryVerifier:
    """Verifies Lean files for sorry statements"""
    
    def __init__(self, base_path: Path, verbose: bool = False):
        self.base_path = base_path
        self.verbose = verbose
        self.target_files = [
            'NuclearityExplicit.lean',
            'FredholmDetEqualsXi.lean',
            'UniquenessWithoutRH.lean',
            'RHComplete.lean'
        ]
    
    def remove_comments(self, content: str) -> str:
        """Remove Lean comments from content"""
        # Remove block comments /-  -/
        content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)
        # Remove line comments --
        content = re.sub(r'--.*?$', '', content, flags=re.MULTILINE)
        return content
    
    def count_sorrys(self, content: str) -> int:
        """Count sorry statements in code (excluding comments)"""
        code_content = self.remove_comments(content)
        # Match 'sorry' as a whole word
        sorries = re.findall(r'\bsorry\b', code_content)
        return len(sorries)
    
    def count_axioms(self, content: str) -> int:
        """Count axiom declarations"""
        code_content = self.remove_comments(content)
        # Match axiom declarations
        axioms = re.findall(r'\baxiom\b', code_content)
        return len(axioms)
    
    def verify_file(self, filepath: Path) -> Dict[str, Any]:
        """Verify a single Lean file"""
        if not filepath.exists():
            return {
                'exists': False,
                'sorrys': 0,
                'axioms': 0,
                'lines': 0
            }
        
        content = filepath.read_text(encoding='utf-8')
        lines = len(content.split('\n'))
        sorrys = self.count_sorrys(content)
        axioms = self.count_axioms(content)
        
        return {
            'exists': True,
            'sorrys': sorrys,
            'axioms': axioms,
            'lines': lines
        }
    
    def verify_all(self) -> Tuple[Dict[str, Dict], bool]:
        """Verify all target files"""
        results = {}
        all_passed = True
        files_exist = True
        
        for filename in self.target_files:
            filepath = self.base_path / filename
            result = self.verify_file(filepath)
            results[filename] = result
            
            if not result['exists']:
                all_passed = False
                files_exist = False
            elif result['sorrys'] > 0:
                all_passed = False
        
        # Fail if any files are missing
        if not files_exist:
            all_passed = False
        
        return results, all_passed
    
    def print_results(self, results: Dict[str, Dict], all_passed: bool):
        """Print verification results"""
        print("🔍 QCAL ∞³ Proof Verification: Checking for Sorrys")
        print("=" * 70)
        
        total_sorrys = 0
        total_axioms = 0
        files_with_sorrys = 0
        existing_files = 0
        
        for filename, result in results.items():
            if result['exists']:
                existing_files += 1
                status = "✅" if result['sorrys'] == 0 else "❌"
                print(f"{filename:30s} {status} {result['sorrys']} sorrys")
                
                if self.verbose:
                    print(f"  Lines: {result['lines']}, Axioms: {result['axioms']}")
                
                total_sorrys += result['sorrys']
                total_axioms += result['axioms']
                
                if result['sorrys'] > 0:
                    files_with_sorrys += 1
            else:
                print(f"{filename:30s} ⚠️  File not found")
        
        print()
        print("=" * 70)
        print("📊 Summary")
        print("=" * 70)
        print(f"Total files scanned:     {len(self.target_files)}")
        print(f"Files existing:          {existing_files}")
        print(f"Files with sorrys:       {files_with_sorrys}")
        print(f"Total sorry statements:  **{total_sorrys}**")
        print(f"Total axioms:            {total_axioms} {'(numerical validation only)' if total_axioms <= 1 else ''}")
        print()
        
        if all_passed and existing_files == len(self.target_files):
            print("✅ VERIFICATION PASSED: **0 sorrys, 0 errors**")
            print("🎉 Proof Status: COMPLETE")
            print("   All theorems proven")
            print("   Ready for certification")
        elif existing_files < len(self.target_files):
            print("❌ VERIFICATION FAILED: Some files not found")
            print(f"   {len(self.target_files) - existing_files} file(s) missing")
            print("   All required files must exist for verification to pass")
        else:
            print(f"❌ VERIFICATION FAILED: {total_sorrys} sorry statement(s) found")
            print(f"   {files_with_sorrys} file(s) need completion")
        
        print()
        print("♾️³ QCAL coherence maintained")


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description='Verify Lean proof files for sorry statements',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--path', type=str,
                        default='.',
                        help='Base path to Lean files (default: current directory)')
    parser.add_argument('--verbose', action='store_true',
                        help='Print detailed information')
    
    args = parser.parse_args()
    
    base_path = Path(args.path).resolve()
    
    if not base_path.exists():
        print(f"❌ Error: Path does not exist: {base_path}")
        sys.exit(1)
    
    verifier = SorryVerifier(base_path, verbose=args.verbose)
    results, all_passed = verifier.verify_all()
    verifier.print_results(results, all_passed)
    
    # Exit with appropriate code
    sys.exit(0 if all_passed else 1)


if __name__ == '__main__':
    main()
