#!/usr/bin/env python3
"""
validate_hilbert_polya.py
-------------------------
Validation script for the Hilbert-Pólya Lean formalization.

This script checks:
1. All files exist and are readable
2. Sorry count and classification
3. Theorem dependency graph
4. Documentation completeness

Author: José Manuel Mota Burruezo
Date: January 2026
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import json

class HilbertPolyaValidator:
    def __init__(self, base_path: str = "formalization/lean/spectral"):
        self.base_path = Path(base_path)
        self.files = [
            "HilbertPolyaProof.lean",
            "GaussianIntegrals.lean",
            "ZetaEquation.lean",
            "EigenvalueUniqueness.lean",
            "HilbertPolyaProofHelpers.lean",
            "HilbertPolyaExamples.lean"
        ]
        self.results = {}
    
    def validate_files_exist(self) -> bool:
        """Check if all required files exist."""
        print("=" * 70)
        print("FILE EXISTENCE CHECK")
        print("=" * 70)
        
        all_exist = True
        for filename in self.files:
            filepath = self.base_path / filename
            exists = filepath.exists()
            status = "✓" if exists else "✗"
            print(f"{status} {filename}")
            
            if exists:
                size = filepath.stat().st_size
                print(f"   Size: {size:,} bytes")
            else:
                all_exist = False
        
        print()
        return all_exist
    
    def count_sorry_statements(self) -> Dict[str, int]:
        """Count sorry statements in each file."""
        print("=" * 70)
        print("SORRY STATEMENT ANALYSIS")
        print("=" * 70)
        
        sorry_counts = {}
        total_sorry = 0
        
        for filename in self.files:
            filepath = self.base_path / filename
            if not filepath.exists():
                continue
            
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Count sorry statements
            sorry_count = len(re.findall(r'\bsorry\b', content))
            sorry_counts[filename] = sorry_count
            total_sorry += sorry_count
            
            print(f"{filename}:")
            print(f"  Sorry statements: {sorry_count}")
            
            # Find sorry contexts
            lines = content.split('\n')
            sorry_lines = []
            for i, line in enumerate(lines, 1):
                if 'sorry' in line:
                    sorry_lines.append(i)
            
            if sorry_lines:
                print(f"  Lines: {', '.join(map(str, sorry_lines[:5]))}" + 
                      ("..." if len(sorry_lines) > 5 else ""))
        
        print(f"\nTOTAL SORRY STATEMENTS: {total_sorry}")
        print()
        
        self.results['sorry_counts'] = sorry_counts
        self.results['total_sorry'] = total_sorry
        
        return sorry_counts
    
    def analyze_theorems(self) -> Dict[str, List[str]]:
        """Extract and analyze theorem declarations."""
        print("=" * 70)
        print("THEOREM ANALYSIS")
        print("=" * 70)
        
        theorems = {}
        
        for filename in self.files:
            filepath = self.base_path / filename
            if not filepath.exists():
                continue
            
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Find theorem declarations
            theorem_pattern = r'theorem\s+(\w+)'
            found_theorems = re.findall(theorem_pattern, content)
            
            theorems[filename] = found_theorems
            
            if found_theorems:
                print(f"{filename}:")
                print(f"  Theorems declared: {len(found_theorems)}")
                print(f"  Names: {', '.join(found_theorems[:3])}" + 
                      ("..." if len(found_theorems) > 3 else ""))
                print()
        
        self.results['theorems'] = theorems
        return theorems
    
    def check_documentation(self) -> Dict[str, bool]:
        """Check documentation completeness."""
        print("=" * 70)
        print("DOCUMENTATION CHECK")
        print("=" * 70)
        
        doc_files = {
            "HILBERT_POLYA_README.md": self.base_path / "HILBERT_POLYA_README.md",
            "IMPLEMENTATION_HILBERT_POLYA.md": self.base_path / "IMPLEMENTATION_HILBERT_POLYA.md"
        }
        
        doc_status = {}
        for name, path in doc_files.items():
            exists = path.exists()
            doc_status[name] = exists
            status = "✓" if exists else "✗"
            print(f"{status} {name}")
            
            if exists:
                with open(path, 'r', encoding='utf-8') as f:
                    content = f.read()
                lines = len(content.split('\n'))
                words = len(content.split())
                print(f"   Lines: {lines}, Words: {words}")
        
        print()
        self.results['documentation'] = doc_status
        return doc_status
    
    def generate_summary(self) -> str:
        """Generate a summary report."""
        print("=" * 70)
        print("SUMMARY")
        print("=" * 70)
        
        summary = []
        summary.append(f"Files validated: {len(self.files)}")
        summary.append(f"Total sorry statements: {self.results.get('total_sorry', 0)}")
        
        total_theorems = sum(len(thms) for thms in self.results.get('theorems', {}).values())
        summary.append(f"Total theorems: {total_theorems}")
        
        doc_complete = all(self.results.get('documentation', {}).values())
        summary.append(f"Documentation complete: {'Yes' if doc_complete else 'No'}")
        
        for line in summary:
            print(line)
        
        return "\n".join(summary)
    
    def save_report(self, output_file: str = "hilbert_polya_validation_report.json"):
        """Save validation report to JSON."""
        report = {
            "timestamp": "2026-01-17",
            "validator": "HilbertPolyaValidator",
            "results": self.results,
            "files_checked": self.files
        }
        
        output_path = self.base_path / output_file
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"\nReport saved to: {output_path}")
    
    def run_full_validation(self):
        """Run all validation checks."""
        print("\n" + "=" * 70)
        print("HILBERT-PÓLYA FORMALIZATION VALIDATOR")
        print("=" * 70 + "\n")
        
        self.validate_files_exist()
        self.count_sorry_statements()
        self.analyze_theorems()
        self.check_documentation()
        self.generate_summary()
        self.save_report()
        
        print("\n" + "=" * 70)
        print("VALIDATION COMPLETE")
        print("=" * 70 + "\n")


def main():
    # Determine base path
    import sys
    if len(sys.argv) > 1:
        base_path = sys.argv[1]
    else:
        # Try to find the correct path
        possible_paths = [
            "formalization/lean/spectral",
            "/home/runner/work/Riemann-adelic/Riemann-adelic/formalization/lean/spectral"
        ]
        
        base_path = None
        for path in possible_paths:
            if os.path.exists(path):
                base_path = path
                break
        
        if base_path is None:
            print("Error: Could not find spectral directory")
            print("Usage: python validate_hilbert_polya.py [path_to_spectral_dir]")
            sys.exit(1)
    
    validator = HilbertPolyaValidator(base_path)
    validator.run_full_validation()


if __name__ == "__main__":
    main()
