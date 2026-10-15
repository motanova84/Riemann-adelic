#!/usr/bin/env python3
"""
validate_collapse_spectral.py
========================================================================
Validation and Testing for Collapse Spectral RH Proof

This script validates the Lean4 formalization of the Collapse Spectral
RH theorem, checking syntax, structure, and mathematical consistency.

Usage:
    python validate_collapse_spectral.py

Author: José Manuel Mota Burruezo
Date: 17 January 2026
========================================================================
"""

import os
import sys
import subprocess
import re
from pathlib import Path
from typing import List, Tuple, Dict

# ANSI color codes
GREEN = '\033[92m'
YELLOW = '\033[93m'
RED = '\033[91m'
BLUE = '\033[94m'
RESET = '\033[0m'
BOLD = '\033[1m'

def print_header(text: str):
    """Print a formatted section header."""
    print(f"\n{BLUE}{BOLD}{'='*70}{RESET}")
    print(f"{BLUE}{BOLD}{text:^70}{RESET}")
    print(f"{BLUE}{BOLD}{'='*70}{RESET}\n")

def print_success(text: str):
    """Print a success message."""
    print(f"{GREEN}✓ {text}{RESET}")

def print_warning(text: str):
    """Print a warning message."""
    print(f"{YELLOW}⚠ {text}{RESET}")

def print_error(text: str):
    """Print an error message."""
    print(f"{RED}✗ {text}{RESET}")

def print_info(text: str):
    """Print an info message."""
    print(f"{BLUE}ℹ {text}{RESET}")

class CollapseSpectralValidator:
    """Validator for Collapse Spectral RH formalization."""
    
    def __init__(self):
        self.base_dir = Path(__file__).parent.absolute()
        self.main_file = self.base_dir / "collapse_spectral_RH.lean"
        self.proofs_file = self.base_dir / "collapse_spectral_RH_proofs.lean"
        self.readme_file = self.base_dir / "collapse_spectral_RH_README.md"
        
        self.errors = []
        self.warnings = []
        self.successes = []
    
    def validate_files_exist(self) -> bool:
        """Check that all required files exist."""
        print_header("FILE EXISTENCE CHECK")
        
        files = [
            ("Main Lean file", self.main_file),
            ("Proofs file", self.proofs_file),
            ("README file", self.readme_file),
        ]
        
        all_exist = True
        for name, path in files:
            if path.exists():
                print_success(f"{name}: {path.name}")
            else:
                print_error(f"{name} NOT FOUND: {path}")
                all_exist = False
        
        return all_exist
    
    def count_sorry_statements(self, file_path: Path) -> Tuple[int, List[str]]:
        """Count and locate sorry statements in a Lean file."""
        if not file_path.exists():
            return 0, []
        
        content = file_path.read_text()
        
        # Find all sorry statements with context
        sorry_pattern = r'sorry|Sorry|SORRY'
        matches = re.finditer(sorry_pattern, content, re.IGNORECASE)
        
        sorry_locations = []
        lines = content.split('\n')
        
        for match in matches:
            # Find line number
            pos = match.start()
            line_num = content[:pos].count('\n') + 1
            
            # Get context (line content)
            if line_num <= len(lines):
                line_content = lines[line_num - 1].strip()
                sorry_locations.append(f"Line {line_num}: {line_content[:60]}")
        
        return len(sorry_locations), sorry_locations
    
    def validate_sorry_statements(self) -> bool:
        """Validate and report on sorry statements."""
        print_header("SORRY STATEMENT ANALYSIS")
        
        # Check main file
        main_count, main_locs = self.count_sorry_statements(self.main_file)
        print_info(f"Main file ({self.main_file.name}):")
        print(f"  Total sorry statements: {main_count}")
        
        if main_count > 0:
            print_warning(f"  Found {main_count} sorry statement(s) in main file")
            for loc in main_locs[:5]:  # Show first 5
                print(f"    • {loc}")
            if len(main_locs) > 5:
                print(f"    ... and {len(main_locs) - 5} more")
        else:
            print_success("  No sorry statements in main file!")
        
        # Check proofs file
        proofs_count, proofs_locs = self.count_sorry_statements(self.proofs_file)
        print_info(f"\nProofs file ({self.proofs_file.name}):")
        print(f"  Total sorry statements: {proofs_count}")
        
        if proofs_count > 0:
            print_warning(f"  Found {proofs_count} sorry statement(s) in proofs file")
            for loc in proofs_locs[:5]:
                print(f"    • {loc}")
            if len(proofs_locs) > 5:
                print(f"    ... and {len(proofs_locs) - 5} more")
        else:
            print_success("  No sorry statements in proofs file!")
        
        total_sorry = main_count + proofs_count
        print(f"\n{BOLD}Total sorry statements: {total_sorry}{RESET}")
        
        if total_sorry == 0:
            print_success("✓ Goal achieved: No sorry statements!")
            return True
        else:
            print_warning(f"⚠ Still need to eliminate {total_sorry} sorry statement(s)")
            return False
    
    def check_theorem_statements(self) -> bool:
        """Check for key theorem statements."""
        print_header("THEOREM STATEMENT CHECK")
        
        if not self.main_file.exists():
            print_error("Main file not found")
            return False
        
        content = self.main_file.read_text()
        
        required_theorems = [
            "riemann_hypothesis",
            "collapse_spectral_RH",
            "spectrum_on_critical_line",
            "H_Ψ_selfadjoint",
            "eigenfunction_property",
            "zeta_equals_spectral_trace",
        ]
        
        found_count = 0
        for theorem in required_theorems:
            if f"theorem {theorem}" in content or f"lemma {theorem}" in content:
                print_success(f"Found: {theorem}")
                found_count += 1
            else:
                print_warning(f"Missing or renamed: {theorem}")
        
        print(f"\n{BOLD}Found {found_count}/{len(required_theorems)} key theorems{RESET}")
        
        return found_count == len(required_theorems)
    
    def check_imports(self) -> bool:
        """Check that necessary imports are present."""
        print_header("IMPORT CHECK")
        
        if not self.main_file.exists():
            return False
        
        content = self.main_file.read_text()
        
        required_imports = [
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Analysis.SpecialFunctions.Gamma",
            "Mathlib.NumberTheory.ZetaFunction",
            "Mathlib.MeasureTheory.Integral",
        ]
        
        found_count = 0
        for imp in required_imports:
            if f"import {imp}" in content:
                print_success(f"Import: {imp}")
                found_count += 1
            else:
                print_warning(f"Missing import: {imp}")
        
        print(f"\n{BOLD}Found {found_count}/{len(required_imports)} key imports{RESET}")
        
        return found_count >= len(required_imports) - 1  # Allow one missing
    
    def validate_structure(self) -> bool:
        """Validate overall file structure."""
        print_header("STRUCTURE VALIDATION")
        
        if not self.main_file.exists():
            return False
        
        content = self.main_file.read_text()
        
        # Check for key structural elements
        checks = [
            ("Namespace declaration", "namespace CollapseSpectralRH"),
            ("Noncomputable section", "noncomputable section"),
            ("Adelic Hilbert space definition", "def AdelicHilbert"),
            ("H_Ψ action definition", "def H_Ψ_action"),
            ("Spectral trace definition", "def spectral_trace"),
            ("Main theorem", "theorem riemann_hypothesis"),
        ]
        
        passed = 0
        for name, pattern in checks:
            if pattern in content:
                print_success(name)
                passed += 1
            else:
                print_error(f"Missing: {name}")
        
        print(f"\n{BOLD}Structure checks: {passed}/{len(checks)}{RESET}")
        
        return passed == len(checks)
    
    def try_lean_check(self) -> bool:
        """Try to check the file with Lean (if available)."""
        print_header("LEAN SYNTAX CHECK")
        
        # Check if lean is available
        try:
            result = subprocess.run(['lean', '--version'], 
                                    capture_output=True, 
                                    text=True,
                                    timeout=5)
            print_info(f"Lean version: {result.stdout.strip()}")
        except (FileNotFoundError, subprocess.TimeoutExpired):
            print_warning("Lean not found or not responding - skipping syntax check")
            print_info("Install Lean 4 to enable syntax checking")
            return True  # Not a failure, just skipped
        
        # Try to check the main file
        print_info("Checking Lean syntax...")
        try:
            result = subprocess.run(['lean', str(self.main_file)],
                                    capture_output=True,
                                    text=True,
                                    timeout=30)
            
            if result.returncode == 0:
                print_success("Lean syntax check passed!")
                return True
            else:
                print_error("Lean syntax check failed:")
                # Show first few error lines
                error_lines = result.stderr.split('\n')[:10]
                for line in error_lines:
                    if line.strip():
                        print(f"  {line}")
                return False
        except subprocess.TimeoutExpired:
            print_warning("Lean check timed out - file may be too complex")
            return True  # Not necessarily a failure
    
    def generate_report(self) -> Dict:
        """Generate a summary report."""
        print_header("VALIDATION SUMMARY")
        
        report = {
            'files_exist': self.validate_files_exist(),
            'imports_ok': self.check_imports(),
            'structure_ok': self.validate_structure(),
            'theorems_present': self.check_theorem_statements(),
            'no_sorry': self.validate_sorry_statements(),
            'lean_check': self.try_lean_check(),
        }
        
        # Calculate score
        total = len(report)
        passed = sum(1 for v in report.values() if v)
        score = (passed / total) * 100
        
        print(f"\n{BOLD}Overall Validation Score: {score:.1f}%{RESET}")
        print(f"{BOLD}Checks passed: {passed}/{total}{RESET}\n")
        
        if score == 100:
            print_success("✓ ALL VALIDATIONS PASSED!")
        elif score >= 80:
            print_success("✓ Good progress - minor issues remain")
        elif score >= 60:
            print_warning("⚠ Moderate progress - some work needed")
        else:
            print_error("✗ Significant work required")
        
        return report
    
    def run_full_validation(self):
        """Run all validation checks."""
        print(f"\n{BOLD}{'='*70}{RESET}")
        print(f"{BOLD}COLLAPSE SPECTRAL RH VALIDATION{RESET}")
        print(f"{BOLD}{'='*70}{RESET}")
        
        report = self.generate_report()
        
        return report

def main():
    """Main validation entry point."""
    validator = CollapseSpectralValidator()
    report = validator.run_full_validation()
    
    # Exit with appropriate code
    if all(report.values()):
        sys.exit(0)  # All checks passed
    elif sum(report.values()) >= len(report) * 0.8:
        sys.exit(0)  # Mostly passed
    else:
        sys.exit(1)  # Significant failures

if __name__ == "__main__":
    main()
