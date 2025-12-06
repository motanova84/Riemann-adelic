#!/usr/bin/env python3
"""
QCAL Comprehensive Test Runner with Logging
===========================================

Run all tests and validations with comprehensive execution logs.
Creates detailed timestamped logs for every test and proof validation.

Usage:
    python run_all_tests_with_logs.py [options]

Options:
    --pytest-only      Run only pytest tests
    --validation-only  Run only validation scripts
    --quick           Run quick subset of tests
    --full            Run complete test suite (default)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import argparse
import subprocess
import sys
from pathlib import Path
from datetime import datetime
import json
from typing import List, Dict, Any
import os


class ComprehensiveTestRunner:
    """Run all tests with comprehensive logging."""
    
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.log_dir = project_root / "logs" / "validation"
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        self.timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.summary_file = self.log_dir / f"test_run_summary_{self.timestamp}.json"
        
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "test_suites": [],
            "summary": {
                "total_suites": 0,
                "passed_suites": 0,
                "failed_suites": 0
            }
        }
    
    def run_pytest_tests(self) -> Dict[str, Any]:
        """Run pytest tests with comprehensive logging."""
        print("\n" + "=" * 80)
        print("🧪 RUNNING PYTEST TEST SUITE")
        print("=" * 80)
        
        log_file = self.log_dir / f"pytest_run_{self.timestamp}.log"
        
        cmd = [
            sys.executable, "-m", "pytest",
            "tests/",
            "-v",
            "--tb=short",
            f"--log-file={log_file}",
            "--log-file-level=DEBUG",
            "--capture=no"
        ]
        
        print(f"📝 Pytest log: {log_file}")
        print(f"Running: {' '.join(cmd)}\n")
        
        result = subprocess.run(
            cmd,
            cwd=self.project_root,
            capture_output=True,
            text=True
        )
        
        # Also save stdout/stderr
        output_file = self.log_dir / f"pytest_output_{self.timestamp}.txt"
        with open(output_file, 'w') as f:
            f.write("STDOUT:\n")
            f.write(result.stdout)
            f.write("\n\nSTDERR:\n")
            f.write(result.stderr)
        
        suite_result = {
            "name": "pytest_tests",
            "log_file": str(log_file),
            "output_file": str(output_file),
            "return_code": result.returncode,
            "status": "passed" if result.returncode == 0 else "failed",
            "timestamp": datetime.now().isoformat()
        }
        
        if result.returncode == 0:
            print("✅ Pytest tests PASSED")
        else:
            print(f"❌ Pytest tests FAILED (return code: {result.returncode})")
        
        return suite_result
    
    def run_validation_script(self, script_path: Path) -> Dict[str, Any]:
        """Run a validation script with logging."""
        script_name = script_path.stem
        
        print(f"\n{'=' * 80}")
        print(f"🔍 RUNNING: {script_name}")
        print(f"{'=' * 80}")
        
        log_file = self.log_dir / f"{script_name}_{self.timestamp}.log"
        
        cmd = [sys.executable, str(script_path)]
        
        print(f"📝 Log: {log_file}")
        
        result = subprocess.run(
            cmd,
            cwd=self.project_root,
            capture_output=True,
            text=True
        )
        
        # Save output to log
        with open(log_file, 'w') as f:
            f.write(f"Validation Script: {script_name}\n")
            f.write(f"Timestamp: {datetime.now().isoformat()}\n")
            f.write("=" * 80 + "\n\n")
            f.write("STDOUT:\n")
            f.write(result.stdout)
            f.write("\n\nSTDERR:\n")
            f.write(result.stderr)
            f.write("\n\n" + "=" * 80 + "\n")
            f.write(f"Return Code: {result.returncode}\n")
        
        suite_result = {
            "name": script_name,
            "log_file": str(log_file),
            "return_code": result.returncode,
            "status": "passed" if result.returncode == 0 else "failed",
            "timestamp": datetime.now().isoformat()
        }
        
        if result.returncode == 0:
            print(f"✅ {script_name} PASSED")
        else:
            print(f"❌ {script_name} FAILED (return code: {result.returncode})")
        
        return suite_result
    
    def get_validation_scripts(self, quick: bool = False) -> List[Path]:
        """Get list of validation scripts to run."""
        all_scripts = [
            "validate_v5_coronacion.py",
            "validate_explicit_formula.py",
            "validate_critical_line.py",
            "validate_hilbert_polya.py",
            "validate_spectral_self_adjoint.py",
            "validate_h_psi_self_adjoint.py",
        ]
        
        quick_scripts = [
            "validate_v5_coronacion.py",
            "validate_critical_line.py",
        ]
        
        script_list = quick_scripts if quick else all_scripts
        
        scripts = []
        for script_name in script_list:
            script_path = self.project_root / script_name
            if script_path.exists():
                scripts.append(script_path)
        
        return scripts
    
    def run_all(self, pytest_only: bool = False, validation_only: bool = False, 
                quick: bool = False):
        """Run all tests and validations."""
        print("\n" + "=" * 80)
        print("🚀 QCAL COMPREHENSIVE TEST RUNNER")
        print("=" * 80)
        print(f"Timestamp: {datetime.now().isoformat()}")
        print(f"Log directory: {self.log_dir}")
        print("=" * 80)
        
        # Run pytest tests
        if not validation_only:
            suite_result = self.run_pytest_tests()
            self.results["test_suites"].append(suite_result)
            self.results["summary"]["total_suites"] += 1
            if suite_result["status"] == "passed":
                self.results["summary"]["passed_suites"] += 1
            else:
                self.results["summary"]["failed_suites"] += 1
        
        # Run validation scripts
        if not pytest_only:
            validation_scripts = self.get_validation_scripts(quick=quick)
            
            for script in validation_scripts:
                suite_result = self.run_validation_script(script)
                self.results["test_suites"].append(suite_result)
                self.results["summary"]["total_suites"] += 1
                if suite_result["status"] == "passed":
                    self.results["summary"]["passed_suites"] += 1
                else:
                    self.results["summary"]["failed_suites"] += 1
        
        # Save summary
        self.save_summary()
        self.print_final_summary()
    
    def save_summary(self):
        """Save test run summary to JSON."""
        with open(self.summary_file, 'w') as f:
            json.dump(self.results, f, indent=2)
        
        print(f"\n📊 Test run summary saved to: {self.summary_file}")
    
    def print_final_summary(self):
        """Print final summary."""
        print("\n" + "=" * 80)
        print("📊 FINAL SUMMARY")
        print("=" * 80)
        print(f"Total test suites: {self.results['summary']['total_suites']}")
        print(f"✅ Passed: {self.results['summary']['passed_suites']}")
        print(f"❌ Failed: {self.results['summary']['failed_suites']}")
        print("=" * 80)
        
        print("\n📝 Individual logs:")
        for suite in self.results["test_suites"]:
            status_icon = "✅" if suite["status"] == "passed" else "❌"
            print(f"  {status_icon} {suite['name']}: {suite.get('log_file', 'N/A')}")
        
        print("\n" + "=" * 80)
        if self.results['summary']['failed_suites'] == 0:
            print("🏆 ALL TESTS PASSED!")
        else:
            print(f"⚠️  {self.results['summary']['failed_suites']} test suite(s) failed")
        print("=" * 80)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Run all QCAL tests with comprehensive logging',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--pytest-only', action='store_true',
                        help='Run only pytest tests')
    parser.add_argument('--validation-only', action='store_true',
                        help='Run only validation scripts')
    parser.add_argument('--quick', action='store_true',
                        help='Run quick subset of tests')
    parser.add_argument('--full', action='store_true',
                        help='Run complete test suite (default)')
    
    args = parser.parse_args()
    
    # Determine project root
    project_root = Path(__file__).parent
    
    # Create runner
    runner = ComprehensiveTestRunner(project_root)
    
    # Run tests
    runner.run_all(
        pytest_only=args.pytest_only,
        validation_only=args.validation_only,
        quick=args.quick
    )
    
    # Exit with appropriate code
    if runner.results['summary']['failed_suites'] == 0:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == '__main__':
    main()
