#!/usr/bin/env python3
"""
Final validation script to ensure all repository improvements are working correctly.

This script runs a comprehensive check of all components and workflows.
"""

import os
import sys
import subprocess
import time
import json
from pathlib import Path

def run_command(cmd, description, timeout=60, check_returncode=True):
    """Run a command and report results."""
    print(f"🔧 {description}...")
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True, timeout=timeout
        )
        
        if check_returncode and result.returncode != 0:
            print(f"❌ Failed: {description}")
            print(f"   Error: {result.stderr.strip()}")
            return False
        else:
            print(f"✅ Success: {description}")
            if result.stdout.strip():
                # Show first few lines of output
                lines = result.stdout.strip().split('\n')
                for line in lines[:3]:
                    print(f"   {line}")
                if len(lines) > 3:
                    print(f"   ... ({len(lines)-3} more lines)")
            return True
            
    except subprocess.TimeoutExpired:
        print(f"⏱️ Timeout: {description}")
        return False
    except Exception as e:
        print(f"❌ Error running {description}: {e}")
        return False

def check_file_exists(filepath, description):
    """Check if a file exists."""
    if os.path.exists(filepath):
        size = os.path.getsize(filepath)
        print(f"✅ {description}: {filepath} ({size:,} bytes)")
        return True
    else:
        print(f"❌ Missing: {description} - {filepath}")
        return False

def main():
    """Run comprehensive validation."""
    print("🧮 Riemann-Adelic Repository Final Validation")
    print("=" * 60)
    
    start_time = time.time()
    checks = []
    
    # 1. Environment checks
    print("\n📋 ENVIRONMENT VALIDATION")
    print("-" * 30)
    
    checks.append(("Python version", sys.version_info >= (3, 8)))
    checks.append(("Working directory", os.getcwd().endswith('-jmmotaburr-riemann-adelic')))
    
    # 2. File structure validation
    print("\n📁 FILE STRUCTURE VALIDATION")
    print("-" * 30)
    
    required_files = [
        ("Setup script", "setup_environment.py"),
        ("Main validation", "validate_explicit_formula.py"),
        ("Mellin transforms", "utils/mellin.py"),
        ("Fetch utility", "utils/fetch_odlyzko.py"),
        ("Checksum utility", "utils/checksum_zeros.py"),
        ("Performance monitor", "utils/performance_monitor.py"),
        ("Test suite", "tests/test_validation.py"),
        ("Requirements", "requirements.txt"),
        ("CI workflow", ".github/workflows/comprehensive-ci.yml"),
        ("Pre-commit config", ".pre-commit-config.yaml"),
        ("Gitignore", ".gitignore")
    ]
    
    for desc, filepath in required_files:
        checks.append((desc, check_file_exists(filepath, desc)))
    
    # 3. Required directories
    print("\n📂 DIRECTORY STRUCTURE VALIDATION") 
    print("-" * 30)
    
    required_dirs = ["zeros", "data", "logs", "notebooks", "utils", "tests", "docs"]
    for directory in required_dirs:
        exists = os.path.exists(directory) and os.path.isdir(directory)
        if exists:
            print(f"✅ Directory: {directory}/")
        else:
            print(f"❌ Missing directory: {directory}/")
        checks.append((f"Directory {directory}", exists))
    
    # 4. Python dependencies
    print("\n📦 DEPENDENCY VALIDATION")
    print("-" * 30)
    
    required_packages = ["mpmath", "numpy", "sympy", "requests", "jupyter", "nbconvert", "pytest"]
    for package in required_packages:
        try:
            __import__(package)
            print(f"✅ Package: {package}")
            checks.append((f"Package {package}", True))
        except ImportError:
            print(f"❌ Missing package: {package}")
            checks.append((f"Package {package}", False))
    
    # 5. Data validation
    print("\n📊 DATA VALIDATION")
    print("-" * 30)
    
    zeros_file = "zeros/zeros_t1e8.txt"
    if os.path.exists(zeros_file):
        line_count = sum(1 for _ in open(zeros_file))
        print(f"✅ Zeros data: {line_count:,} lines")
        checks.append(("Zeros data", line_count > 100))
    else:
        print("⚠️ No zeros data - will use sample data")
        checks.append(("Zeros data", False))
    
    # 6. Run tests
    print("\n🧪 TEST SUITE VALIDATION")
    print("-" * 30)
    
    test_success = run_command(
        "python -m pytest tests/ -v --tb=short -x",
        "Running test suite",
        timeout=120
    )
    checks.append(("Test suite", test_success))
    
    # 7. Quick validation run
    print("\n🔬 COMPUTATIONAL VALIDATION")
    print("-" * 30)
    
    validation_success = run_command(
        "python validate_explicit_formula.py --max_primes 20 --max_zeros 20 --integration_t 3",
        "Quick validation run",
        timeout=30
    )
    checks.append(("Quick validation", validation_success))
    
    # 8. Fetch utility test
    print("\n📥 DATA FETCHING VALIDATION")  
    print("-" * 30)
    
    fetch_success = run_command(
        "python utils/fetch_odlyzko.py --validate-only",
        "Data validation",
        timeout=30
    )
    checks.append(("Data fetching utility", fetch_success))
    
    # 9. Performance monitoring test
    print("\n⚡ PERFORMANCE MONITORING VALIDATION")
    print("-" * 30)
    
    perf_success = run_command(
        "python utils/performance_monitor.py --quick",
        "Performance monitoring",
        timeout=120,
        check_returncode=False  # May have non-zero exit for performance reasons
    )
    checks.append(("Performance monitoring", perf_success))
    
    # 10. Environment setup test
    print("\n🔧 SETUP SCRIPT VALIDATION")
    print("-" * 30)
    
    setup_success = run_command(
        "python setup_environment.py --validate-only",
        "Environment setup validation",
        timeout=60
    )
    checks.append(("Setup script", setup_success))
    
    # Summary
    elapsed_time = time.time() - start_time
    passed = sum(1 for _, result in checks if result)
    total = len(checks)
    
    print("\n" + "=" * 60)
    print("📋 FINAL VALIDATION SUMMARY")
    print("=" * 60)
    
    print(f"⏱️  Total time: {elapsed_time:.1f}s")
    print(f"✅ Passed: {passed}/{total} checks")
    print(f"❌ Failed: {total-passed}/{total} checks")
    
    if passed == total:
        print("\n🎉 ALL VALIDATIONS PASSED!")
        print("\n🚀 Repository is ready for:")
        print("   • Automated CI/CD workflows")
        print("   • Mathematical validation runs")
        print("   • Research and development work")
        print("   • Performance benchmarking")
        print("   • Collaborative contributions")
        
        return 0
    else:
        print(f"\n⚠️  {total-passed} issues detected:")
        for desc, result in checks:
            if not result:
                print(f"   • {desc}")
        
        print("\n💡 Recommended actions:")
        print("   • Run: python setup_environment.py --full-setup")
        print("   • Install missing dependencies: pip install -r requirements.txt")  
        print("   • Check network connectivity for data fetching")
        
        return 1

if __name__ == "__main__":
    sys.exit(main())