#!/usr/bin/env python3
"""
Test Suite for Lean 4.5.0 Setup Infrastructure
==============================================

Tests that all the setup infrastructure works correctly.
"""

__author__ = "José Manuel Mota Burruezo"
__date__ = "October 2025"

import os
import sys
import subprocess
from pathlib import Path

# Constants
CONTENT_PREVIEW_LENGTH = 50
VALIDATION_TIMEOUT = 60

def test_file_exists(file_path: Path, description: str) -> bool:
    """Test if a file exists."""
    if file_path.exists():
        print(f"✓ {description}: {file_path.name}")
        return True
    else:
        print(f"✗ {description}: {file_path.name} NOT FOUND")
        return False

def test_file_executable(file_path: Path, description: str) -> bool:
    """Test if a file is executable."""
    if file_path.exists() and os.access(file_path, os.X_OK):
        print(f"✓ {description} is executable")
        return True
    else:
        print(f"✗ {description} is NOT executable")
        return False

def test_file_content(file_path: Path, search_string: str, description: str) -> bool:
    """Test if a file contains specific content."""
    try:
        with open(file_path, 'r') as f:
            content = f.read()
        if search_string in content:
            preview = search_string[:CONTENT_PREVIEW_LENGTH]
            print(f"✓ {description}: contains '{preview}...'")
            return True
        else:
            preview = search_string[:CONTENT_PREVIEW_LENGTH]
            print(f"✗ {description}: missing '{preview}...'")
            return False
    except Exception as e:
        print(f"✗ {description}: Error reading file - {e}")
        return False

def test_validation_script_runs(script_path: Path) -> bool:
    """Test if validation script runs without errors."""
    try:
        result = subprocess.run(
            ['python3', str(script_path)],
            capture_output=True,
            text=True,
            timeout=VALIDATION_TIMEOUT
        )
        if result.returncode == 0:
            print(f"✓ {script_path.name} runs successfully")
            return True
        else:
            print(f"✗ {script_path.name} failed with code {result.returncode}")
            return False
    except subprocess.TimeoutExpired:
        print(f"✗ {script_path.name} timed out")
        return False
    except Exception as e:
        print(f"✗ {script_path.name} error: {e}")
        return False

def main():
    """Run all tests."""
    print("=" * 70)
    print("Testing Lean 4.5.0 Setup Infrastructure")
    print("=" * 70)
    print()
    
    repo_root = Path(__file__).parent
    lean_dir = repo_root / 'formalization' / 'lean'
    
    results = []
    
    # Test 1: lakefile.toml exists
    print("Test 1: lakefile.toml")
    results.append(test_file_exists(
        lean_dir / 'lakefile.toml',
        "lakefile.toml exists"
    ))
    results.append(test_file_content(
        lean_dir / 'lakefile.toml',
        'name = "riemann-adelic"',
        "lakefile.toml has correct package name"
    ))
    results.append(test_file_content(
        lean_dir / 'lakefile.toml',
        'version = "5.3"',
        "lakefile.toml has correct version"
    ))
    print()
    
    # Test 2: lakefile.lean updated
    print("Test 2: lakefile.lean")
    results.append(test_file_exists(
        lean_dir / 'lakefile.lean',
        "lakefile.lean exists"
    ))
    results.append(test_file_content(
        lean_dir / 'lakefile.lean',
        'package riemannAdelic',
        "lakefile.lean has correct package declaration"
    ))
    results.append(test_file_content(
        lean_dir / 'lakefile.lean',
        'lean_lib RiemannAdelic',
        "lakefile.lean has correct lib declaration"
    ))
    print()
    
    # Test 3: lean-toolchain
    print("Test 3: lean-toolchain")
    results.append(test_file_exists(
        lean_dir / 'lean-toolchain',
        "lean-toolchain exists"
    ))
    results.append(test_file_content(
        lean_dir / 'lean-toolchain',
        'leanprover/lean4:v4.5.0',
        "lean-toolchain specifies Lean 4.5.0"
    ))
    print()
    
    # Test 4: setup_lean.sh
    print("Test 4: setup_lean.sh")
    setup_script = repo_root / 'setup_lean.sh'
    results.append(test_file_exists(
        setup_script,
        "setup_lean.sh exists"
    ))
    results.append(test_file_executable(
        setup_script,
        "setup_lean.sh"
    ))
    results.append(test_file_content(
        setup_script,
        'elan toolchain install leanprover/lean4:v4.5.0',
        "setup_lean.sh installs correct version"
    ))
    print()
    
    # Test 5: validar_formalizacion_lean.py
    print("Test 5: validar_formalizacion_lean.py")
    validation_script = repo_root / 'validar_formalizacion_lean.py'
    results.append(test_file_exists(
        validation_script,
        "validar_formalizacion_lean.py exists"
    ))
    results.append(test_file_executable(
        validation_script,
        "validar_formalizacion_lean.py"
    ))
    results.append(test_file_content(
        validation_script,
        'def validar_estructura_proyecto',
        "validar_formalizacion_lean.py has validation function"
    ))
    print()
    
    # Test 6: LEAN_SETUP_GUIDE.md
    print("Test 6: LEAN_SETUP_GUIDE.md")
    guide = repo_root / 'LEAN_SETUP_GUIDE.md'
    results.append(test_file_exists(
        guide,
        "LEAN_SETUP_GUIDE.md exists"
    ))
    results.append(test_file_content(
        guide,
        './setup_lean.sh',
        "LEAN_SETUP_GUIDE.md references setup script"
    ))
    results.append(test_file_content(
        guide,
        'lakefile.toml',
        "LEAN_SETUP_GUIDE.md mentions lakefile.toml"
    ))
    print()
    
    # Test 7: LEAN_QUICKREF.md
    print("Test 7: LEAN_QUICKREF.md")
    quickref = repo_root / 'LEAN_QUICKREF.md'
    results.append(test_file_exists(
        quickref,
        "LEAN_QUICKREF.md exists"
    ))
    results.append(test_file_content(
        quickref,
        'lean --version',
        "LEAN_QUICKREF.md has version command"
    ))
    print()
    
    # Test 8: README.md updated
    print("Test 8: README.md")
    readme = repo_root / 'README.md'
    results.append(test_file_content(
        readme,
        'LEAN_SETUP_GUIDE.md',
        "README.md references LEAN_SETUP_GUIDE.md"
    ))
    results.append(test_file_content(
        readme,
        'validar_formalizacion_lean.py',
        "README.md references validation script"
    ))
    print()
    
    # Test 9: .gitignore has Lean artifacts
    print("Test 9: .gitignore")
    gitignore = repo_root / '.gitignore'
    results.append(test_file_content(
        gitignore,
        '.lake/',
        ".gitignore excludes .lake/"
    ))
    results.append(test_file_content(
        gitignore,
        '*.olean',
        ".gitignore excludes .olean files"
    ))
    print()
    
    # Test 10: Run validate_lean_formalization.py
    print("Test 10: Existing validation script")
    existing_validation = repo_root / 'validate_lean_formalization.py'
    if test_file_exists(existing_validation, "validate_lean_formalization.py exists"):
        results.append(test_validation_script_runs(existing_validation))
    print()
    
    # Summary
    print("=" * 70)
    print("Test Summary")
    print("=" * 70)
    
    total_tests = len(results)
    passed_tests = sum(results)
    failed_tests = total_tests - passed_tests
    
    print(f"\nTotal Tests: {total_tests}")
    print(f"Passed: {passed_tests}")
    print(f"Failed: {failed_tests}")
    
    if failed_tests == 0:
        print("\n✅ All tests passed! Lean setup infrastructure is complete.")
        return 0
    else:
        print(f"\n⚠️  {failed_tests} test(s) failed. Please review the output above.")
        return 1

if __name__ == '__main__':
    sys.exit(main())
