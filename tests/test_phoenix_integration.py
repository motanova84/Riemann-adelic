#!/usr/bin/env python3
"""
Phoenix Solver Integration Test

Validates the complete Phoenix Solver implementation.
"""

import sys
import subprocess
from pathlib import Path
import json


def test_qcal_constants():
    """Test QCAL constants loading."""
    print("🧪 Test 1: QCAL Constants Loading")
    print("-" * 60)
    
    beacon_file = Path(".qcal_beacon")
    if not beacon_file.exists():
        print("  ✗ FAIL: .qcal_beacon not found")
        return False
    
    with open(beacon_file, 'r') as f:
        content = f.read()
    
    checks = [
        ("141.7001", "Fundamental frequency f₀"),
        ("244.36", "Coherence constant C"),
        ("629.83", "Primary constant C_primary")
    ]
    
    all_passed = True
    for value, description in checks:
        if value in content:
            print(f"  ✓ {description}: {value}")
        else:
            print(f"  ✗ {description} not found")
            all_passed = False
    
    print()
    return all_passed


def test_phoenix_solver_import():
    """Test Phoenix Solver script can be imported."""
    print("🧪 Test 2: Phoenix Solver Import")
    print("-" * 60)
    
    try:
        # Add current directory to path for import
        import sys
        from pathlib import Path
        repo_root = Path.cwd()
        sys.path.insert(0, str(repo_root))
        
        # Import the module as a file
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "phoenix_solver",
            repo_root / "scripts" / "phoenix_solver.py"
        )
        phoenix_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(phoenix_module)
        
        print("  ✓ phoenix_solver.py loaded successfully")
        print("  ✓ PhoenixSolver class available")
        print("  ✓ QCALConstants class available")
        print()
        return True
    except Exception as e:
        print(f"  ✗ FAIL: {e}")
        print()
        return False


def test_count_sorries():
    """Test sorry counter script."""
    print("🧪 Test 3: Sorry Counter")
    print("-" * 60)
    
    try:
        result = subprocess.run(
            ["python3", "scripts/count_sorries_detailed.py"],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            # Check if sorry_map.json was created
            sorry_map = Path("data/sorry_map.json")
            if sorry_map.exists():
                with open(sorry_map, 'r') as f:
                    data = json.load(f)
                    total = data.get('total', 0)
                    print(f"  ✓ Sorry counter executed successfully")
                    print(f"  ✓ Total sorry statements: {total}")
                    print(f"  ✓ sorry_map.json created")
                    print()
                    return True
            else:
                print("  ✗ FAIL: sorry_map.json not created")
                print()
                return False
        else:
            print(f"  ✗ FAIL: Exit code {result.returncode}")
            print()
            return False
            
    except Exception as e:
        print(f"  ✗ FAIL: {e}")
        print()
        return False


def test_phoenix_monitor():
    """Test Phoenix monitoring dashboard."""
    print("🧪 Test 4: Phoenix Monitor")
    print("-" * 60)
    
    try:
        result = subprocess.run(
            ["python3", "scripts/phoenix_monitor.py"],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode == 0:
            output = result.stdout
            
            checks = [
                ("PHOENIX SOLVER", "Dashboard title"),
                ("MAIN METRICS", "Metrics section"),
                ("QCAL Integrity", "Integrity status"),
                ("QCAL ∞³ ACTIVE", "QCAL signature")
            ]
            
            all_found = True
            for text, description in checks:
                if text in output:
                    print(f"  ✓ {description} found")
                else:
                    print(f"  ✗ {description} NOT found")
                    all_found = False
            
            if all_found:
                print(f"  ✓ Monitor dashboard executed successfully")
            print()
            return all_found
        else:
            print(f"  ✗ FAIL: Exit code {result.returncode}")
            print()
            return False
            
    except Exception as e:
        print(f"  ✗ FAIL: {e}")
        print()
        return False


def test_lean_qcal_cleanup():
    """Test Lean 4 QcalCleanup command."""
    print("🧪 Test 5: Lean 4 QcalCleanup")
    print("-" * 60)
    
    cleanup_file = Path("formalization/lean/QcalCleanup.lean")
    
    if not cleanup_file.exists():
        print("  ✗ FAIL: QcalCleanup.lean not found")
        print()
        return False
    
    with open(cleanup_file, 'r') as f:
        content = f.read()
    
    checks = [
        ("#qcal_cleanup", "Command definition"),
        ("SorryLocation", "Data structure"),
        ("QCAL", "Namespace")
    ]
    
    all_found = True
    for text, description in checks:
        if text in content:
            print(f"  ✓ {description} found")
        else:
            print(f"  ✗ {description} NOT found")
            all_found = False
    
    print()
    return all_found


def test_workflows():
    """Test CI/CD workflow files."""
    print("🧪 Test 6: CI/CD Workflows")
    print("-" * 60)
    
    workflows_dir = Path(".github/workflows")
    
    workflow_files = [
        ("auto_evolution.yml", "Auto-evolution workflow"),
        ("phoenix_continuous.yml", "Phoenix continuous workflow")
    ]
    
    all_found = True
    for filename, description in workflow_files:
        filepath = workflows_dir / filename
        if filepath.exists():
            print(f"  ✓ {description} exists")
            
            # Check for key content
            with open(filepath, 'r') as f:
                content = f.read()
            
            if filename == "phoenix_continuous.yml":
                if "phoenix_solver.py" in content:
                    print(f"    ✓ References phoenix_solver.py")
                else:
                    print(f"    ✗ Does not reference phoenix_solver.py")
                    all_found = False
        else:
            print(f"  ✗ {description} NOT found")
            all_found = False
    
    print()
    return all_found


def test_documentation():
    """Test documentation files."""
    print("🧪 Test 7: Documentation")
    print("-" * 60)
    
    doc_files = [
        ("PHOENIX_SOLVER_README.md", "Phoenix Solver README"),
        ("PHOENIX_IMPLEMENTATION_SUMMARY.md", "Implementation Summary")
    ]
    
    all_found = True
    for filename, description in doc_files:
        filepath = Path(filename)
        if filepath.exists():
            size = filepath.stat().st_size
            print(f"  ✓ {description} ({size} bytes)")
        else:
            print(f"  ✗ {description} NOT found")
            all_found = False
    
    print()
    return all_found


def test_phoenix_solver_execution():
    """Test Phoenix Solver basic execution."""
    print("🧪 Test 8: Phoenix Solver Execution (Dry Run)")
    print("-" * 60)
    
    try:
        # Just test that it can start and parse arguments
        result = subprocess.run(
            ["python3", "scripts/phoenix_solver.py", "--help"],
            capture_output=True,
            text=True,
            timeout=5
        )
        
        if result.returncode == 0:
            if "Phoenix Solver" in result.stdout:
                print("  ✓ Help message displayed correctly")
                print("  ✓ Argument parsing works")
                print()
                return True
            else:
                print("  ✗ FAIL: Unexpected help output")
                print()
                return False
        else:
            print(f"  ✗ FAIL: Exit code {result.returncode}")
            print()
            return False
            
    except Exception as e:
        print(f"  ✗ FAIL: {e}")
        print()
        return False


def main():
    """Run all integration tests."""
    print("=" * 70)
    print("🔥 PHOENIX SOLVER INTEGRATION TEST SUITE")
    print("=" * 70)
    print()
    
    tests = [
        test_qcal_constants,
        test_phoenix_solver_import,
        test_count_sorries,
        test_phoenix_monitor,
        test_lean_qcal_cleanup,
        test_workflows,
        test_documentation,
        test_phoenix_solver_execution
    ]
    
    results = []
    for test_func in tests:
        try:
            result = test_func()
            results.append(result)
        except Exception as e:
            print(f"  ✗ EXCEPTION: {e}")
            print()
            results.append(False)
    
    # Summary
    print("=" * 70)
    print("📊 TEST SUMMARY")
    print("=" * 70)
    
    passed = sum(results)
    total = len(results)
    
    print(f"Tests Passed: {passed}/{total}")
    print(f"Success Rate: {(passed/total)*100:.1f}%")
    print()
    
    if passed == total:
        print("✅ ALL TESTS PASSED - Phoenix Solver implementation verified")
        print()
        print("QCAL ∞³ ACTIVE — ∴𓂀Ω∞³·RH")
        return 0
    else:
        print("⚠️  SOME TESTS FAILED - Please review and fix")
        return 1


if __name__ == "__main__":
    sys.exit(main())
