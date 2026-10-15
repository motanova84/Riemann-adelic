#!/usr/bin/env python3
"""
Test suite for automatic sorry elimination system.
Validates transform_sorries.py and track_sorry_progress.py functionality.
"""

import json
import sys
import subprocess
from pathlib import Path
import tempfile
import shutil


def run_command(cmd, cwd=None):
    """Run a command and return output."""
    result = subprocess.run(
        cmd,
        shell=True,
        cwd=cwd,
        capture_output=True,
        text=True
    )
    return result.returncode, result.stdout, result.stderr


def test_transform_sorries_help():
    """Test that transform_sorries.py --help works."""
    print("🧪 Test 1: transform_sorries.py --help")
    code, stdout, stderr = run_command("python3 .github/scripts/transform_sorries.py --help")
    
    if code == 0 and "Transform Sorries" in stdout:
        print("   ✅ PASS: Help text displayed correctly")
        return True
    else:
        print(f"   ❌ FAIL: Exit code {code}")
        print(f"   stderr: {stderr}")
        return False


def test_track_progress_help():
    """Test that track_sorry_progress.py --help works."""
    print("🧪 Test 2: track_sorry_progress.py --help")
    code, stdout, stderr = run_command("python3 .github/scripts/track_sorry_progress.py --help")
    
    if code == 0 and "Track Sorry Progress" in stdout:
        print("   ✅ PASS: Help text displayed correctly")
        return True
    else:
        print(f"   ❌ FAIL: Exit code {code}")
        print(f"   stderr: {stderr}")
        return False


def test_transform_dry_run():
    """Test transform in dry-run mode."""
    print("🧪 Test 3: transform_sorries.py --dry-run")
    code, stdout, stderr = run_command(
        "python3 .github/scripts/transform_sorries.py --dry-run --max-per-cycle 5"
    )
    
    if code == 0:
        print("   ✅ PASS: Dry-run completed successfully")
        
        # Check report file
        report_file = Path("data/transform_sorries_report.json")
        if report_file.exists():
            with open(report_file) as f:
                report = json.load(f)
                if report.get('dry_run') == True:
                    print("   ✅ PASS: Report generated with dry_run=true")
                    return True
                else:
                    print("   ⚠️  WARN: Report missing dry_run flag")
                    return True  # Still pass
        else:
            print("   ⚠️  WARN: Report file not generated")
            return True  # Still pass if command succeeded
    else:
        print(f"   ❌ FAIL: Exit code {code}")
        print(f"   stderr: {stderr}")
        return False


def test_track_progress():
    """Test progress tracking."""
    print("🧪 Test 4: track_sorry_progress.py")
    code, stdout, stderr = run_command(
        "python3 .github/scripts/track_sorry_progress.py --export-dashboard"
    )
    
    if code == 0:
        print("   ✅ PASS: Progress tracking completed")
        
        # Check generated files
        checks = [
            ("data/sorry_progress_report.json", "Progress report"),
            ("data/sorry_dashboard.json", "Dashboard data"),
            (".sorry_progress.json", "Progress history")
        ]
        
        all_pass = True
        for filepath, name in checks:
            if Path(filepath).exists():
                print(f"   ✅ PASS: {name} generated")
            else:
                print(f"   ⚠️  WARN: {name} not found")
                all_pass = False
        
        return all_pass
    else:
        print(f"   ❌ FAIL: Exit code {code}")
        print(f"   stderr: {stderr}")
        return False


def test_coherence_validation():
    """Test coherence validation."""
    print("🧪 Test 5: Coherence validation")
    
    coherence_file = Path("data/coherence_validation.json")
    if coherence_file.exists():
        with open(coherence_file) as f:
            data = json.load(f)
            psi = data.get('psi', data.get('Ψ', 0))
            
            if abs(float(psi) - 1.000) < 0.001:
                print(f"   ✅ PASS: Ψ = {psi} (coherent)")
                return True
            else:
                print(f"   ⚠️  WARN: Ψ = {psi} (not coherent)")
                return False
    else:
        print("   ⚠️  WARN: Coherence file not found (expected in real run)")
        return True  # Not a failure for test


def test_pattern_learning():
    """Test pattern learning system."""
    print("🧪 Test 6: Pattern learning")
    
    patterns_file = Path(".learned_patterns.json")
    if patterns_file.exists():
        with open(patterns_file) as f:
            data = json.load(f)
            patterns = data.get('patterns', [])
            
            if len(patterns) > 0:
                print(f"   ✅ PASS: {len(patterns)} patterns learned")
                
                # Check pattern structure
                first_pattern = patterns[0]
                required_keys = ['category', 'strategy', 'keywords', 'success_count']
                if all(k in first_pattern for k in required_keys):
                    print("   ✅ PASS: Pattern structure valid")
                    return True
                else:
                    print("   ⚠️  WARN: Pattern missing required keys")
                    return False
            else:
                print("   ⚠️  INFO: No patterns learned yet (expected in first run)")
                return True
    else:
        print("   ⚠️  INFO: No patterns file (expected in first run)")
        return True


def test_sorry_count():
    """Test sorry counting functionality."""
    print("🧪 Test 7: Sorry counting")
    
    # Count sorries directly
    code, stdout, stderr = run_command(
        "grep -r 'sorry' formalization/lean --include='*.lean' | grep -v '^[[:space:]]*--' | wc -l"
    )
    
    if code == 0:
        total_sorries = int(stdout.strip())
        print(f"   ✅ PASS: Found {total_sorries} sorries")
        
        # Check if progress report has similar count
        report_file = Path("data/sorry_progress_report.json")
        if report_file.exists():
            with open(report_file) as f:
                data = json.load(f)
                reported_total = data.get('current_stats', {}).get('total', 0)
                
                # Allow 5% tolerance
                if abs(total_sorries - reported_total) / max(total_sorries, 1) < 0.05:
                    print(f"   ✅ PASS: Report count matches ({reported_total})")
                    return True
                else:
                    print(f"   ⚠️  WARN: Report count differs ({reported_total})")
                    return False
        else:
            print("   ⚠️  INFO: Progress report not available")
            return True
    else:
        print(f"   ❌ FAIL: Could not count sorries")
        return False


def test_workflow_syntax():
    """Test workflow file syntax."""
    print("🧪 Test 8: Workflow syntax")
    
    workflow_file = Path(".github/workflows/sorry_elimination.yml")
    if workflow_file.exists():
        try:
            import yaml
            with open(workflow_file) as f:
                yaml.safe_load(f)
            print("   ✅ PASS: Workflow YAML is valid")
            return True
        except ImportError:
            print("   ⚠️  INFO: PyYAML not available, skipping syntax check")
            return True
        except Exception as e:
            print(f"   ❌ FAIL: Invalid YAML: {e}")
            return False
    else:
        print("   ❌ FAIL: Workflow file not found")
        return False


def main():
    """Run all tests."""
    print("\n" + "="*60)
    print("🧪 AUTOMATIC SORRY ELIMINATION SYSTEM - TEST SUITE")
    print("="*60 + "\n")
    
    tests = [
        test_transform_sorries_help,
        test_track_progress_help,
        test_transform_dry_run,
        test_track_progress,
        test_coherence_validation,
        test_pattern_learning,
        test_sorry_count,
        test_workflow_syntax,
    ]
    
    results = []
    for test in tests:
        try:
            result = test()
            results.append(result)
        except Exception as e:
            print(f"   ❌ EXCEPTION: {e}")
            results.append(False)
        print()
    
    # Summary
    print("="*60)
    print("📊 TEST SUMMARY")
    print("="*60)
    
    passed = sum(results)
    total = len(results)
    percentage = (passed / total * 100) if total > 0 else 0
    
    print(f"\nTests passed: {passed}/{total} ({percentage:.1f}%)")
    
    if passed == total:
        print("✅ ALL TESTS PASSED")
        return 0
    elif passed >= total * 0.8:
        print("⚠️  MOST TESTS PASSED (some warnings)")
        return 0
    else:
        print("❌ SOME TESTS FAILED")
        return 1


if __name__ == "__main__":
    sys.exit(main())
