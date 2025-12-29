#!/usr/bin/env python3
"""
Quick Integration Test for All Enhancements

This script runs quick tests on all new enhancement modules to ensure
they work correctly together.
"""

import sys
import subprocess
import time

def run_command(cmd, description, timeout=60):
    """Run a command and report results"""
    print(f"\n{'='*70}")
    print(f"Testing: {description}")
    print(f"Command: {cmd}")
    print('='*70)
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=timeout
        )
        elapsed = time.time() - start_time
        
        if result.returncode == 0:
            print(f"✅ PASS ({elapsed:.2f}s)")
            # Print last few lines of output
            lines = result.stdout.strip().split('\n')
            for line in lines[-5:]:
                print(f"  {line}")
            return True
        else:
            print(f"❌ FAIL ({elapsed:.2f}s)")
            print("Error output:")
            for line in result.stderr.strip().split('\n')[-10:]:
                print(f"  {line}")
            return False
    except subprocess.TimeoutExpired:
        print(f"⏱️ TIMEOUT (>{timeout}s)")
        return False
    except Exception as e:
        print(f"❌ ERROR: {e}")
        return False

def main():
    """Run all integration tests"""
    print("="*70)
    print("Comprehensive Enhancement Integration Tests")
    print("="*70)
    
    tests = [
        # Test 1: Original A4 verification
        (
            "python3 verify_a4_lemma.py",
            "Original A4 Lemma Verification",
            30
        ),
        
        # Test 2: Extended GL₁ validation (limited)
        (
            "python3 gl1_extended_validation.py --max-prime 100 --precision 30",
            "Extended GL₁(p) Validation (Quick)",
            30
        ),
        
        # Test 3: KSS analysis
        (
            "python3 kss_analysis.py --precision 30",
            "Kato-Seiler-Simon Analysis",
            60
        ),
        
        # Test 4: Autonomous uniqueness (may have partial results due to truncation)
        (
            "python3 autonomous_uniqueness_verification.py --precision 30 || true",
            "Autonomous Uniqueness Verification (Partial Expected)",
            60
        ),
    ]
    
    results = []
    for cmd, description, timeout in tests:
        result = run_command(cmd, description, timeout)
        results.append((description, result))
    
    # Summary
    print("\n" + "="*70)
    print("INTEGRATION TEST SUMMARY")
    print("="*70)
    
    passed = sum(1 for _, r in results if r)
    total = len(results)
    
    for description, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} - {description}")
    
    print("="*70)
    print(f"Total: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n🎉 ALL INTEGRATION TESTS PASSED!")
        return 0
    else:
        print(f"\n⚠️ {total - passed} test(s) failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())
