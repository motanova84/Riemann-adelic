#!/usr/bin/env python3
"""
Validate all computational processes in the repository.
This script reactivates and runs all computational processes to ensure they complete successfully.
"""

import os
import subprocess
import sys
import time
from pathlib import Path

def run_command(cmd, description, timeout=300):
    """Run a command with timeout and error handling."""
    print(f"🔄 {description}...")
    start_time = time.time()
    
    try:
        result = subprocess.run(
            cmd, 
            shell=True, 
            capture_output=True, 
            text=True, 
            timeout=timeout,
            cwd='/home/runner/work/-jmmotaburr-riemann-adelic/-jmmotaburr-riemann-adelic'
        )
        
        duration = time.time() - start_time
        
        if result.returncode == 0:
            print(f"✅ {description} completed successfully ({duration:.1f}s)")
            if result.stdout:
                print(f"   Output: {result.stdout.strip()[:200]}...")
            return True
        else:
            print(f"❌ {description} failed with return code {result.returncode}")
            if result.stderr:
                print(f"   Error: {result.stderr.strip()[:300]}...")
            return False
            
    except subprocess.TimeoutExpired:
        print(f"⏰ {description} timed out after {timeout}s")
        return False
    except Exception as e:
        print(f"💥 {description} crashed: {e}")
        return False

def main():
    """Run all validation processes."""
    print("🚀 Starting validation of all computational processes...")
    print("=" * 60)
    
    # Ensure directories exist
    os.makedirs("data", exist_ok=True)
    os.makedirs("logs", exist_ok=True)
    os.makedirs("docs", exist_ok=True)
    
    processes = [
        # 1. Test the test suite
        ("python -m pytest tests/ -v --tb=short", "Running test suite", 180),
        
        # 2. Check zeros data integrity
        ("python utils/checksum_zeros.py", "Validating zeros data", 30),
        
        # 3. Run main validation with small parameters
        ("python validate_explicit_formula.py --max_primes 50 --max_zeros 50 --precision_dps 15", "Main validation script (small)", 120),
        
        # 4. Run validation with Weil formula
        ("python validate_explicit_formula.py --use_weil_formula --max_primes 50 --max_zeros 50 --precision_dps 15 --integration_t 10", "Weil formula validation", 120),
        
        # 5. Run alternative validation script
        ("python validate_by_height.py --max_zeros 50", "Alternative validation script", 60),
        
        # 6. Simple notebook execution test
        ("python simple_notebook_test.py", "Notebook execution test", 120),
        
        # 7. Test utility functions
        ("python -c \"from utils.mellin import truncated_gaussian, mellin_transform; from utils.riemann_tools import t_to_n, load_zeros_near_t; print('✅ All utility imports successful')\"", "Utility functions test", 30),
    ]
    
    results = {}
    
    for cmd, desc, timeout in processes:
        success = run_command(cmd, desc, timeout)
        results[desc] = success
        print()
    
    # Summary
    print("=" * 60)
    print("📊 PROCESS VALIDATION SUMMARY")
    print("=" * 60)
    
    passed = sum(results.values())
    total = len(results)
    
    for desc, success in results.items():
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status}: {desc}")
    
    print(f"\n🏁 Results: {passed}/{total} processes completed successfully")
    
    if passed == total:
        print("🎉 All processes are working correctly!")
        
        # Create a completion report
        with open("logs/process_validation.log", "w") as f:
            f.write(f"Process Validation Report - {time.ctime()}\n")
            f.write(f"Results: {passed}/{total} processes completed successfully\n\n")
            for desc, success in results.items():
                status = "PASS" if success else "FAIL"
                f.write(f"{status}: {desc}\n")
        
        return 0
    else:
        print(f"⚠️  {total - passed} processes need attention")
        return 1

if __name__ == "__main__":
    sys.exit(main())