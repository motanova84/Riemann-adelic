#!/usr/bin/env python3
"""
Comprehensive test to validate all badge-related workflows
This script simulates what each CI/CD workflow does locally
"""

import sys
import subprocess
import json
from pathlib import Path
from datetime import datetime


def run_command(cmd, description, timeout=120):
    """Run a shell command and report results"""
    print(f"\n{'='*80}")
    print(f"🔍 {description}")
    print(f"{'='*80}")
    print(f"Command: {cmd}")
    
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=Path(__file__).parent
        )
        
        if result.returncode == 0:
            print(f"✅ {description}: PASSED")
            if result.stdout:
                print(f"Output (last 20 lines):")
                lines = result.stdout.split('\n')
                for line in lines[-20:]:
                    if line.strip():
                        print(f"  {line}")
            return True
        else:
            print(f"❌ {description}: FAILED (exit code {result.returncode})")
            if result.stderr:
                print(f"Error output:")
                for line in result.stderr.split('\n')[:20]:
                    if line.strip():
                        print(f"  {line}")
            return False
    except subprocess.TimeoutExpired:
        print(f"⚠️  {description}: TIMEOUT (exceeded {timeout}s)")
        return False
    except Exception as e:
        print(f"❌ {description}: ERROR - {str(e)}")
        return False


def main():
    """Run all badge-related validations"""
    print("="*80)
    print("🎯 COMPREHENSIVE BADGE VALIDATION TEST SUITE")
    print("="*80)
    print(f"Timestamp: {datetime.now().isoformat()}")
    print(f"Working directory: {Path(__file__).parent}")
    print()
    
    results = {}
    
    # 1. V5 Coronación validation
    results['v5_coronacion'] = run_command(
        "python3 validate_v5_coronacion.py --precision 15",
        "1. V5 Coronación Validation",
        timeout=60
    )
    
    # 2. Core pytest tests (simulating CI Coverage)
    results['ci_coverage'] = run_command(
        "pytest tests/test_coronacion_v5.py tests/test_a4_lemma.py tests/test_adelic_D.py -v --tb=short",
        "2. CI Coverage - Core Tests",
        timeout=120
    )
    
    # 3. Critical Line Verification
    results['critical_line'] = run_command(
        "python3 validate_critical_line.py --max_zeros 100 --precision 20",
        "3. Critical Line Verification",
        timeout=60
    )
    
    # 4. Explicit Formula Validation
    results['explicit_formula'] = run_command(
        "python3 validate_explicit_formula.py --max_primes 100 --max_zeros 100 --precision_dps 15",
        "4. Explicit Formula Validation",
        timeout=120
    )
    
    # 5. Lean formalization file check
    results['lean_files'] = run_command(
        "find formalization/lean -name '*.lean' | head -10",
        "5. Lean Formalization File Check",
        timeout=10
    )
    
    # 6. Badge link verification
    results['badge_links'] = run_command(
        "python3 test_badge_links.py",
        "6. Badge Links Verification",
        timeout=30
    )
    
    # 7. Repository validation
    results['repo_validation'] = run_command(
        "python3 validate_repository.py",
        "7. Repository Structure Validation",
        timeout=60
    )
    
    # Print summary
    print("\n" + "="*80)
    print("📊 VALIDATION SUMMARY")
    print("="*80)
    
    total_tests = len(results)
    passed_tests = sum(1 for v in results.values() if v)
    failed_tests = total_tests - passed_tests
    
    print(f"\n✅ Passed: {passed_tests}/{total_tests}")
    print(f"❌ Failed: {failed_tests}/{total_tests}")
    print()
    
    for test_name, passed in results.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {status} - {test_name}")
    
    print("\n" + "="*80)
    print("🎯 BADGE READINESS STATUS")
    print("="*80)
    
    badges = {
        "V5 Coronación": results['v5_coronacion'],
        "CI Coverage": results['ci_coverage'],
        "Critical Line Verification": results['critical_line'],
        "Advanced Validation": results['explicit_formula'],
        "Lean Formalization": results['lean_files'],
        "Badge System": results['badge_links'],
        "Repository": results['repo_validation']
    }
    
    for badge_name, status in badges.items():
        badge_status = "🟢 READY" if status else "🔴 NEEDS ATTENTION"
        print(f"  {badge_status} - {badge_name}")
    
    # Save results to JSON
    results_file = Path(__file__).parent / "data" / "badge_validation_results.json"
    results_file.parent.mkdir(exist_ok=True)
    
    with open(results_file, 'w') as f:
        json.dump({
            'timestamp': datetime.now().isoformat(),
            'total_tests': total_tests,
            'passed_tests': passed_tests,
            'failed_tests': failed_tests,
            'results': results,
            'badges': badges
        }, f, indent=2)
    
    print(f"\n📄 Results saved to: {results_file}")
    
    if failed_tests == 0:
        print("\n🎉 ALL BADGES ARE READY TO PASS!")
        print("✨ The CI/CD workflows should all run green!")
        return 0
    else:
        print(f"\n⚠️  {failed_tests} validation(s) need attention")
        print("   Review the failed tests above and fix issues")
        return 1


if __name__ == '__main__':
    sys.exit(main())
