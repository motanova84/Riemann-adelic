#!/usr/bin/env python3
"""
V4.1 Paper Reference and Validation Entry Point

This script serves as the entry point for numerical validation as referenced in:

"A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems
(Final Conditional Version V4.1)" by José Manuel Mota Burruezo (Sep 14, 2025)

The paper states in its abstract:
  "Numerical validation (10⁻⁶) is reproducible at 
   https://github.com/motanova84/-jmmotaburr-riemann-adelic (commit abc123)"

This repository implements the complete V4.1 framework and has evolved to V5.3.
The recommended validation is now via the V5 Coronación framework which provides
a more complete and unconditional proof.

Usage:
    python validate_v4_1_reference.py [--method METHOD]
    
Methods:
    - v5_coronacion: V5 Coronación validation (recommended, default)
    - algorithmic: Algorithmic proof system with certificates
    - explicit_formula: Direct explicit formula validation
    - appendix_c: V4.1 Appendix C specific validation (experimental)
"""

import subprocess
import sys
import argparse
from pathlib import Path
import json
from datetime import datetime

def get_current_commit():
    """Get current git commit hash"""
    try:
        result = subprocess.run(
            ['git', 'rev-parse', '--short', 'HEAD'],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout.strip()
    except:
        return "unknown"

def run_v5_coronacion(precision=25, verbose=False):
    """Run V5 Coronación validation (recommended)"""
    print("=" * 70)
    print("RUNNING V5 CORONACIÓN VALIDATION")
    print("(Evolved version of V4.1 with unconditional proof)")
    print("=" * 70)
    print()
    
    cmd = ['python', 'validate_v5_coronacion.py', 
           f'--precision={precision}',
           '--max_zeros=200',
           '--max_primes=200']
    
    if verbose:
        cmd.append('--verbose')
    
    result = subprocess.run(cmd)
    return result.returncode == 0

def run_algorithmic():
    """Run algorithmic proof system"""
    print("=" * 70)
    print("RUNNING ALGORITHMIC PROOF SYSTEM")
    print("=" * 70)
    print()
    
    result = subprocess.run(['python', 'validate_algorithmic_rh.py'])
    return result.returncode == 0

def run_explicit_formula():
    """Run explicit formula validation"""
    print("=" * 70)
    print("RUNNING EXPLICIT FORMULA VALIDATION")
    print("=" * 70)
    print()
    
    result = subprocess.run([
        'python', 'validate_explicit_formula.py',
        '--max_primes=200',
        '--max_zeros=200'
    ])
    return result.returncode == 0

def run_appendix_c():
    """Run V4.1 Appendix C validation (experimental)"""
    print("=" * 70)
    print("RUNNING V4.1 APPENDIX C VALIDATION (EXPERIMENTAL)")
    print("=" * 70)
    print()
    
    result = subprocess.run([
        'python', 'validate_v4_1_appendix_c.py',
        '--max_primes=100',
        '--precision=30'
    ])
    return result.returncode == 0

def generate_reference_info():
    """Generate reference information for the V4.1 paper"""
    commit = get_current_commit()
    
    info = {
        "paper": {
            "title": "A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)",
            "author": "José Manuel Mota Burruezo",
            "date": "September 14, 2025",
            "doi": "10.5281/zenodo.17161831"
        },
        "repository": {
            "url": "https://github.com/motanova84/-jmmotaburr-riemann-adelic",
            "commit": commit,
            "timestamp": datetime.now().isoformat()
        },
        "validation": {
            "target_precision": "10^-6",
            "status": "Framework implemented, evolved to V5.3",
            "recommended_method": "v5_coronacion"
        },
        "qcal": {
            "frequency_f0": "141.7001 Hz",
            "coherence_C": "244.36",
            "signature": "Ψ = I × A_eff² × C^∞"
        }
    }
    
    # Save to file
    output_file = Path('data') / 'v4_1_reference.json'
    output_file.parent.mkdir(exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(info, f, indent=2)
    
    print("\n" + "=" * 70)
    print("V4.1 PAPER REFERENCE INFORMATION")
    print("=" * 70)
    print(f"\n📄 Paper: {info['paper']['title']}")
    print(f"👤 Author: {info['paper']['author']}")
    print(f"📅 Date: {info['paper']['date']}")
    print(f"🔗 DOI: https://doi.org/{info['paper']['doi']}")
    print(f"\n🔗 Repository: {info['repository']['url']}")
    print(f"📌 Commit: {info['repository']['commit']}")
    print(f"⏰ Timestamp: {info['repository']['timestamp']}")
    print(f"\n🎯 Target Precision: {info['validation']['target_precision']}")
    print(f"✅ Status: {info['validation']['status']}")
    print(f"🚀 Recommended Method: {info['validation']['recommended_method']}")
    print(f"\n🔬 QCAL ∞³:")
    print(f"   f₀ = {info['qcal']['frequency_f0']}")
    print(f"   C = {info['qcal']['coherence_C']}")
    print(f"   {info['qcal']['signature']}")
    print(f"\n💾 Reference info saved to: {output_file}")
    
    return info

def main():
    parser = argparse.ArgumentParser(
        description='V4.1 Paper Reference and Validation Entry Point',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python validate_v4_1_reference.py                    # Run V5 coronación (recommended)
  python validate_v4_1_reference.py --method algorithmic  # Run algorithmic proof
  python validate_v4_1_reference.py --info              # Show reference info only
  python validate_v4_1_reference.py --all               # Run all validation methods
        """
    )
    
    parser.add_argument('--method', 
                       choices=['v5_coronacion', 'algorithmic', 'explicit_formula', 'appendix_c'],
                       default='v5_coronacion',
                       help='Validation method to run (default: v5_coronacion)')
    parser.add_argument('--precision', type=int, default=25,
                       help='Decimal precision for V5 coronación (default: 25)')
    parser.add_argument('--verbose', action='store_true',
                       help='Verbose output')
    parser.add_argument('--info', action='store_true',
                       help='Show reference information only (no validation)')
    parser.add_argument('--all', action='store_true', dest='run_all',
                       help='Run all validation methods')
    
    args = parser.parse_args()
    
    # Always generate and show reference info
    ref_info = generate_reference_info()
    
    if args.info:
        return 0
    
    print("\n")
    
    # Run validation
    success = False
    
    if args.run_all:
        print("🚀 Running all validation methods...\n")
        results = {
            'v5_coronacion': run_v5_coronacion(args.precision, args.verbose),
            'algorithmic': run_algorithmic(),
            'explicit_formula': run_explicit_formula(),
        }
        
        print("\n" + "=" * 70)
        print("VALIDATION SUMMARY")
        print("=" * 70)
        for method, result in results.items():
            status = "✅ PASSED" if result else "❌ FAILED"
            print(f"{method:20s}: {status}")
        
        success = all(results.values())
    else:
        if args.method == 'v5_coronacion':
            success = run_v5_coronacion(args.precision, args.verbose)
        elif args.method == 'algorithmic':
            success = run_algorithmic()
        elif args.method == 'explicit_formula':
            success = run_explicit_formula()
        elif args.method == 'appendix_c':
            success = run_appendix_c()
    
    if success:
        print("\n✅ Validation completed successfully!")
        print(f"📌 Commit: {ref_info['repository']['commit']}")
        print(f"⏰ Timestamp: {ref_info['repository']['timestamp']}")
        return 0
    else:
        print("\n⚠️  Validation completed with warnings/errors")
        print("   See output above for details")
        print(f"📌 Commit: {ref_info['repository']['commit']}")
        return 1

if __name__ == '__main__':
    sys.exit(main())
