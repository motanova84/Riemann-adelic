#!/usr/bin/env python3
"""
Demo of TAUberian Spectral Computation

This script demonstrates the TAUberian spectral method for computing
Riemann zeros with rigorous error bounds.

Usage:
    python demo_tauberian.py [--small]
    
    --small: Run with small parameters for quick demonstration
"""

import sys
import argparse
from tauberian_spectral import tauberian_spectral_computation, validatio_tauberiana


def demo_small_computation():
    """Quick demonstration with small parameters"""
    print("="*70)
    print("TAUberian Spectral Computation - Small Demo")
    print("="*70)
    print()
    
    # Small parameters for quick demo
    N = 10
    h = 0.001
    num_jobs = 2
    
    print(f"Parameters:")
    print(f"  N (basis functions): {N}")
    print(f"  h (thermal parameter): {h}")
    print(f"  num_jobs: {num_jobs}")
    print()
    
    print("Computing zeros...")
    try:
        zeros, H = tauberian_spectral_computation(N, h, num_jobs)
        
        print(f"\nComputed {len(zeros)} zeros:")
        for i, z in enumerate(zeros[:5]):
            print(f"  ρ_{i+1} = {z.real:.4f} + {z.imag:.8f}i")
        
        print("\nNote: This is a small/fast computation for demonstration.")
        print("Results may not be highly accurate. Use larger N and smaller h")
        print("for production computations.")
        
    except Exception as e:
        print(f"\nError during computation: {e}")
        print("This is expected for a quick demo - the computation is very demanding.")
        

def demo_full_validation():
    """Full validation with production parameters"""
    print("="*70)
    print("TAUberian Spectral Computation - Full Validation")
    print("="*70)
    print()
    print("WARNING: This will take several minutes to complete!")
    print("Parameters: N=80, h=0.0002")
    print()
    
    response = input("Continue? [y/N]: ")
    if response.lower() != 'y':
        print("Cancelled.")
        return
    
    print("\nRunning full validation...")
    success, zeros = validatio_tauberiana()
    
    if success:
        print("\n" + "="*70)
        print("✅ VALIDATION SUCCESSFUL")
        print("="*70)
        print("\nAll zeros computed within TAUberian error bounds!")
        print("\nFirst 5 computed zeros:")
        for i, z in enumerate(zeros[:5]):
            print(f"  ρ_{i+1} = {z.real:.4f} + {z.imag:.12f}i")
    else:
        print("\n" + "="*70)
        print("⚠️  Validation completed with warnings")
        print("="*70)
        print("See output above for details.")


def demo_parameter_exploration():
    """Show effect of different parameters"""
    print("="*70)
    print("TAUberian Parameter Exploration")
    print("="*70)
    print()
    
    print("Effect of N (number of basis functions):")
    print("  N=10:  Fast, low accuracy (~1-2 minute)")
    print("  N=50:  Medium, good accuracy (~5-10 minutes)")
    print("  N=80:  Slow, high accuracy (~10-20 minutes)")
    print("  N=100: Very slow, very high accuracy (~30+ minutes)")
    print()
    
    print("Effect of h (thermal parameter):")
    print("  h=0.01:  Very fast, low precision")
    print("  h=0.001: Fast, medium precision")
    print("  h=0.0002: Slow, high precision")
    print("  h=0.0001: Very slow, very high precision")
    print()
    
    print("Recommended combinations:")
    print("  Quick test:     N=10,  h=0.01   (~1 min)")
    print("  Medium:         N=50,  h=0.001  (~5 min)")
    print("  Production:     N=80,  h=0.0002 (~15 min)")
    print("  High precision: N=100, h=0.0001 (~30+ min)")
    print()


def main():
    parser = argparse.ArgumentParser(
        description='Demo of TAUberian Spectral Computation'
    )
    parser.add_argument(
        '--small', 
        action='store_true',
        help='Run small/fast demo instead of full validation'
    )
    parser.add_argument(
        '--params',
        action='store_true',
        help='Show parameter exploration guide'
    )
    
    args = parser.parse_args()
    
    if args.params:
        demo_parameter_exploration()
    elif args.small:
        demo_small_computation()
    else:
        demo_full_validation()


if __name__ == "__main__":
    main()
