#!/usr/bin/env python3
"""
Demonstration: Riemann Zeros Frequency Computation

This script demonstrates the computation of a specific frequency based on
Riemann zeros with exponential decay weighting and golden ratio scaling.

The demonstration shows:
1. Loading Riemann zeros from data files
2. Computing weighted sum with exponential decay: Σ exp(-α·γ_n)
3. Validating against φ·400/exp(γ·π) target value
4. Computing final frequency with multiple scaling factors

Usage:
    python demo_zeros_frequency.py [--precision DPS] [--T HEIGHT] [--alpha ALPHA]

Examples:
    python demo_zeros_frequency.py
    python demo_zeros_frequency.py --precision 50 --T 4000 --alpha 0.55
    python demo_zeros_frequency.py --limit 1000

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import sys
from pathlib import Path

# Direct import to avoid utils/__init__.py issues
sys.path.insert(0, str(Path(__file__).parent))

# Import directly from the module file
import importlib.util
spec = importlib.util.spec_from_file_location(
    "zeros_frequency_computation",
    Path(__file__).parent / "utils" / "zeros_frequency_computation.py"
)
zfc_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(zfc_module)
ZerosFrequencyComputation = zfc_module.ZerosFrequencyComputation


def main():
    """
    Main demonstration function.
    """
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 15 + "RIEMANN ZEROS FREQUENCY COMPUTATION" + " " * 28 + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  Golden Ratio Scaling with Exponential Decay".ljust(78) + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    # Create computation instance with high precision
    print("🔧 Initializing computation with 100 decimal places precision...")
    computation = ZerosFrequencyComputation(dps=100)
    
    print("✅ Constants initialized:")
    print(f"   φ (phi):  {computation.phi}")
    print(f"   γ (gamma): {computation.gamma}")
    print(f"   π (pi):   {computation.pi}")
    print(f"   exp(γ·π): {computation.e_gamma_pi}")
    print(f"   φ×400:    {computation.phi_400}")
    print(f"   Target:   {computation.target}")
    print()
    
    # Run complete computation with default parameters
    print("🔬 Running complete computation chain...")
    print("   Parameters: T=3967.986, α=0.551020, limit=3438")
    print()
    
    try:
        results = computation.run_complete_computation(
            T=3967.986,
            alpha=0.551020,
            limit=3438,
            verbose=True
        )
        
        print()
        print("📊 RESULTS SUMMARY:")
        print("-" * 80)
        print(f"Sum S:                {results['sum']:.15e}")
        print(f"Validation S·e^(γπ):  {results['validation_result']:.15e}")
        print(f"Target φ×400:         {results['target']:.15e}")
        print(f"Validation status:    {'✅ PASSED' if results['validation_passed'] else '❌ FAILED'}")
        print(f"Frequency:            {results['frequency_hz']:.10f} Hz")
        print("-" * 80)
        
        # Additional analysis
        print()
        print("📈 ADDITIONAL ANALYSIS:")
        print("-" * 80)
        
        # Compare with QCAL beacon frequency
        qcal_frequency = 141.7001
        freq_ratio = results['frequency_hz'] / qcal_frequency
        print(f"QCAL beacon frequency: {qcal_frequency} Hz")
        print(f"Computed frequency:    {results['frequency_hz']:.6f} Hz")
        print(f"Ratio (computed/QCAL): {freq_ratio:.6f}")
        
        # Relative error analysis
        rel_error = abs(results['validation_result'] - results['target']) / results['target']
        print(f"Relative error:        {rel_error:.2e}")
        print("-" * 80)
        
        print()
        print("✨ Computation completed successfully!")
        
        return 0
        
    except FileNotFoundError as e:
        print(f"❌ Error: {e}")
        print()
        print("💡 Make sure you are running this script from the repository root:")
        print("   cd /path/to/-jmmotaburr-riemann-adelic")
        print("   python demo_zeros_frequency.py")
        return 1
        
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
