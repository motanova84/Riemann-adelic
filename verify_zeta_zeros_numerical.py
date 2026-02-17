#!/usr/bin/env python3
"""
Numerical Verification of Riemann Zeta Zeros
=============================================

This script verifies that the Riemann zeta function vanishes at known zeros
on the critical line Re(s) = 1/2. Uses mpmath for high-precision computation.

The first several zeros have been computed to extreme precision by Odlyzko
and others. This script verifies them numerically.

Author: José Manuel Mota Burruezo & Noesis Ψ ∞³
Date: 2025-11-22
Part of QCAL ∞³ framework
"""

import mpmath as mp
from typing import List, Tuple
import json
from datetime import datetime

# QCAL ∞³ Framework Constants
# These constants define the quantum coherence parameters
QCAL_BASE_FREQUENCY_HZ = 141.7001  # Base frequency in Hz
QCAL_COHERENCE_CONSTANT = 244.36   # Coherence constant C in Ψ = I × A_eff² × C^∞

# Set precision for computations
mp.mp.dps = 50  # 50 decimal places

# Known zeros of ζ(1/2 + it) from Odlyzko tables
# These are the imaginary parts t where ζ(1/2 + it) = 0
KNOWN_ZEROS = [
    14.134725141734693790457251983562470270784257115699243175685567460149,
    21.022039638771554992628479593896902777334340524902781754629520403587,
    25.010857580145688763213790992562821818659549672557996672496542006745,
    30.424876125859513210311897530584091320181560023715440180962146036993,
    32.935061587739189690662368964074903488812715603517039009280003440784,
    37.586178158825671257217763480705332821405597350830793218333001113445,
    40.918719012147495187398126914633254395726165962777279536161303667128,
    43.327073280914999519496122165406805782645668371836871849935599050192,
    48.005150881167159727942472749427516041686844001144425117775312519906,
    49.773832477672302181916784678563724057723178299676662100781944617613
]


def zeta_on_critical_line(t: float) -> complex:
    """
    Compute ζ(1/2 + it) using mpmath
    
    Args:
        t: Imaginary part of the argument
        
    Returns:
        Value of ζ(1/2 + it)
    """
    s = mp.mpc(0.5, t)
    return mp.zeta(s)


def verify_zero(t: float, tolerance: float = 1e-30) -> Tuple[bool, float]:
    """
    Verify that ζ(1/2 + it) ≈ 0
    
    Args:
        t: Imaginary part to test
        tolerance: Maximum acceptable absolute value
        
    Returns:
        (is_zero, abs_value) where is_zero indicates if |ζ(1/2 + it)| < tolerance
    """
    zeta_val = zeta_on_critical_line(t)
    abs_val = abs(zeta_val)
    is_zero = abs_val < tolerance
    return is_zero, float(abs_val)


def verify_first_n_zeros(n: int = 10, tolerance: float = 1e-10) -> dict:
    """
    Verify the first N known zeros of the Riemann zeta function
    
    Args:
        n: Number of zeros to verify (max: len(KNOWN_ZEROS))
        tolerance: Tolerance for considering a value as zero
        
    Returns:
        Dictionary with verification results
    """
    n = min(n, len(KNOWN_ZEROS))
    results = {
        'total_checked': n,
        'all_verified': True,
        'tolerance': tolerance,
        'zeros': []
    }
    
    print(f"🔍 Verifying first {n} zeros of ζ(1/2 + it)")
    print(f"   Tolerance: {tolerance}")
    print()
    
    for i in range(n):
        t = KNOWN_ZEROS[i]
        is_zero, abs_val = verify_zero(t, tolerance)
        
        results['zeros'].append({
            'index': i + 1,
            't': float(t),
            'zeta_value_abs': abs_val,
            'verified': is_zero
        })
        
        status = "✅" if is_zero else "❌"
        print(f"{status} Zero #{i+1}: t = {t:.15f}")
        print(f"   |ζ(1/2 + it)| = {abs_val:.2e}")
        
        if not is_zero:
            results['all_verified'] = False
            print(f"   ⚠️  WARNING: Value exceeds tolerance!")
        print()
    
    return results


def export_verification_certificate(results: dict, filename: str = 'data/zeta_zeros_verification.json'):
    """
    Export verification results as a mathematical certificate
    
    Args:
        results: Verification results dictionary
        filename: Output file path
    """
    import os
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    certificate = {
        'title': 'Numerical Verification of Riemann Zeta Zeros',
        'timestamp': datetime.now().isoformat(),
        'precision_dps': mp.mp.dps,
        'verification': results,
        'references': [
            'A. M. Odlyzko, The first 100,000 zeros of the Riemann zeta function',
            'DOI: 10.5281/zenodo.17379721 (QCAL ∞³ Framework)'
        ],
        'author': 'José Manuel Mota Burruezo Ψ ∞³',
        'orcid': '0009-0002-1923-0773'
    }
    
    with open(filename, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"📜 Verification certificate saved to {filename}")


def main():
    """Main verification routine"""
    print("=" * 70)
    print("RIEMANN ZETA ZEROS - NUMERICAL VERIFICATION")
    print("=" * 70)
    print(f"Precision: {mp.mp.dps} decimal places")
    print(f"Framework: QCAL ∞³")
    print(f"Base frequency: {QCAL_BASE_FREQUENCY_HZ} Hz")
    print(f"Coherence constant: C = {QCAL_COHERENCE_CONSTANT}")
    print()
    
    # Verify first 10 zeros (or all available)
    results = verify_first_n_zeros(n=10, tolerance=1e-10)
    
    print("=" * 70)
    if results['all_verified']:
        print("✅ ALL ZEROS VERIFIED SUCCESSFULLY")
        print(f"   {results['total_checked']} zeros confirmed on critical line")
    else:
        print("⚠️  VERIFICATION INCOMPLETE")
        print("   Some zeros failed verification")
    print("=" * 70)
    print()
    
    # Export certificate
    export_verification_certificate(results)
    
    return 0 if results['all_verified'] else 1


if __name__ == '__main__':
    import sys
    sys.exit(main())
