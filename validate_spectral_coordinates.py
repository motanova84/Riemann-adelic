#!/usr/bin/env python3
"""
Quick validation of spectral coordinates implementation.

This script runs basic tests without needing pytest or other dependencies.
It validates the spectral coordinates τ(p) implementation for the QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path


def verify_repository_root():
    """
    Verify that the script is being executed from the repository root directory.
    
    This check ensures that all relative paths and imports will work correctly.
    The repository root is identified by the presence of key marker files.
    
    Raises:
        SystemExit: If the script is not being run from the repository root.
    """
    current_dir = Path.cwd()
    
    # Check for key marker files that should exist in repo root
    markers = ['.qcal_beacon', 'operators', 'tests', 'validate_v5_coronacion.py']
    
    missing = [m for m in markers if not (current_dir / m).exists()]
    
    if missing:
        print()
        print("ERROR: This script must be run from the repository root directory.")
        print(f"Current directory: {current_dir}")
        print(f"Missing markers: {', '.join(missing)}")
        print()
        print("Please run:")
        print(f"  cd {current_dir.parent if current_dir.name != 'Riemann-adelic' else current_dir}")
        print(f"  python {Path(__file__).name}")
        print()
        sys.exit(1)


# Verify we're in the correct directory BEFORE any other imports
verify_repository_root()

# Now safe to import
from operators.spectral_coordinates import (
    compute_tau,
    verify_monotonicity,
    verify_constant_imaginary,
    validate_spectral_coordinates,
    F0,
    GAMMA_1
)

def test_basic_computation():
    """Test basic τ(p) computation."""
    print("Testing basic computation...")
    
    tau_3 = compute_tau(3)
    assert tau_3.real > 0, "Real part should be positive"
    assert tau_3.imag > 0, "Imaginary part should be positive"
    
    tau_5 = compute_tau(5)
    assert tau_5.real > tau_3.real, "Monotonicity check failed"
    assert abs(tau_5.imag - tau_3.imag) < 1e-10, "Imaginary parts should be equal"
    
    print("  ✓ Basic computation passed")


def test_properties():
    """Test key properties."""
    print("Testing properties...")
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    assert verify_monotonicity(primes), "Monotonicity test failed"
    assert verify_constant_imaginary(primes), "Constant imaginary test failed"
    
    print("  ✓ Monotonicity verified")
    print("  ✓ Constant imaginary part verified")


def test_validation():
    """Test validation function."""
    print("Testing validation...")
    
    results = validate_spectral_coordinates()
    assert results['validated'], "Validation failed"
    assert results['properties_verified']['monotonicity'], "Monotonicity verification failed"
    assert results['properties_verified']['constant_imaginary'], "Constant imaginary verification failed"
    
    print("  ✓ Validation passed")


def test_constants():
    """Test fundamental constants."""
    print("Testing constants...")
    
    assert F0 == 141.7001, f"F0 should be 141.7001, got {F0}"
    assert GAMMA_1 == 14.134725, f"GAMMA_1 should be 14.134725, got {GAMMA_1}"
    
    print("  ✓ Constants verified")


def main():
    """Run all tests."""
    print()
    print("=" * 60)
    print("Spectral Coordinates Quick Validation")
    print("=" * 60)
    print()
    
    try:
        test_constants()
        test_basic_computation()
        test_properties()
        test_validation()
        
        print()
        print("=" * 60)
        print("✅ All validation tests passed!")
        print("=" * 60)
        print()
        return 0
        
    except AssertionError as e:
        print()
        print("=" * 60)
        print(f"❌ Validation failed: {e}")
        print("=" * 60)
        print()
        return 1
    except Exception as e:
        print()
        print("=" * 60)
        print(f"❌ Error: {e}")
        print("=" * 60)
        print()
        return 1


if __name__ == "__main__":
    sys.exit(main())
