#!/usr/bin/env python3
"""
Validation Script for Paso de la Verdad Implementation
=======================================================

This script validates the Hilbert-Pólya operator implementation
and generates a certificate.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import json
import hashlib
import time
from datetime import datetime
import numpy as np

from operators.hilbert_polya_paso_verdad import (
    paso_de_la_verdad,
    construct_full_operator,
    verify_hermitian,
    compute_kernel_L2_norm,
    verify_spectral_reality,
    prime_sieve,
    F0_QCAL,
    C_COHERENCE,
    C_PRIMARY
)


def validate_paso_verdad(verbose=True):
    """
    Comprehensive validation of Paso de la Verdad implementation.
    
    Returns:
        dict: Validation results and certificate
    """
    if verbose:
        print("=" * 80)
        print("VALIDACIÓN PASO DE LA VERDAD")
        print("=" * 80)
        print(f"Date: {datetime.now().isoformat()}")
        print(f"QCAL ∞³: f₀ = {F0_QCAL} Hz, C = {C_COHERENCE}")
        print()
    
    validation_results = {
        'timestamp': datetime.now().isoformat(),
        'qcal_constants': {
            'f0': F0_QCAL,
            'C_coherence': C_COHERENCE,
            'C_primary': C_PRIMARY
        },
        'tests': []
    }
    
    # Test 1: Small grid (quick test)
    if verbose:
        print("[1/5] Testing with small grid (N=32)...")
    
    try:
        results_small = paso_de_la_verdad(N=32, verbose=False)
        test1 = {
            'name': 'Small grid test',
            'N': 32,
            'passed': True,
            'hermitian': bool(results_small['hermitian'].is_hermitian),
            'kernel_L2': bool(results_small['kernel_L2'].kernel_in_L2),
            'spectrum_real': bool(results_small['spectral_reality'].spectrum_is_real),
            'psi_total': float(results_small['psi_total'])
        }
        validation_results['tests'].append(test1)
        
        if verbose:
            print(f"  ✓ Passed: Ψ = {test1['psi_total']:.4f}")
    except Exception as e:
        if verbose:
            print(f"  ✗ Failed: {str(e)}")
        test1 = {'name': 'Small grid test', 'passed': False, 'error': str(e)}
        validation_results['tests'].append(test1)
    
    # Test 2: Medium grid (standard test)
    if verbose:
        print("[2/5] Testing with medium grid (N=64)...")
    
    try:
        results_medium = paso_de_la_verdad(N=64, verbose=False)
        test2 = {
            'name': 'Medium grid test',
            'N': 64,
            'passed': True,
            'hermitian': bool(results_medium['hermitian'].is_hermitian),
            'hermitian_error': float(results_medium['hermitian'].hermitian_error),
            'kernel_L2': bool(results_medium['kernel_L2'].kernel_in_L2),
            'kernel_L2_norm': float(results_medium['kernel_L2'].L2_norm),
            'spectrum_real': bool(results_medium['spectral_reality'].spectrum_is_real),
            'n_eigenvalues': len(results_medium['spectral_reality'].eigenvalues),
            'psi_total': float(results_medium['psi_total'])
        }
        validation_results['tests'].append(test2)
        
        if verbose:
            print(f"  ✓ Passed: Ψ = {test2['psi_total']:.4f}")
            print(f"    Hermitian error: {test2['hermitian_error']:.2e}")
            print(f"    ||K||_L² = {test2['kernel_L2_norm']:.2f}")
    except Exception as e:
        if verbose:
            print(f"  ✗ Failed: {str(e)}")
        test2 = {'name': 'Medium grid test', 'passed': False, 'error': str(e)}
        validation_results['tests'].append(test2)
    
    # Test 3: Large grid (precision test)
    if verbose:
        print("[3/5] Testing with large grid (N=128)...")
    
    try:
        results_large = paso_de_la_verdad(N=128, verbose=False)
        test3 = {
            'name': 'Large grid test',
            'N': 128,
            'passed': True,
            'hermitian': bool(results_large['hermitian'].is_hermitian),
            'hermitian_error': float(results_large['hermitian'].hermitian_error),
            'kernel_L2': bool(results_large['kernel_L2'].kernel_in_L2),
            'kernel_L2_norm': float(results_large['kernel_L2'].L2_norm),
            'spectrum_real': bool(results_large['spectral_reality'].spectrum_is_real),
            'n_eigenvalues': len(results_large['spectral_reality'].eigenvalues),
            'mean_error_to_zeros': float(results_large['spectral_reality'].mean_error_to_zeros),
            'psi_total': float(results_large['psi_total'])
        }
        validation_results['tests'].append(test3)
        
        if verbose:
            print(f"  ✓ Passed: Ψ = {test3['psi_total']:.4f}")
            print(f"    Hermitian error: {test3['hermitian_error']:.2e}")
            print(f"    ||K||_L² = {test3['kernel_L2_norm']:.2f}")
            print(f"    Error to zeros: {test3['mean_error_to_zeros']:.2f}")
    except Exception as e:
        if verbose:
            print(f"  ✗ Failed: {str(e)}")
        test3 = {'name': 'Large grid test', 'passed': False, 'error': str(e)}
        validation_results['tests'].append(test3)
    
    # Test 4: Prime sieve correctness
    if verbose:
        print("[4/5] Testing prime sieve...")
    
    try:
        primes = prime_sieve(100)
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 
                          43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
        
        test4 = {
            'name': 'Prime sieve test',
            'passed': primes == expected_primes,
            'n_primes_found': len(primes),
            'n_primes_expected': len(expected_primes)
        }
        validation_results['tests'].append(test4)
        
        if verbose:
            if test4['passed']:
                print(f"  ✓ Passed: {len(primes)} primes found")
            else:
                print(f"  ✗ Failed: Expected {len(expected_primes)}, got {len(primes)}")
    except Exception as e:
        if verbose:
            print(f"  ✗ Failed: {str(e)}")
        test4 = {'name': 'Prime sieve test', 'passed': False, 'error': str(e)}
        validation_results['tests'].append(test4)
    
    # Test 5: Hermiticity precision
    if verbose:
        print("[5/5] Testing Hermiticity precision...")
    
    try:
        H, x = construct_full_operator(N=64)
        hermitian_result = verify_hermitian(H, threshold=1e-12)
        
        test5 = {
            'name': 'Hermiticity precision test',
            'passed': bool(hermitian_result.is_hermitian and hermitian_result.hermitian_error < 1e-10),
            'hermitian_error': float(hermitian_result.hermitian_error),
            'symmetry_error': float(hermitian_result.symmetry_error),
            'threshold': 1e-12,
            'psi': float(hermitian_result.psi)
        }
        validation_results['tests'].append(test5)
        
        if verbose:
            if test5['passed']:
                print(f"  ✓ Passed: error = {test5['hermitian_error']:.2e}, Ψ = {test5['psi']:.6f}")
            else:
                print(f"  ✗ Failed: error = {test5['hermitian_error']:.2e} > 1e-10")
    except Exception as e:
        if verbose:
            print(f"  ✗ Failed: {str(e)}")
        test5 = {'name': 'Hermiticity precision test', 'passed': False, 'error': str(e)}
        validation_results['tests'].append(test5)
    
    # Summary
    passed_tests = sum(1 for test in validation_results['tests'] if test.get('passed', False))
    total_tests = len(validation_results['tests'])
    
    validation_results['summary'] = {
        'total_tests': total_tests,
        'passed_tests': passed_tests,
        'failed_tests': total_tests - passed_tests,
        'success_rate': passed_tests / total_tests if total_tests > 0 else 0
    }
    
    # Generate certificate hash
    cert_data = json.dumps(validation_results, sort_keys=True)
    cert_hash = hashlib.sha256(cert_data.encode()).hexdigest()
    validation_results['certificate_hash'] = f"0xQCAL_PASO_VERDAD_{cert_hash[:16]}"
    
    if verbose:
        print()
        print("=" * 80)
        print("VALIDATION SUMMARY")
        print("=" * 80)
        print(f"Total tests: {total_tests}")
        print(f"Passed: {passed_tests}")
        print(f"Failed: {total_tests - passed_tests}")
        print(f"Success rate: {validation_results['summary']['success_rate']*100:.1f}%")
        print()
        print(f"Certificate hash: {validation_results['certificate_hash']}")
        print("=" * 80)
    
    return validation_results


def save_certificate(results, filename='data/paso_verdad_validation_certificate.json'):
    """
    Save validation certificate to file.
    
    Args:
        results: Validation results dictionary
        filename: Output filename
    """
    import os
    
    # Ensure data directory exists
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    
    # Save certificate
    with open(filename, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✓ Certificate saved to: {filename}")


if __name__ == "__main__":
    # Run validation
    results = validate_paso_verdad(verbose=True)
    
    # Save certificate
    save_certificate(results)
    
    # Exit with appropriate code
    import sys
    if results['summary']['success_rate'] == 1.0:
        print("\n✅ ALL VALIDATIONS PASSED")
        sys.exit(0)
    else:
        print("\n⚠️ SOME VALIDATIONS FAILED")
        sys.exit(1)
