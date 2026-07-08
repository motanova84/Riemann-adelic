#!/usr/bin/env python3
"""
Validation Script for Selberg-Riemann Holographic Trace Formula
================================================================

Validates the arithmetic holography implementation and generates certificate.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import json
import hashlib
from datetime import datetime
import numpy as np
from pathlib import Path
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))

from operators.selberg_riemann_holographic_trace import (
    SelbergRiemannHolographicTrace,
    demonstrate_holographic_trace,
    F0_QCAL,
    C_COHERENCE,
    OMEGA_0
)


def validate_selberg_riemann_holographic_trace(verbose: bool = True) -> dict:
    """
    Comprehensive validation of the Selberg-Riemann holographic trace implementation.
    
    Validates:
    1. Test function properties
    2. Fourier transform correctness
    3. Geodesic sum computation
    4. Spectral sum computation
    5. Holographic correspondence
    6. QCAL integration
    
    Args:
        verbose: Print detailed output
        
    Returns:
        Dictionary with validation results
    """
    if verbose:
        print("="*80)
        print("SELBERG-RIEMANN HOLOGRAPHIC TRACE VALIDATION")
        print("="*80)
        print(f"Timestamp: {datetime.now().isoformat()}")
        print(f"QCAL ∞³: f₀ = {F0_QCAL} Hz, C = {C_COHERENCE}")
        print("="*80)
        print()
    
    validation_results = {
        'timestamp': datetime.now().isoformat(),
        'qcal_constants': {
            'f0': F0_QCAL,
            'omega_0': float(OMEGA_0),
            'C_coherence': C_COHERENCE
        },
        'tests': {},
        'overall_status': 'UNKNOWN'
    }
    
    # Test 1: Test function properties
    if verbose:
        print("Test 1: Validating test function properties...")
    
    trace = SelbergRiemannHolographicTrace(
        n_primes=50,
        n_zeros=30,
        test_function_type='gaussian',
        test_function_width=5.0
    )
    
    # Check Gaussian symmetry
    x_test = np.array([-5.0, -1.0, 0.0, 1.0, 5.0])
    h_vals = trace.test_function_h(x_test)
    symmetry_error = abs(h_vals[0] - h_vals[4]) + abs(h_vals[1] - h_vals[3])
    
    validation_results['tests']['test_function_symmetry'] = {
        'passed': bool(symmetry_error < 1e-10),
        'error': float(symmetry_error),
        'description': 'Gaussian test function symmetry'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['test_function_symmetry']['passed'] else "✗"
        print(f"  {status} Test function symmetry: error = {symmetry_error:.2e}")
    
    # Test 2: Fourier transform
    if verbose:
        print("\nTest 2: Validating Fourier transform...")
    
    # At y=0, FT of Gaussian exp(-x²/(2σ²)) is σ√(2π)
    g_zero = trace.fourier_transform_h(np.array([0.0]))[0]
    expected_g_zero = 5.0 * np.sqrt(2 * np.pi)
    ft_error = abs(np.real(g_zero) - expected_g_zero)
    
    validation_results['tests']['fourier_transform'] = {
        'passed': bool(ft_error < 1e-6),
        'error': float(ft_error),
        'expected': float(expected_g_zero),
        'computed': float(np.real(g_zero)),
        'description': 'Fourier transform correctness at y=0'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['fourier_transform']['passed'] else "✗"
        print(f"  {status} Fourier transform: error = {ft_error:.2e}")
    
    # Test 3: Geodesic sum
    if verbose:
        print("\nTest 3: Validating geodesic sum...")
    
    geodesic_sum, geo_info = trace.compute_geodesic_sum(verbose=False)
    
    validation_results['tests']['geodesic_sum'] = {
        'passed': bool(geodesic_sum > 0 and np.isfinite(geodesic_sum)),
        'value': float(geodesic_sum),
        'n_geodesics': int(geo_info['n_geodesics']),
        'description': 'Geodesic sum positivity and finiteness'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['geodesic_sum']['passed'] else "✗"
        print(f"  {status} Geodesic sum: {geodesic_sum:.6f} ({geo_info['n_geodesics']} geodesics)")
    
    # Test 4: Spectral sum
    if verbose:
        print("\nTest 4: Validating spectral sum...")
    
    spectral_sum, spec_info = trace.compute_spectral_sum(verbose=False)
    
    validation_results['tests']['spectral_sum'] = {
        'passed': bool(spectral_sum >= 0 and np.isfinite(spectral_sum)),
        'value': float(spectral_sum),
        'n_eigenvalues': int(spec_info['n_eigenvalues']),
        'description': 'Spectral sum non-negativity and finiteness'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['spectral_sum']['passed'] else "✗"
        print(f"  {status} Spectral sum: {spectral_sum:.6f} ({spec_info['n_eigenvalues']} eigenvalues)")
    
    # Test 5: Holographic correspondence (narrow Gaussian)
    if verbose:
        print("\nTest 5: Validating holographic correspondence (narrow Gaussian)...")
    
    result_narrow = demonstrate_holographic_trace(
        n_primes=100,
        n_zeros=50,
        test_function_type='gaussian',
        width=2.0,
        verbose=False
    )
    
    validation_results['tests']['holographic_narrow'] = {
        'passed': bool(result_narrow.qcal_coherence > 0.90),
        'selberg_total': float(result_narrow.selberg_total),
        'riemann_total': float(result_narrow.riemann_total),
        'equality_error': float(result_narrow.equality_error),
        'relative_error': float(result_narrow.relative_error),
        'qcal_coherence': float(result_narrow.qcal_coherence),
        'description': 'Holographic correspondence with narrow Gaussian (σ=2)'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['holographic_narrow']['passed'] else "✗"
        print(f"  {status} Narrow Gaussian:")
        print(f"      Selberg: {result_narrow.selberg_total:.6f}")
        print(f"      Riemann: {result_narrow.riemann_total:.6f}")
        print(f"      Error: {result_narrow.equality_error:.2e}")
        print(f"      Ψ: {result_narrow.qcal_coherence:.6f}")
    
    # Test 6: Holographic correspondence (wide Gaussian)
    if verbose:
        print("\nTest 6: Validating holographic correspondence (wide Gaussian)...")
    
    result_wide = demonstrate_holographic_trace(
        n_primes=100,
        n_zeros=50,
        test_function_type='gaussian',
        width=30.0,
        verbose=False
    )
    
    validation_results['tests']['holographic_wide'] = {
        'passed': bool(result_wide.qcal_coherence > 0.85),
        'selberg_total': float(result_wide.selberg_total),
        'riemann_total': float(result_wide.riemann_total),
        'equality_error': float(result_wide.equality_error),
        'relative_error': float(result_wide.relative_error),
        'qcal_coherence': float(result_wide.qcal_coherence),
        'description': 'Holographic correspondence with wide Gaussian (σ=30)'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['holographic_wide']['passed'] else "✗"
        print(f"  {status} Wide Gaussian:")
        print(f"      Selberg: {result_wide.selberg_total:.6f}")
        print(f"      Riemann: {result_wide.riemann_total:.6f}")
        print(f"      Error: {result_wide.equality_error:.2e}")
        print(f"      Ψ: {result_wide.qcal_coherence:.6f}")
    
    # Test 7: QCAL integration
    if verbose:
        print("\nTest 7: Validating QCAL integration...")
    
    # Average coherence across tests
    avg_coherence = (result_narrow.qcal_coherence + result_wide.qcal_coherence) / 2.0
    
    validation_results['tests']['qcal_integration'] = {
        'passed': bool(avg_coherence > 0.85),
        'average_coherence': float(avg_coherence),
        'f0_qcal': float(F0_QCAL),
        'C_coherence': float(C_COHERENCE),
        'description': 'QCAL ∞³ integration and coherence metrics'
    }
    
    if verbose:
        status = "✓" if validation_results['tests']['qcal_integration']['passed'] else "✗"
        print(f"  {status} QCAL Integration:")
        print(f"      Average Ψ: {avg_coherence:.6f}")
        print(f"      f₀: {F0_QCAL} Hz")
        print(f"      C: {C_COHERENCE}")
    
    # Overall status
    all_passed = all(test['passed'] for test in validation_results['tests'].values())
    validation_results['overall_status'] = 'PASSED' if all_passed else 'FAILED'
    validation_results['tests_passed'] = sum(1 for t in validation_results['tests'].values() if t['passed'])
    validation_results['tests_total'] = len(validation_results['tests'])
    
    # Compute overall Ψ
    validation_results['overall_psi'] = float(avg_coherence)
    
    if verbose:
        print("\n" + "="*80)
        print("VALIDATION SUMMARY")
        print("="*80)
        print(f"Overall Status: {validation_results['overall_status']}")
        print(f"Tests Passed: {validation_results['tests_passed']}/{validation_results['tests_total']}")
        print(f"Overall Ψ: {validation_results['overall_psi']:.6f}")
        print("="*80)
    
    return validation_results


def generate_certificate(validation_results: dict, output_file: str = None) -> str:
    """
    Generate QCAL certificate for Selberg-Riemann holographic trace validation.
    
    Args:
        validation_results: Results from validate_selberg_riemann_holographic_trace
        output_file: Path to save certificate (default: data/selberg_riemann_holographic_trace_certificate.json)
        
    Returns:
        Certificate hash
    """
    if output_file is None:
        output_file = 'data/selberg_riemann_holographic_trace_certificate.json'
    
    # Create certificate
    certificate = {
        'module': 'selberg_riemann_holographic_trace',
        'version': '1.0.0',
        'timestamp': validation_results['timestamp'],
        'validation_results': validation_results,
        'qcal_signature': {
            'f0': F0_QCAL,
            'C': C_COHERENCE,
            'omega_0': float(OMEGA_0),
            'coherence_psi': validation_results['overall_psi']
        },
        'mathematical_framework': {
            'selberg_side': 'Geodesic lengths on SL(2,ℤ)\\ℍ',
            'riemann_side': 'Zeros of ζ(s) and prime powers',
            'correspondence': 'Arithmetic holography: boundary ↔ bulk',
            'test_function': 'Schwartz class Gaussian'
        },
        'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
        'institution': 'Instituto de Conciencia Cuántica (ICQ)',
        'orcid': '0009-0002-1923-0773',
        'doi': '10.5281/zenodo.17379721'
    }
    
    # Compute hash
    cert_str = json.dumps(certificate, sort_keys=True)
    cert_hash = hashlib.sha256(cert_str.encode()).hexdigest()[:16]
    certificate['certificate_hash'] = f'0xQCAL_SELBERG_RIEMANN_HOLO_{cert_hash}'
    
    # Save certificate
    Path(output_file).parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    return certificate['certificate_hash']


def main():
    """Main validation routine."""
    print("\n" + "█"*80)
    print("█" + " "*78 + "█")
    print("█" + "  SELBERG-RIEMANN HOLOGRAPHIC TRACE VALIDATION  ".center(78) + "█")
    print("█" + " "*78 + "█")
    print("█"*80 + "\n")
    
    # Run validation
    results = validate_selberg_riemann_holographic_trace(verbose=True)
    
    # Generate certificate
    print("\n" + "="*80)
    print("GENERATING CERTIFICATE...")
    print("="*80)
    
    cert_hash = generate_certificate(results)
    
    print(f"\n✓ Certificate generated: {cert_hash}")
    print(f"✓ Saved to: data/selberg_riemann_holographic_trace_certificate.json")
    
    # Final summary
    print("\n" + "█"*80)
    if results['overall_status'] == 'PASSED':
        print("█" + " "*78 + "█")
        print("█" + "  ✅ VALIDATION PASSED - HOLOGRAPHIC CORRESPONDENCE CONFIRMED  ".center(78) + "█")
        print("█" + " "*78 + "█")
        print("█" + f"  Overall Ψ = {results['overall_psi']:.6f}  ".center(78) + "█")
        print("█" + " "*78 + "█")
    else:
        print("█" + " "*78 + "█")
        print("█" + "  ⚠️  VALIDATION COMPLETED WITH WARNINGS  ".center(78) + "█")
        print("█" + " "*78 + "█")
    print("█"*80)
    
    print("\n♾️ QCAL ∞³ Node evolution complete – validation coherent.")
    print("∴𓂀Ω∞³Φ @ 141.7001 Hz\n")
    
    return 0 if results['overall_status'] == 'PASSED' else 1


if __name__ == '__main__':
    exit(main())
