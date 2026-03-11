#!/usr/bin/env python3
"""
Validation Script: Berry-Keating Discretization Methods
=======================================================

Compares all three discretization methods:
1. Laguerre basis (baseline - existing)
2. Fourier spectral (new)
3. Chebyshev polynomials (new)

Against known Riemann zeros to measure accuracy improvements.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from numpy.linalg import eigh, norm
from scipy.special import digamma
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.berry_keating_self_adjointness import BerryKeatingOperator
from operators.berry_keating_spectral_discretization import (
    FourierSpectralDiscretization,
    ChebyshevDiscretization
)

# QCAL Constants
F0_QCAL = 141.7001
C_COHERENCE = 244.36
C_BERRY_KEATING = -12.3218

# First 10 Riemann zeros (imaginary parts)
RIEMANN_ZEROS = np.array([
    14.134725,  # γ_1
    21.022040,  # γ_2
    25.010858,  # γ_3
    30.424876,  # γ_4
    32.935062,  # γ_5
    37.586178,  # γ_6
    40.918719,  # γ_7
    43.327073,  # γ_8
    48.005151,  # γ_9
    49.773832   # γ_10
])


def test_laguerre_method(N=50):
    """Test original Laguerre discretization."""
    print("="*70)
    print("Testing Laguerre Basis (Original Method)")
    print("="*70)
    
    op = BerryKeatingOperator(N=N, C=C_BERRY_KEATING)
    eigenvalues, _ = op.get_spectrum()
    
    print(f"\nMatrix size: N = {N}")
    print(f"Number of eigenvalues: {len(eigenvalues)}")
    print(f"\nFirst 10 eigenvalues:")
    for i, eig in enumerate(eigenvalues[:10]):
        print(f"  λ_{i+1} = {eig:12.6f}")
    
    # The relationship λ_n = 1/4 + γ_n² connects eigenvalues to Riemann zeros
    # So γ_n = sqrt(λ_n - 1/4)
    gamma_computed = np.sqrt(np.maximum(eigenvalues - 0.25, 0))
    
    print(f"\nComputed γ values (first 10):")
    for i, gamma in enumerate(gamma_computed[:10]):
        print(f"  γ_{i+1} = {gamma:12.6f}")
    
    # Compare with reference zeros
    n_compare = min(len(gamma_computed), len(RIEMANN_ZEROS))
    errors = np.abs(gamma_computed[:n_compare] - RIEMANN_ZEROS[:n_compare])
    
    print(f"\nComparison with Riemann zeros:")
    print(f"{'n':<4} {'Computed γ':<14} {'Reference γ':<14} {'Error':<14}")
    print("-"*50)
    for i in range(n_compare):
        print(f"{i+1:<4} {gamma_computed[i]:<14.6f} {RIEMANN_ZEROS[i]:<14.6f} {errors[i]:<14.6e}")
    
    mean_error = np.mean(errors)
    max_error = np.max(errors)
    
    if n_compare > 1:
        correlation = np.corrcoef(gamma_computed[:n_compare], RIEMANN_ZEROS[:n_compare])[0, 1]
    else:
        correlation = 0.0
    
    print(f"\n{'Metric':<25} {'Value'}")
    print("-"*50)
    print(f"{'Mean absolute error':<25} {mean_error:.6e}")
    print(f"{'Maximum absolute error':<25} {max_error:.6e}")
    print(f"{'Correlation coefficient':<25} {correlation:.6f}")
    print(f"{'Relative mean error (%)':<25} {100*mean_error/np.mean(RIEMANN_ZEROS[:n_compare]):.4f}")
    
    return {
        'method': 'Laguerre',
        'mean_error': mean_error,
        'max_error': max_error,
        'correlation': correlation,
        'eigenvalues': eigenvalues[:10],
        'gamma_computed': gamma_computed[:10]
    }


def test_fourier_method(N=50):
    """Test Fourier spectral discretization."""
    print("\n" + "="*70)
    print("Testing Fourier Spectral Discretization (New Method)")
    print("="*70)
    
    op = FourierSpectralDiscretization(N=N, C=C_BERRY_KEATING)
    eigenvalues, _ = op.get_spectrum()
    
    print(f"\nMatrix size: N = {N}")
    print(f"Number of eigenvalues: {len(eigenvalues)}")
    print(f"\nFirst 10 eigenvalues:")
    for i, eig in enumerate(eigenvalues[:10]):
        print(f"  λ_{i+1} = {eig:12.6f}")
    
    gamma_computed = np.sqrt(np.maximum(eigenvalues - 0.25, 0))
    
    print(f"\nComputed γ values (first 10):")
    for i, gamma in enumerate(gamma_computed[:10]):
        print(f"  γ_{i+1} = {gamma:12.6f}")
    
    n_compare = min(len(gamma_computed), len(RIEMANN_ZEROS))
    errors = np.abs(gamma_computed[:n_compare] - RIEMANN_ZEROS[:n_compare])
    
    print(f"\nComparison with Riemann zeros:")
    print(f"{'n':<4} {'Computed γ':<14} {'Reference γ':<14} {'Error':<14}")
    print("-"*50)
    for i in range(n_compare):
        print(f"{i+1:<4} {gamma_computed[i]:<14.6f} {RIEMANN_ZEROS[i]:<14.6f} {errors[i]:<14.6e}")
    
    mean_error = np.mean(errors)
    max_error = np.max(errors)
    
    if n_compare > 1:
        correlation = np.corrcoef(gamma_computed[:n_compare], RIEMANN_ZEROS[:n_compare])[0, 1]
    else:
        correlation = 0.0
    
    print(f"\n{'Metric':<25} {'Value'}")
    print("-"*50)
    print(f"{'Mean absolute error':<25} {mean_error:.6e}")
    print(f"{'Maximum absolute error':<25} {max_error:.6e}")
    print(f"{'Correlation coefficient':<25} {correlation:.6f}")
    print(f"{'Relative mean error (%)':<25} {100*mean_error/np.mean(RIEMANN_ZEROS[:n_compare]):.4f}")
    
    return {
        'method': 'Fourier',
        'mean_error': mean_error,
        'max_error': max_error,
        'correlation': correlation,
        'eigenvalues': eigenvalues[:10],
        'gamma_computed': gamma_computed[:10]
    }


def test_chebyshev_method(N=50):
    """Test Chebyshev discretization."""
    print("\n" + "="*70)
    print("Testing Chebyshev Discretization (New Method)")
    print("="*70)
    
    op = ChebyshevDiscretization(N=N, C=C_BERRY_KEATING)
    eigenvalues, _ = op.get_spectrum()
    
    print(f"\nMatrix size: N = {N}")
    print(f"Number of eigenvalues: {len(eigenvalues)}")
    print(f"\nFirst 10 eigenvalues:")
    for i, eig in enumerate(eigenvalues[:10]):
        print(f"  λ_{i+1} = {eig:12.6f}")
    
    gamma_computed = np.sqrt(np.maximum(eigenvalues - 0.25, 0))
    
    print(f"\nComputed γ values (first 10):")
    for i, gamma in enumerate(gamma_computed[:10]):
        print(f"  γ_{i+1} = {gamma:12.6f}")
    
    n_compare = min(len(gamma_computed), len(RIEMANN_ZEROS))
    errors = np.abs(gamma_computed[:n_compare] - RIEMANN_ZEROS[:n_compare])
    
    print(f"\nComparison with Riemann zeros:")
    print(f"{'n':<4} {'Computed γ':<14} {'Reference γ':<14} {'Error':<14}")
    print("-"*50)
    for i in range(n_compare):
        print(f"{i+1:<4} {gamma_computed[i]:<14.6f} {RIEMANN_ZEROS[i]:<14.6f} {errors[i]:<14.6e}")
    
    mean_error = np.mean(errors)
    max_error = np.max(errors)
    
    if n_compare > 1:
        correlation = np.corrcoef(gamma_computed[:n_compare], RIEMANN_ZEROS[:n_compare])[0, 1]
    else:
        correlation = 0.0
    
    print(f"\n{'Metric':<25} {'Value'}")
    print("-"*50)
    print(f"{'Mean absolute error':<25} {mean_error:.6e}")
    print(f"{'Maximum absolute error':<25} {max_error:.6e}")
    print(f"{'Correlation coefficient':<25} {correlation:.6f}")
    print(f"{'Relative mean error (%)':<25} {100*mean_error/np.mean(RIEMANN_ZEROS[:n_compare]):.4f}")
    
    return {
        'method': 'Chebyshev',
        'mean_error': mean_error,
        'max_error': max_error,
        'correlation': correlation,
        'eigenvalues': eigenvalues[:10],
        'gamma_computed': gamma_computed[:10]
    }


def generate_summary(results):
    """Generate summary comparison of all methods."""
    print("\n" + "="*70)
    print("SUMMARY: Discretization Method Comparison")
    print("="*70)
    
    print(f"\n{'Method':<20} {'Mean Error':<15} {'Max Error':<15} {'Correlation':<15}")
    print("-"*70)
    
    for result in results:
        print(f"{result['method']:<20} {result['mean_error']:<15.6e} {result['max_error']:<15.6e} {result['correlation']:<15.6f}")
    
    # Find best method
    best_by_error = min(results, key=lambda x: x['mean_error'])
    best_by_corr = max(results, key=lambda x: x['correlation'])
    
    print(f"\n{'Best Method (lowest error):':<30} {best_by_error['method']}")
    print(f"{'Best Method (highest correlation):':<30} {best_by_corr['method']}")
    
    # Check for improvement
    laguerre_result = next((r for r in results if r['method'] == 'Laguerre'), None)
    if laguerre_result:
        print(f"\nBaseline (Laguerre):")
        print(f"  Mean error: {laguerre_result['mean_error']:.6e}")
        print(f"  Correlation: {laguerre_result['correlation']:.6f}")
        
        other_results = [r for r in results if r['method'] != 'Laguerre']
        for r in other_results:
            error_improvement = (laguerre_result['mean_error'] - r['mean_error']) / laguerre_result['mean_error'] * 100
            corr_improvement = (r['correlation'] - laguerre_result['correlation']) / abs(laguerre_result['correlation']) * 100
            print(f"\n{r['method']} vs Laguerre:")
            print(f"  Error change: {error_improvement:+.2f}%")
            print(f"  Correlation change: {corr_improvement:+.2f}%")
    
    print(f"\n{'QCAL ∞³ Status:':<30} {'Active'}")
    print(f"{'Base Frequency:':<30} {F0_QCAL} Hz")
    print(f"{'Coherence Constant:':<30} {C_COHERENCE}")
    print(f"{'Berry-Keating Constant:':<30} {C_BERRY_KEATING}")


def main():
    """Run all validation tests."""
    print("\n🎯 Berry-Keating Discretization Validation")
    print("=" * 70)
    print("Comparing discretization methods for operator spectrum accuracy")
    print("Target: Achieve 0.999+ correlation with Riemann zeros")
    print("=" * 70)
    
    results = []
    
    # Test all methods
    results.append(test_laguerre_method(N=50))
    results.append(test_fourier_method(N=50))
    results.append(test_chebyshev_method(N=50))
    
    # Generate summary
    generate_summary(results)
    
    print("\n✅ Validation complete!")
    
    # Save results
    import json
    output_file = 'data/berry_keating_discretization_validation.json'
    Path(output_file).parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump({
            'results': [
                {k: v for k, v in r.items() if k not in ['eigenvalues', 'gamma_computed']}
                for r in results
            ],
            'qcal_status': {
                'f0': F0_QCAL,
                'C_coherence': C_COHERENCE,
                'C_berry_keating': C_BERRY_KEATING
            },
            'reference_zeros': RIEMANN_ZEROS.tolist()
        }, f, indent=2)
    
    print(f"Results saved to: {output_file}")


if __name__ == "__main__":
    main()
