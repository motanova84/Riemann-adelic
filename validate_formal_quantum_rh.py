#!/usr/bin/env python3
"""
Validation Script for Formal Quantum Mechanical RH Operator
============================================================

Comprehensive validation of the formal quantum mechanical solution to the
Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz
"""

import sys
import os
import json
import numpy as np
from datetime import datetime

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'operators'))

from formal_quantum_rh_operator import (
    FormalQuantumRHOperator,
    HilbertSpaceConfig,
    F0, C_COHERENCE
)


def validate_formal_quantum_rh_operator():
    """
    Complete validation of formal quantum mechanical RH operator.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION: Formal Quantum Mechanical RH Operator")
    print("=" * 80)
    print()
    
    # Initialize operator
    config = HilbertSpaceConfig(x_min=1.0, x_max=60.0, n_grid=300)
    operator = FormalQuantumRHOperator(config)
    
    print("Configuration:")
    print(f"  Hilbert space: L²([{config.x_min}, {config.x_max}), dx/x)")
    print(f"  Grid points: {config.n_grid}")
    print(f"  Phase boundary: θ = {config.phase_theta:.4f}")
    print()
    
    # Run complete verification
    print("Running complete verification...")
    print()
    results = operator.complete_verification(n_eigenvalues=40)
    
    # Extract key metrics
    validation_results = {
        'timestamp': datetime.now().isoformat(),
        'framework': results['framework'],
        'qcal_frequency': results['qcal_frequency'],
        'coherence_constant': results['coherence_constant'],
        'validations': {
            'self_adjoint': results['self_adjointness']['is_self_adjoint'],
            'discrete_spectrum': results['spectrum']['is_discrete'],
            'real_eigenvalues': results['spectrum']['is_real'],
            'weyl_riemann_law': results['counting_function']['weyl_law_verified'],
            'trace_formula': results['trace_formula']['trace_identity_verified']
        },
        'metrics': {
            'hermiticity_error': results['self_adjointness']['hermiticity_error'],
            'n_eigenvalues': results['spectrum']['n_eigenvalues'],
            'spectral_gap': results['spectrum']['spectral_gap'],
            'counting_mean_error': results['counting_function']['mean_relative_error'],
            'trace_identity_error': results['trace_formula']['trace_identity_error']
        },
        'coherence': {
            'Psi_total': results['coherence']['Psi_total'],
            'components': results['coherence']['components'],
            'threshold': results['qcal_validation']['threshold'],
            'passes_threshold': results['qcal_validation']['passes_threshold']
        },
        'first_eigenvalues': results['spectrum']['first_eigenvalues']
    }
    
    # Print validation summary
    print("\n" + "=" * 80)
    print("VALIDATION RESULTS")
    print("=" * 80)
    print()
    
    print("1. Self-Adjointness:")
    print(f"   Status: {'✓ PASS' if validation_results['validations']['self_adjoint'] else '✗ FAIL'}")
    print(f"   Hermiticity error: {validation_results['metrics']['hermiticity_error']:.2e}")
    print()
    
    print("2. Spectral Properties:")
    print(f"   Discrete spectrum: {'✓ PASS' if validation_results['validations']['discrete_spectrum'] else '✗ FAIL'}")
    print(f"   Real eigenvalues: {'✓ PASS' if validation_results['validations']['real_eigenvalues'] else '✗ FAIL'}")
    print(f"   Number of eigenvalues: {validation_results['metrics']['n_eigenvalues']}")
    print(f"   Spectral gap: {validation_results['metrics']['spectral_gap']:.4f}")
    print()
    
    print("3. Weyl-Riemann Counting Law:")
    print(f"   Status: {'✓ PASS' if validation_results['validations']['weyl_riemann_law'] else '✗ FAIL'}")
    print(f"   Mean relative error: {validation_results['metrics']['counting_mean_error']:.4f}")
    print()
    
    print("4. Guinand-Weil Trace Formula:")
    print(f"   Status: {'✓ PASS' if validation_results['validations']['trace_formula'] else '✗ FAIL'}")
    print(f"   Identity error: {validation_results['metrics']['trace_identity_error']:.4f}")
    print()
    
    print("5. Overall Coherence:")
    print(f"   Ψ_total = {validation_results['coherence']['Psi_total']:.4f}")
    print(f"   QCAL threshold (0.888): {'✓ PASS' if validation_results['coherence']['passes_threshold'] else '✗ FAIL'}")
    print()
    
    print("Component Coherences:")
    for component, value in validation_results['coherence']['components'].items():
        print(f"   {component}: {value:.4f}")
    print()
    
    print("First 10 Eigenvalues:")
    for i, ev in enumerate(validation_results['first_eigenvalues'][:10], 1):
        print(f"   γ_{i:2d} = {ev:10.6f}")
    print()
    
    # Overall validation status
    all_validations_pass = all(validation_results['validations'].values())
    coherence_pass = validation_results['coherence']['passes_threshold']
    overall_pass = all_validations_pass and coherence_pass
    
    print("=" * 80)
    print(f"OVERALL STATUS: {'✓ PASS' if overall_pass else '✗ FAIL'}")
    print("=" * 80)
    print()
    
    if overall_pass:
        print("✓ All validations passed successfully")
        print("✓ Formal quantum mechanical RH operator is verified")
        print("✓ QCAL ∞³ coherence threshold met")
    else:
        print("✗ Some validations failed")
        if not all_validations_pass:
            failed = [k for k, v in validation_results['validations'].items() if not v]
            print(f"  Failed validations: {', '.join(failed)}")
        if not coherence_pass:
            print(f"  Coherence below threshold: {validation_results['coherence']['Psi_total']:.4f} < 0.888")
    
    print()
    print("QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print("Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz")
    print("=" * 80)
    
    # Save results to JSON
    output_file = os.path.join(os.path.dirname(__file__), 'data', 'formal_quantum_rh_validation.json')
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(validation_results, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")
    
    return validation_results


if __name__ == "__main__":
    results = validate_formal_quantum_rh_operator()
    
    # Exit with appropriate code
    # Check both coherence threshold and all validations passed
    all_validations_pass = all(results['validations'].values())
    coherence_pass = results['coherence']['passes_threshold']
    
    if all_validations_pass and coherence_pass:
        sys.exit(0)
    else:
        sys.exit(1)
