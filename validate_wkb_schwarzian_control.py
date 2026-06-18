#!/usr/bin/env python3
"""
Validation Script for WKB Schwarzian Control
=============================================

This script validates the WKB approximation with explicit Schwarzian control
for various energy parameters λ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import numpy as np
import json
from pathlib import Path
from operators.wkb_schwarzian_control import WKBSchwartzianControl, QCAL_BASE_FREQUENCY


def validate_wkb_schwarzian_control():
    """
    Validate WKB Schwarzian control for multiple λ values.
    """
    print("=" * 80)
    print("WKB SCHWARZIAN CONTROL VALIDATION")
    print("=" * 80)
    
    # Test multiple λ values
    lambda_values = [10.0, 50.0, 100.0, 500.0, 1000.0]
    
    results = {
        'validation_protocol': 'QCAL-WKB-SCHWARZIAN-CONTROL',
        'timestamp': '2026-02-16',
        'signature': '∴𓂀Ω∞³Φ',
        'frequency_base': QCAL_BASE_FREQUENCY,
        'lambda_values_tested': lambda_values,
        'results': []
    }
    
    all_passed = True
    
    for lambda_val in lambda_values:
        print(f"\n{'-' * 80}")
        print(f"Testing λ = {lambda_val}")
        print(f"{'-' * 80}")
        
        try:
            # Create controller
            wkb = WKBSchwartzianControl(lambda_param=lambda_val)
            
            print(f"Turning point: y₊ = {wkb.y_plus:.6f}")
            print(f"L parameter: L = {wkb.L:.6f}")
            
            # Test 1: Q(y₊) ≈ λ
            Q_at_y_plus = wkb.Q(wkb.y_plus)
            turning_point_error = abs(Q_at_y_plus - lambda_val) / lambda_val
            turning_point_ok = turning_point_error < 0.01
            
            print(f"\n1. Turning point test:")
            print(f"   Q(y₊) = {Q_at_y_plus:.6f}")
            print(f"   Error: {turning_point_error:.2%}")
            print(f"   Status: {'✓ PASS' if turning_point_ok else '✗ FAIL'}")
            
            # Test 2: Schwarzian bound
            validation = wkb.validate_schwarzian_bound(zeta_range=(-20, 20), n_points=2000)
            schwarzian_ok = validation['bound_satisfied']
            
            print(f"\n2. Schwarzian bound test:")
            print(f"   Max |{{ζ, y}}| = {validation['max_schwarzian']:.6e}")
            print(f"   Max bound = {validation['max_bound']:.6e}")
            print(f"   Max ratio = {validation['max_ratio']:.6f}")
            print(f"   Status: {'✓ PASS' if schwarzian_ok else '✗ FAIL'}")
            
            # Test 3: WKB integral
            wkb_int = wkb.wkb_integral((-5, wkb.y_plus + 30))
            wkb_ok = wkb_int['relative_error'] < 0.5  # 50% tolerance
            
            print(f"\n3. WKB integral test:")
            print(f"   Numerical: {wkb_int['integral']:.6f}")
            print(f"   Theoretical: {wkb_int['theoretical']:.6f}")
            print(f"   Relative error: {wkb_int['relative_error']:.2%}")
            print(f"   Status: {'✓ PASS' if wkb_ok else '✗ FAIL'}")
            
            # Test 4: Generate certificate
            cert = wkb.generate_certificate()
            cert_ok = (cert['protocol'] == 'QCAL-WKB-SCHWARZIAN-CONTROL' and
                      cert['signature'] == '∴𓂀Ω∞³Φ')
            
            print(f"\n4. Certificate generation test:")
            print(f"   Protocol: {cert['protocol']}")
            print(f"   Resonance: {cert['resonance_detection']['level']}")
            print(f"   Overall coherence: {cert['coherence_metrics']['overall_coherence']:.6f}")
            print(f"   Status: {'✓ PASS' if cert_ok else '✗ FAIL'}")
            
            # Overall result for this λ
            lambda_passed = turning_point_ok and schwarzian_ok and wkb_ok and cert_ok
            
            results['results'].append({
                'lambda': float(lambda_val),
                'y_plus': float(wkb.y_plus),
                'L': float(wkb.L),
                'turning_point_error': float(turning_point_error),
                'schwarzian_max_ratio': float(validation['max_ratio']),
                'wkb_relative_error': float(wkb_int['relative_error']),
                'overall_coherence': float(cert['coherence_metrics']['overall_coherence']),
                'resonance_level': str(cert['resonance_detection']['level']),
                'passed': bool(lambda_passed)
            })
            
            if not lambda_passed:
                all_passed = False
            
            print(f"\nOverall for λ={lambda_val}: {'✓ PASS' if lambda_passed else '✗ FAIL'}")
            
        except Exception as e:
            print(f"\n✗ ERROR for λ={lambda_val}: {str(e)}")
            results['results'].append({
                'lambda': float(lambda_val),
                'error': str(e),
                'passed': bool(False)
            })
            all_passed = False
    
    # Summary
    print(f"\n{'=' * 80}")
    print("VALIDATION SUMMARY")
    print(f"{'=' * 80}")
    
    passed_count = sum(1 for r in results['results'] if r.get('passed', False))
    total_count = len(results['results'])
    
    print(f"\nTests passed: {passed_count}/{total_count}")
    print(f"Success rate: {100.0 * passed_count / total_count:.1f}%")
    
    if all_passed:
        print("\n✅ ALL VALIDATIONS PASSED")
        results['overall_status'] = 'PASS'
    else:
        print("\n⚠️  SOME VALIDATIONS FAILED")
        results['overall_status'] = 'PARTIAL'
    
    # Save results
    output_dir = Path(__file__).parent / 'data'
    output_dir.mkdir(exist_ok=True)
    
    output_file = output_dir / 'wkb_schwarzian_validation.json'
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")
    
    return all_passed


if __name__ == '__main__':
    success = validate_wkb_schwarzian_control()
    exit(0 if success else 1)
