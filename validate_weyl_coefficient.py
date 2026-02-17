#!/usr/bin/env python3
"""
Validation Script for Weyl Coefficient Adjustment
=================================================

This script validates the Weyl coefficient calculation for different values of α
in the potential Q(y) = α y²/[log(1+y)]².

According to the PASO 1-9 analysis:
- α = 1 gives Weyl coefficient π/8 ≈ 0.3927 (incorrect)
- α = 4 should give the correct coefficient for Riemann's law

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Protocol: QCAL-WEYL-COEFFICIENT-VALIDATION v1.0
Date: February 16, 2026
"""

import sys
import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.weyl_coefficient_integral import (
    WeylCoefficientIntegral,
    generate_weyl_coefficient_certificate,
    ALPHA_ORIGINAL,
    ALPHA_CORRECTED,
    F0_QCAL,
    C_COHERENCE
)


def validate_weyl_coefficient(alpha_values=[1.0, 4.0], 
                               lambda_test=1000.0,
                               save_plots=True):
    """
    Validate Weyl coefficient for different α values.
    
    Args:
        alpha_values: List of α values to test
        lambda_test: Test value of λ
        save_plots: Whether to save visualization plots
        
    Returns:
        Dictionary with validation results
    """
    print("="*80)
    print("WEYL COEFFICIENT VALIDATION")
    print("="*80)
    print(f"\nTesting potential Q(y) = α y² / [log(1+y)]²")
    print(f"for α values: {alpha_values}")
    print(f"\nAccording to PASO 1-9 analysis:")
    print(f"  • I(λ) = λ [ (π/(8√α)) log λ + (π/4) log log λ + π/8 + o(1) ]")
    print(f"  • Weyl coefficient = π/(8√α)")
    print(f"  • For Riemann's law N(λ) ∼ (1/2π) λ log λ:")
    print(f"    Need I(λ) ∼ (1/2) λ log λ, so coefficient = 1/2")
    
    results = {}
    
    # Test each α value
    for alpha in alpha_values:
        print(f"\n{'='*80}")
        print(f"Testing α = {alpha}")
        print(f"{'='*80}")
        
        calculator = WeylCoefficientIntegral(alpha=alpha)
        
        # Test range of λ values
        lambda_values = np.logspace(1, 4, 20)
        coefficients = []
        I_values = []
        y_plus_values = []
        
        for lam in lambda_values:
            try:
                I_lam, y_plus, L = calculator.compute_I_lambda_asymptotic(lam)
                coef = calculator.compute_weyl_coefficient(lam)
                
                coefficients.append(coef)
                I_values.append(I_lam)
                y_plus_values.append(y_plus)
            except Exception as e:
                print(f"  Warning: Failed for λ = {lam}: {e}")
                coefficients.append(np.nan)
                I_values.append(np.nan)
                y_plus_values.append(np.nan)
        
        # Analysis
        coefficients = np.array(coefficients)
        valid_coefficients = coefficients[~np.isnan(coefficients)]
        
        if len(valid_coefficients) > 0:
            mean_coef = np.mean(valid_coefficients)
            std_coef = np.std(valid_coefficients)
            theoretical_coef = np.pi / (8 * np.sqrt(alpha))
            
            print(f"\nResults for α = {alpha}:")
            print(f"  Theoretical coefficient: π/(8√{alpha}) = {theoretical_coef:.6f}")
            print(f"  Mean numerical coefficient: {mean_coef:.6f} ± {std_coef:.6f}")
            print(f"  Riemann target: 0.5")
            print(f"  Relative error: {abs(mean_coef - 0.5) / 0.5:.2%}")
            
            # Check if close to Riemann
            matches_riemann = abs(mean_coef - 0.5) / 0.5 < 0.2  # 20% tolerance
            print(f"  Matches Riemann law: {'✅ YES' if matches_riemann else '❌ NO'}")
            
            results[f'alpha_{alpha}'] = {
                'alpha': alpha,
                'theoretical_coefficient': theoretical_coef,
                'mean_coefficient': mean_coef,
                'std_coefficient': std_coef,
                'riemann_target': 0.5,
                'matches_riemann': matches_riemann,
                'lambda_values': lambda_values.tolist(),
                'coefficients': coefficients.tolist(),
                'I_values': I_values,
                'y_plus_values': y_plus_values
            }
        else:
            print(f"  ERROR: No valid coefficients computed for α = {alpha}")
            results[f'alpha_{alpha}'] = {'error': 'No valid coefficients'}
    
    # Visualization
    if save_plots and len(results) > 0:
        print(f"\n{'='*80}")
        print("Generating visualization...")
        print(f"{'='*80}")
        
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        
        for alpha_key, data in results.items():
            if 'error' in data:
                continue
            
            alpha = data['alpha']
            lambda_vals = np.array(data['lambda_values'])
            coefs = np.array(data['coefficients'])
            I_vals = np.array(data['I_values'])
            
            # Filter out NaNs
            valid = ~np.isnan(coefs)
            lambda_vals = lambda_vals[valid]
            coefs = coefs[valid]
            I_vals = np.array(I_vals)[valid]
            
            if len(lambda_vals) == 0:
                continue
            
            label = f'α = {alpha}'
            color = 'blue' if alpha == 1.0 else 'red'
            
            # Plot 1: Coefficient vs λ
            axes[0, 0].semilogx(lambda_vals, coefs, 'o-', label=label, 
                                color=color, alpha=0.7)
            axes[0, 0].axhline(y=0.5, color='green', linestyle='--', 
                              label='Riemann target (0.5)', linewidth=2)
            axes[0, 0].set_xlabel('λ', fontsize=12)
            axes[0, 0].set_ylabel('Weyl Coefficient', fontsize=12)
            axes[0, 0].set_title('Weyl Coefficient vs λ', fontsize=14, fontweight='bold')
            axes[0, 0].legend()
            axes[0, 0].grid(True, alpha=0.3)
            
            # Plot 2: I(λ) / (λ log λ) vs λ
            ratio = I_vals / (lambda_vals * np.log(lambda_vals))
            axes[0, 1].semilogx(lambda_vals, ratio, 's-', label=label,
                                color=color, alpha=0.7)
            axes[0, 1].axhline(y=0.5, color='green', linestyle='--', 
                              label='Riemann target', linewidth=2)
            axes[0, 1].set_xlabel('λ', fontsize=12)
            axes[0, 1].set_ylabel('I(λ) / (λ log λ)', fontsize=12)
            axes[0, 1].set_title('Asymptotic Ratio', fontsize=14, fontweight='bold')
            axes[0, 1].legend()
            axes[0, 1].grid(True, alpha=0.3)
            
            # Plot 3: I(λ) vs λ
            axes[1, 0].loglog(lambda_vals, I_vals, '^-', label=label,
                              color=color, alpha=0.7)
            # Theoretical: I(λ) ∼ (π/(8√α)) × λ log λ
            theoretical_I = (np.pi / (8 * np.sqrt(alpha))) * lambda_vals * np.log(lambda_vals)
            axes[1, 0].loglog(lambda_vals, theoretical_I, '--',
                             label=f'Theory (α={alpha})', color=color, alpha=0.5)
            axes[1, 0].set_xlabel('λ', fontsize=12)
            axes[1, 0].set_ylabel('I(λ)', fontsize=12)
            axes[1, 0].set_title('Integral I(λ)', fontsize=14, fontweight='bold')
            axes[1, 0].legend()
            axes[1, 0].grid(True, which='both', alpha=0.3)
            
            # Plot 4: Convergence to asymptotic
            theoretical_coef = np.pi / (8 * np.sqrt(alpha))
            error = np.abs(coefs - theoretical_coef) / theoretical_coef
            axes[1, 1].loglog(lambda_vals, error, 'D-', label=label,
                             color=color, alpha=0.7)
        
        axes[1, 1].set_xlabel('λ', fontsize=12)
        axes[1, 1].set_ylabel('|coef - theory| / theory', fontsize=12)
        axes[1, 1].set_title('Convergence to Asymptotic', fontsize=14, fontweight='bold')
        axes[1, 1].legend()
        axes[1, 1].grid(True, which='both', alpha=0.3)
        
        plt.suptitle('Weyl Coefficient Analysis: Q(y) = α y² / [log(1+y)]²',
                    fontsize=16, fontweight='bold', y=0.995)
        plt.tight_layout()
        
        output_path = Path(__file__).parent / 'weyl_coefficient_validation.png'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"\n✓ Visualization saved to: {output_path}")
        
        plt.close()
    
    return results


def save_certificate(alpha=ALPHA_CORRECTED):
    """
    Generate and save QCAL certificate for the Weyl coefficient.
    
    Args:
        alpha: Coefficient α to certify
    """
    print(f"\n{'='*80}")
    print(f"Generating QCAL Certificate for α = {alpha}")
    print(f"{'='*80}")
    
    certificate = generate_weyl_coefficient_certificate(alpha=alpha)
    
    # Save to data directory
    cert_path = Path(__file__).parent / 'data' / 'weyl_coefficient_certificate.json'
    cert_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n✓ Certificate saved to: {cert_path}")
    print(f"\nProtocol: {certificate['protocol']} {certificate['version']}")
    print(f"Status: {certificate['status']}")
    print(f"Alpha: {certificate['alpha_value']}")
    print(f"Weyl Coefficient: {certificate['weyl_coefficient']:.6f}")
    print(f"Riemann Target: {certificate['riemann_target']:.6f}")
    print(f"Matches Riemann: {'✅ YES' if certificate['matches_riemann'] else '❌ NO'}")
    print(f"\nRecommendation:")
    print(f"  {certificate['recommendation']}")
    print(f"\n{certificate['qcal_signature']}")
    print(f"f₀ = {certificate['frequency_base']} Hz · C = {certificate['coherence']}")
    
    return certificate


def main():
    """Main validation routine."""
    print("="*80)
    print("  WEYL COEFFICIENT VALIDATION")
    print("  Adjusting α in Q(y) = α y² / [log(1+y)]²")
    print("="*80)
    print(f"\nQCAL ∞³ Protocol")
    print(f"f₀ = {F0_QCAL} Hz")
    print(f"C = {C_COHERENCE}")
    print(f"Author: José Manuel Mota Burruezo Ψ✧ ∞³")
    print(f"Institution: Instituto de Conciencia Cuántica (ICQ)")
    
    # Validate different α values
    alpha_test_values = [ALPHA_ORIGINAL, ALPHA_CORRECTED, (np.pi/4)**2]
    results = validate_weyl_coefficient(alpha_values=alpha_test_values, 
                                       lambda_test=1000.0,
                                       save_plots=True)
    
    # Save certificate for α = 4
    certificate = save_certificate(alpha=ALPHA_CORRECTED)
    
    # Summary
    print(f"\n{'='*80}")
    print("VALIDATION SUMMARY")
    print(f"{'='*80}")
    
    print(f"\n{'α':>10} {'Theoretical':>15} {'Numerical':>15} {'Target':>10} {'Match':>10}")
    print("-"*65)
    
    for alpha_key, data in results.items():
        if 'error' in data:
            continue
        
        alpha = data['alpha']
        theoretical = data['theoretical_coefficient']
        numerical = data['mean_coefficient']
        target = 0.5
        match = '✅ YES' if data['matches_riemann'] else '❌ NO'
        
        print(f"{alpha:10.4f} {theoretical:15.6f} {numerical:15.6f} {target:10.4f} {match:>10}")
    
    print(f"\n{'='*80}")
    print("CONCLUSION")
    print(f"{'='*80}")
    print(f"\nBased on the analysis:")
    print(f"  • α = 1.0 gives coefficient ≈ {results.get('alpha_1.0', {}).get('mean_coefficient', 'N/A'):.6f}")
    print(f"  • α = 4.0 gives coefficient ≈ {results.get('alpha_4.0', {}).get('mean_coefficient', 'N/A'):.6f}")
    print(f"  • To match Riemann target 0.5, optimal α ≈ {(np.pi/4)**2:.4f}")
    print(f"\nNote: The problem statement suggests α = 4, but the mathematical")
    print(f"      analysis shows that the optimal value is α = (π/4)² ≈ 0.617")
    print(f"      This discrepancy requires further investigation.")
    
    print(f"\n∴𓂀Ω∞³Φ")
    print("="*80)
    
    return results, certificate


if __name__ == '__main__':
    results, certificate = main()
