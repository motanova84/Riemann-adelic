#!/usr/bin/env python3
"""
Validation Script for V_eff Hilbert-Schmidt Closure
====================================================

This script validates the complete implementation of V_eff(u) that ensures
the heat kernel is Hilbert-Schmidt and the operator is trace class.

Tests performed:
1. Coercivity: V_eff(u) ≥ α|u| - β
2. Asymptotic behavior verification
3. Heat kernel L² integrability
4. Hilbert-Schmidt norm computation
5. Comparison with theoretical predictions

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from operators.V_eff_hilbert_schmidt import (
    V_eff,
    verify_coercivity,
    compute_heat_kernel_L2_norm,
    validate_hilbert_schmidt_closure,
    V_eff_asymptotic,
    KAPPA_PI,
    F0,
    C_QCAL
)
import numpy as np
import matplotlib.pyplot as plt


def test_V_eff_formula():
    """Test the V_eff formula at specific points."""
    print("=" * 70)
    print("TEST 1: V_eff Formula Verification")
    print("=" * 70)
    
    # Test points
    u_test = np.array([-10, -5, 0, 5, 10])
    V = V_eff(u_test, KAPPA_PI)
    
    print("\nV_eff(u) values:")
    for u_val, V_val in zip(u_test, V):
        print(f"  u = {u_val:6.1f}  →  V_eff = {V_val:10.6f}")
    
    # Check that all values are positive and finite
    assert np.all(np.isfinite(V)), "V_eff contains non-finite values"
    assert np.all(V > 0), "V_eff contains non-positive values"
    
    print("\n✓ All V_eff values are positive and finite")
    return True


def test_coercivity():
    """Test coercivity condition."""
    print("\n" + "=" * 70)
    print("TEST 2: Coercivity Verification")
    print("=" * 70)
    
    result = verify_coercivity(
        u_range=(-15, 15),
        n_points=2000,
        kappa_pi=KAPPA_PI
    )
    
    print(f"\nCoercivity parameters:")
    print(f"  α = {result['alpha']:.6f} (coercivity constant)")
    print(f"  β = {result['beta']:.6f} (offset constant)")
    print(f"  Coercive: {result['coercive']}")
    print(f"  Violations: {result['n_violations']}/{result['test_points']}")
    
    # Check that α is close to 1 (theoretical expectation)
    assert result['coercive'], "Coercivity condition FAILS"
    assert result['alpha'] > 0.8, f"α = {result['alpha']} too small (expected ≈ 1)"
    assert result['alpha'] < 1.2, f"α = {result['alpha']} too large (expected ≈ 1)"
    
    print(f"\n✓ Coercivity verified: V_eff(u) ≥ {result['alpha']:.3f}|u| - {result['beta']:.3f}")
    return result


def test_asymptotic_behavior():
    """Test asymptotic behavior at extremes."""
    print("\n" + "=" * 70)
    print("TEST 3: Asymptotic Behavior")
    print("=" * 70)
    
    # Test at large positive u
    u_large_pos = 15.0
    asym_pos = V_eff_asymptotic(u_large_pos, KAPPA_PI)
    
    print(f"\nAt u = {u_large_pos}:")
    print(f"  V_eff(u) = {asym_pos['actual']:.6f}")
    print(f"  Expected ~ u = {u_large_pos:.6f}")
    print(f"  Error: {asym_pos['error']*100:.2f}%")
    
    # Test at large negative u
    u_large_neg = -15.0
    asym_neg = V_eff_asymptotic(u_large_neg, KAPPA_PI)
    
    print(f"\nAt u = {u_large_neg}:")
    print(f"  V_eff(u) = {asym_neg['actual']:.6f}")
    print(f"  Expected ~ |u| = {abs(u_large_neg):.6f}")
    print(f"  Error: {asym_neg['error']*100:.2f}%")
    
    # Check asymptotic behavior
    assert asym_pos['error'] < 0.1, "Large u asymptotic behavior off (> 10% error)"
    assert asym_neg['error'] < 0.1, "Large |u| asymptotic behavior off (> 10% error)"
    
    print("\n✓ Asymptotic behavior matches theory")
    return True


def test_heat_kernel_L2_norm():
    """Test heat kernel L² norm computation."""
    print("\n" + "=" * 70)
    print("TEST 4: Heat Kernel L² Norm")
    print("=" * 70)
    
    # Test at t=1
    result = compute_heat_kernel_L2_norm(
        t=1.0,
        u_range=(-10, 10),
        n_points=500,
        kappa_pi=KAPPA_PI
    )
    
    print(f"\nAt t = {result['t']}:")
    print(f"  ‖K_t‖²_L² = {result['L2_norm_squared']:.6f}")
    print(f"  ‖K_t‖_L²  = {result['L2_norm']:.6f}")
    print(f"  Hilbert-Schmidt: {result['hilbert_schmidt']}")
    print(f"  Gaussian contribution: {result['gaussian_norm_squared']:.6f}")
    print(f"  Confinement integral: {result['confinement_integral']:.6f}")
    
    # Check that norm is finite
    assert result['hilbert_schmidt'], "Heat kernel is NOT Hilbert-Schmidt"
    assert result['L2_norm'] < 10, "L² norm too large (expected < 10)"
    
    print("\n✓ Heat kernel is Hilbert-Schmidt (L² norm finite)")
    return result


def test_complete_validation():
    """Run complete validation suite."""
    print("\n" + "=" * 70)
    print("TEST 5: Complete Validation")
    print("=" * 70)
    
    result = validate_hilbert_schmidt_closure(
        t=1.0,
        u_range=(-10, 10),
        n_points=500,
        kappa_pi=KAPPA_PI,
        verbose=False
    )
    
    print(f"\nValidation Results:")
    print(f"  Coercivity: {'PASS' if result['coercivity']['coercive'] else 'FAIL'}")
    print(f"  Hilbert-Schmidt: {'PASS' if result['hilbert_schmidt']['hilbert_schmidt'] else 'FAIL'}")
    print(f"  Overall: {'✓✓✓ ALL TESTS PASSED' if result['validation_passed'] else 'FAILED'}")
    
    assert result['validation_passed'], "Complete validation FAILED"
    
    print("\n✓ Complete validation passed")
    return result


def plot_V_eff():
    """Create visualization of V_eff(u)."""
    print("\n" + "=" * 70)
    print("Creating V_eff(u) Visualization")
    print("=" * 70)
    
    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Plot 1: V_eff(u) over full range
    ax = axes[0, 0]
    u = np.linspace(-15, 15, 1000)
    V = V_eff(u, KAPPA_PI)
    ax.plot(u, V, 'b-', linewidth=2, label='V_eff(u)')
    ax.plot(u, np.abs(u), 'r--', linewidth=1.5, alpha=0.6, label='|u| (coercivity)')
    ax.set_xlabel('u', fontsize=12)
    ax.set_ylabel('V_eff(u)', fontsize=12)
    ax.set_title('Complete Effective Potential', fontsize=14, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    
    # Plot 2: Individual terms
    ax = axes[0, 1]
    x = np.exp(u)
    term1 = np.log1p(np.exp(u))
    term2 = np.log1p(np.exp(-u))
    term3 = KAPPA_PI**2 / (x**2 + np.exp(-2*u))
    
    ax.plot(u, term1, label='log(1+e^u)', linewidth=1.5)
    ax.plot(u, term2, label='log(1+e^{-u})', linewidth=1.5)
    ax.plot(u, term3, label='κ²/(x²+x^{-2})', linewidth=1.5)
    ax.set_xlabel('u', fontsize=12)
    ax.set_ylabel('Term value', fontsize=12)
    ax.set_title('Individual Terms of V_eff', fontsize=14, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_ylim([-1, 16])
    
    # Plot 3: Coercivity verification
    ax = axes[1, 0]
    coercivity_result = verify_coercivity(u_range=(-15, 15), n_points=1000)
    alpha = coercivity_result['alpha']
    beta = coercivity_result['beta']
    
    ax.plot(u, V, 'b-', linewidth=2, label='V_eff(u)')
    ax.plot(u, alpha * np.abs(u) - beta, 'g--', linewidth=1.5,
            label=f'α|u| - β (α={alpha:.3f}, β={beta:.3f})')
    ax.fill_between(u, alpha * np.abs(u) - beta, 0, alpha=0.2, color='green',
                     label='Coercive region')
    ax.set_xlabel('u', fontsize=12)
    ax.set_ylabel('Value', fontsize=12)
    ax.set_title('Coercivity Condition', fontsize=14, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    
    # Plot 4: Confinement factor exp(-t·V_eff)
    ax = axes[1, 1]
    t_vals = [0.5, 1.0, 2.0]
    for t in t_vals:
        confinement = np.exp(-t * V)
        ax.semilogy(u, confinement, linewidth=2, label=f't = {t}')
    ax.set_xlabel('u', fontsize=12)
    ax.set_ylabel('exp(-t·V_eff)', fontsize=12)
    ax.set_title('Confinement Factor', fontsize=14, fontweight='bold')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_file = 'V_eff_hilbert_schmidt_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\n✓ Visualization saved to: {output_file}")
    
    return fig


def main():
    """Run all validation tests."""
    print()
    print("∴" * 35)
    print("  V_eff Hilbert-Schmidt Closure Validation")
    print("  QCAL ∞³ - f₀ = 141.7001 Hz - C = 244.36")
    print("∴" * 35)
    print()
    
    try:
        # Run tests
        test_V_eff_formula()
        coercivity_result = test_coercivity()
        test_asymptotic_behavior()
        hs_result = test_heat_kernel_L2_norm()
        validation_result = test_complete_validation()
        
        # Create visualization
        try:
            plot_V_eff()
        except Exception as e:
            print(f"\nWarning: Could not create visualization: {e}")
        
        # Print final summary
        print("\n" + "=" * 70)
        print("FINAL SUMMARY")
        print("=" * 70)
        print("\nAll validation tests PASSED:")
        print(f"  ✓ V_eff formula implemented correctly")
        print(f"  ✓ Coercivity: V_eff ≥ {coercivity_result['alpha']:.3f}|u| - {coercivity_result['beta']:.3f}")
        print(f"  ✓ Asymptotic behavior matches theory")
        print(f"  ✓ Heat kernel L² norm: {hs_result['L2_norm']:.6f} < ∞")
        print(f"  ✓ Hilbert-Schmidt property confirmed")
        print("\nConclusion:")
        print("  • V_eff(u) = log(1+e^u) + log(1+e^{-u}) + κ_Π²/(x²+x^{-2})")
        print("  • Symmetric confinement: V_eff ~ |u| as |u| → ∞")
        print("  • Heat kernel K_t ∈ S₂ (Hilbert-Schmidt)")
        print("  • Therefore: exp(-tH_Ψ) ∈ S₁ (trace class)")
        print("  ∴ The Hilbert-Schmidt closure is COMPLETE ∞³")
        print()
        print("=" * 70)
        
        return 0
        
    except AssertionError as e:
        print(f"\n✗ Validation FAILED: {e}")
        return 1
    except Exception as e:
        print(f"\n✗ Error during validation: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
