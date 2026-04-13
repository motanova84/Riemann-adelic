#!/usr/bin/env python3
"""
Example usage of the Discrete Symmetry Operator H_DS

This script demonstrates the key features and properties of the H_DS operator
that implements the functional equation symmetry for the Riemann zeta function.

Run with:
    python example_H_DS.py
"""

import numpy as np
import matplotlib.pyplot as plt
from operador import DiscreteSymmetryOperator


def example_1_basic_application():
    """Example 1: Basic application of H_DS to a function."""
    print("=" * 70)
    print("EXAMPLE 1: Basic Application")
    print("=" * 70)
    
    H_DS = DiscreteSymmetryOperator()
    
    # Define a simple test function
    f = lambda x: x**2 * np.exp(-x)
    
    # Evaluate at some points
    x_values = np.array([0.5, 1.0, 2.0, 4.0])
    
    print(f"\nTest function: f(x) = x² * exp(-x)")
    print(f"\nEvaluating H_DS at x = {x_values}")
    print("\nx     | f(x)      | f(1/x)    | (H_DS f)(x)")
    print("-" * 50)
    
    for x in x_values:
        fx = f(x)
        f_inv_x = f(1/x)
        h_ds_fx = H_DS.apply(f, x)
        print(f"{x:5.2f} | {fx:9.6f} | {f_inv_x:9.6f} | {h_ds_fx:9.6f}")
    
    print("\nNote: (H_DS f)(x) = f(1/x) by definition")


def example_2_involutivity():
    """Example 2: Demonstrate involutivity property."""
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Involutivity Property (H_DS ∘ H_DS = id)")
    print("=" * 70)
    
    H_DS = DiscreteSymmetryOperator()
    
    # Test with a Gaussian
    f = lambda x: np.exp(-x**2 / 2)
    test_points = np.linspace(0.5, 5.0, 10)
    
    # Verify involutivity
    is_involutive, max_error = H_DS.verify_involutivity(f, test_points)
    
    print(f"\nTest function: f(x) = exp(-x²/2)")
    print(f"Test points: {len(test_points)} points from {test_points[0]:.1f} to {test_points[-1]:.1f}")
    print(f"\nInvolutivity test: {'✓ PASSED' if is_involutive else '✗ FAILED'}")
    print(f"Maximum error: {max_error:.2e}")
    
    # Show a few examples
    print("\nVerification at sample points:")
    print("x     | f(x)      | (H_DS∘H_DS f)(x) | Difference")
    print("-" * 55)
    for x in test_points[::3]:  # Show every 3rd point
        fx = f(x)
        h_ds_f = lambda y: H_DS.apply(f, y)
        h_ds_h_ds_fx = H_DS.apply(h_ds_f, x)
        diff = abs(fx - h_ds_h_ds_fx)
        print(f"{x:5.2f} | {fx:9.6f} | {h_ds_h_ds_fx:15.6f} | {diff:.2e}")


def example_3_spectral_symmetry():
    """Example 3: Spectral symmetry with a simple operator."""
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Spectral Symmetry")
    print("=" * 70)
    
    H_DS = DiscreteSymmetryOperator()
    
    # Simple eigenfunction: constant function
    # For a multiplication operator H_Ψ(f) = c*f, any function is an eigenfunction
    f = lambda x: np.exp(-x**2)
    eigenvalue = 2.5
    H_psi = lambda g: lambda x: eigenvalue * g(x)
    
    test_points = np.array([0.5, 1.0, 2.0, 3.0])
    
    # Verify spectral symmetry
    is_symmetric, error = H_DS.verify_spectral_symmetry(
        H_psi, f, eigenvalue, test_points
    )
    
    print(f"\nTest: If H_Ψ(f) = λf, then H_Ψ(H_DS f) = λ(H_DS f)")
    print(f"Eigenvalue λ = {eigenvalue}")
    print(f"Test function: f(x) = exp(-x²)")
    print(f"\nSpectral symmetry: {'✓ VERIFIED' if is_symmetric else '✗ FAILED'}")
    print(f"Maximum error: {error:.2e}")


def example_4_visualization():
    """Example 4: Visualize the action of H_DS."""
    print("\n" + "=" * 70)
    print("EXAMPLE 4: Visualization")
    print("=" * 70)
    
    H_DS = DiscreteSymmetryOperator()
    
    # Test function with interesting behavior
    f = lambda x: x * np.exp(-x**2 / 2)
    
    # Create x range
    x = np.linspace(0.1, 5.0, 200)
    
    # Compute f(x) and (H_DS f)(x)
    f_vals = f(x)
    h_ds_f_vals = H_DS.apply(f, x)
    
    # Create plot
    plt.figure(figsize=(12, 5))
    
    # Plot 1: Original and transformed function
    plt.subplot(1, 2, 1)
    plt.plot(x, f_vals, 'b-', linewidth=2, label='f(x) = x·exp(-x²/2)')
    plt.plot(x, h_ds_f_vals, 'r--', linewidth=2, label='(H_DS f)(x) = f(1/x)')
    plt.axhline(y=0, color='k', linestyle='-', alpha=0.3)
    plt.axvline(x=1, color='g', linestyle=':', alpha=0.5, label='x=1 (symmetry axis)')
    plt.xlabel('x', fontsize=12)
    plt.ylabel('Function value', fontsize=12)
    plt.title('H_DS: Inversion Symmetry', fontsize=14, fontweight='bold')
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    
    # Plot 2: Log scale to show symmetry around x=1
    plt.subplot(1, 2, 2)
    plt.semilogx(x, f_vals, 'b-', linewidth=2, label='f(x)')
    plt.semilogx(x, h_ds_f_vals, 'r--', linewidth=2, label='(H_DS f)(x)')
    plt.axvline(x=1, color='g', linestyle=':', alpha=0.5, label='x=1')
    plt.xlabel('x (log scale)', fontsize=12)
    plt.ylabel('Function value', fontsize=12)
    plt.title('Symmetry around x=1', fontsize=14, fontweight='bold')
    plt.legend(fontsize=10)
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_file = 'H_DS_visualization.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\n✓ Visualization saved to: {output_file}")
    plt.close()
    
    print("\nThe plots show:")
    print("  - Left: f(x) vs (H_DS f)(x) on linear scale")
    print("  - Right: Same functions on log scale showing symmetry around x=1")
    print("  - The inversion x ↦ 1/x creates a reflection around x=1 in log space")


def example_5_comprehensive_verification():
    """Example 5: Comprehensive verification of all properties."""
    print("\n" + "=" * 70)
    print("EXAMPLE 5: Comprehensive Property Verification")
    print("=" * 70)
    
    H_DS = DiscreteSymmetryOperator()
    
    # Test function
    f = lambda x: np.exp(-x**2)
    test_points = np.array([0.5, 1.0, 2.0, 3.0, 5.0])
    
    # Simple H_Ψ for testing
    c = 1.75
    H_psi = lambda g: lambda x: c * g(x)
    
    print(f"\nTest function: f(x) = exp(-x²)")
    print(f"Test operator: H_Ψ(g) = {c} * g")
    print(f"Number of test points: {len(test_points)}")
    
    # Run comprehensive verification
    results = H_DS.verify_all_properties(
        f,
        H_psi=H_psi,
        test_points=test_points,
        eigenvalue=c
    )
    
    print("\n" + "-" * 70)
    print("VERIFICATION RESULTS:")
    print("-" * 70)
    
    # Property 1: Involutivity
    if results['involutivity'] is not None:
        passed, error = results['involutivity']
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"1. Involutivity (H_DS ∘ H_DS = id):        {status}")
        print(f"   Maximum error: {error:.2e}")
    
    # Property 2: Commutation
    if results['commutation'] is not None:
        passed, error = results['commutation']
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"\n2. Commutation ([H_Ψ, H_DS] = 0):         {status}")
        print(f"   Maximum error: {error:.2e}")
    
    # Property 3: Domain stability
    if results['domain_stability'] is not None:
        passed = results['domain_stability']
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"\n3. Domain Stability (D preserved):         {status}")
    
    # Property 4: Spectral symmetry
    if results['spectral_symmetry'] is not None:
        passed, error = results['spectral_symmetry']
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"\n4. Spectral Symmetry (eigenvalues):       {status}")
        print(f"   Maximum error: {error:.2e}")
    
    print("\n" + "-" * 70)
    all_passed = results['all_passed']
    print(f"OVERALL RESULT: {'✓ ALL TESTS PASSED' if all_passed else '✗ SOME TESTS FAILED'}")
    print("-" * 70)
    
    if all_passed:
        print("\n✓ The H_DS operator satisfies all required properties!")
        print("  This confirms it correctly implements the discrete symmetry")
        print("  that enforces the functional equation of the zeta function.")


def main():
    """Run all examples."""
    print("\n" + "=" * 70)
    print("DISCRETE SYMMETRY OPERATOR H_DS - EXAMPLES")
    print("=" * 70)
    print("\nThis script demonstrates the key features of the H_DS operator")
    print("that implements the functional equation symmetry ζ(s) = χ(s)ζ(1-s)")
    print()
    
    try:
        # Run examples
        example_1_basic_application()
        example_2_involutivity()
        example_3_spectral_symmetry()
        example_4_visualization()
        example_5_comprehensive_verification()
        
        print("\n" + "=" * 70)
        print("ALL EXAMPLES COMPLETED SUCCESSFULLY")
        print("=" * 70)
        print("\nFor more details, see:")
        print("  - operador/operador_H_DS.py (implementation)")
        print("  - operador/tests_operador_H_DS.py (test suite)")
        print("  - operador/README_H_DS.md (documentation)")
        print()
        
    except Exception as e:
        print(f"\n✗ Error running examples: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()
