#!/usr/bin/env python3
"""
Test for Operator J Involutive Property

This test validates the mathematical property proven in the Lean 4 formalization:
    J(J(f))(x) = f(x)

Where J is defined as:
    J(f)(x) = (1/x) * f(1/x)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 21 November 2025
Reference: DOI 10.5281/zenodo.17379721
"""

import numpy as np
import pytest
from typing import Callable


def J_operator(f: Callable[[float], complex]) -> Callable[[float], complex]:
    """
    Operator J that transforms f(x) to (1/x) * f(1/x).
    
    Args:
        f: A function from ℝ → ℂ
        
    Returns:
        The transformed function J(f)
    """
    def J_f(x: float) -> complex:
        if x <= 0:
            raise ValueError("x must be positive")
        return (1 / x) * f(1 / x)
    
    return J_f


def test_j_involutive_constant_function():
    """Test J is involutive on constant functions."""
    # f(x) = c for all x
    def f(x: float) -> complex:
        return 5.0 + 3.0j
    
    # Apply J twice
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    # Test at various points
    test_points = [0.1, 0.5, 1.0, 2.0, 10.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


def test_j_involutive_linear_function():
    """Test J is involutive on linear functions."""
    # f(x) = 2x + 1
    def f(x: float) -> complex:
        return 2.0 * x + 1.0
    
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 10.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


def test_j_involutive_quadratic_function():
    """Test J is involutive on quadratic functions."""
    # f(x) = x² + 3x + 2
    def f(x: float) -> complex:
        return x**2 + 3*x + 2
    
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 5.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


def test_j_involutive_exponential_function():
    """Test J is involutive on exponential functions."""
    # f(x) = e^x
    def f(x: float) -> complex:
        return np.exp(x)
    
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 3.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


def test_j_involutive_complex_function():
    """Test J is involutive on complex-valued functions."""
    # f(x) = x + ix²
    def f(x: float) -> complex:
        return x + 1j * x**2
    
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 5.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


def test_j_preserves_symmetry():
    """Test that J preserves functions satisfying x*f(x) = f(1/x)."""
    # Special symmetric function: f(x) = c/√x satisfies x*f(x) = c*√x = f(1/x)
    # Example: f(x) = 1/√x
    def f(x: float) -> complex:
        return 1 / np.sqrt(x)
    
    J_f = J_operator(f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 10.0]
    
    for x in test_points:
        # Verify the symmetry property: x * f(x) = f(1/x)
        assert np.isclose(x * f(x), f(1/x), rtol=1e-10), \
            f"Symmetry property not satisfied at x={x}"
        
        # For functions with x*f(x) = f(1/x), J(f)(x) should equal f(x)
        result = J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(f)({x}) = {result} ≠ f({x}) = {expected} for special symmetric f"


def test_j_argument_inversion():
    """Test that J correctly inverts the argument."""
    # f(x) = x
    def f(x: float) -> complex:
        return x
    
    J_f = J_operator(f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 10.0]
    
    for x in test_points:
        # J(f)(x) = (1/x) * f(1/x) = (1/x) * (1/x) = 1/x²
        result = J_f(x)
        expected = 1 / (x**2)
        assert np.isclose(result, expected, rtol=1e-10), \
            f"J(f)({x}) = {result} ≠ 1/x² = {expected}"


def test_j_positive_domain_only():
    """Test that J raises error for non-positive x."""
    def f(x: float) -> complex:
        return x
    
    J_f = J_operator(f)
    
    with pytest.raises(ValueError):
        J_f(0)
    
    with pytest.raises(ValueError):
        J_f(-1)


def test_j_involutive_riemann_xi_style():
    """
    Test J on a function inspired by Riemann Xi function properties.
    
    This tests the involutive property on a function that mimics
    some properties of functions appearing in the Riemann zeta context.
    """
    # f(x) = x^(1/4) * e^(-x)
    def f(x: float) -> complex:
        return x**0.25 * np.exp(-x)
    
    J_f = J_operator(f)
    J_J_f = J_operator(J_f)
    
    test_points = [0.1, 0.5, 1.0, 2.0, 5.0]
    
    for x in test_points:
        result = J_J_f(x)
        expected = f(x)
        assert np.isclose(result, expected, rtol=1e-9), \
            f"J(J(f))({x}) = {result} ≠ f({x}) = {expected}"


if __name__ == "__main__":
    print("=" * 70)
    print("Testing Operator J Involutive Property")
    print("=" * 70)
    print()
    
    # Run all tests
    test_functions = [
        ("Constant function", test_j_involutive_constant_function),
        ("Linear function", test_j_involutive_linear_function),
        ("Quadratic function", test_j_involutive_quadratic_function),
        ("Exponential function", test_j_involutive_exponential_function),
        ("Complex function", test_j_involutive_complex_function),
        ("Symmetric function preservation", test_j_preserves_symmetry),
        ("Argument inversion", test_j_argument_inversion),
        ("Positive domain enforcement", test_j_positive_domain_only),
        ("Riemann Xi style function", test_j_involutive_riemann_xi_style),
    ]
    
    passed = 0
    failed = 0
    
    for name, test_func in test_functions:
        try:
            test_func()
            print(f"✅ {name}")
            passed += 1
        except Exception as e:
            print(f"❌ {name}: {e}")
            failed += 1
    
    print()
    print("=" * 70)
    print(f"Results: {passed} passed, {failed} failed out of {len(test_functions)} tests")
    print("=" * 70)
    
    if failed == 0:
        print()
        print("✅ All tests passed! Operator J is involutive.")
        print()
        print("This validates the Lean 4 theorem:")
        print("  theorem J_involutive (f : ℝ → ℂ) : ∀ x > 0, J (J f) x = f x")
        print()
        print("JMMB Ψ ∴ ∞³")
        print("DOI: 10.5281/zenodo.17379721")
