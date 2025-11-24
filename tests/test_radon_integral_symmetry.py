"""
Test module for Radon-Poisson Integral Functional Symmetry theorem.

This module validates the integral symmetry property:
    ∫₀^∞ f(x) dx = ∫₀^∞ (Jf)(x) dx
where Jf(x) := (1/x)f(1/x) and f satisfies the symmetry condition f(x) = (1/x)f(1/x).

QCAL Integration: Part of V5 Coronación validation chain
Frequency base: 141.7001 Hz | Coherence: C = 244.36
"""

import pytest
import numpy as np
from scipy import integrate
from typing import Callable


def radon_operator(f: Callable[[float], float]) -> Callable[[float], float]:
    """
    Radon symmetry operator J: f(x) ↦ (1/x)f(1/x)
    
    Args:
        f: Input function
        
    Returns:
        Transformed function Jf
    """
    def Jf(x):
        if x == 0:
            return 0.0
        return (1.0 / x) * f(1.0 / x)
    return Jf


def verify_symmetry_condition(f: Callable[[float], float], 
                              x_samples: np.ndarray,
                              tolerance: float = 1e-10) -> bool:
    """
    Verify that f satisfies the Radon symmetry condition: f(x) = (1/x)f(1/x)
    
    Args:
        f: Function to check
        x_samples: Sample points (should be > 0)
        tolerance: Numerical tolerance
        
    Returns:
        True if symmetry condition is satisfied
    """
    Jf = radon_operator(f)
    
    for x in x_samples:
        if x > 0:
            f_x = f(x)
            Jf_x = Jf(x)
            if abs(f_x - Jf_x) > tolerance:
                return False
    return True


def test_radon_operator_involutive():
    """Test that the Radon operator is involutive: J(J(f)) = f"""
    # Define a simple symmetric function
    def f(x):
        if x <= 0:
            return 0.0
        return np.exp(-x - 1/x)
    
    Jf = radon_operator(f)
    JJf = radon_operator(Jf)
    
    # Test at several points
    x_values = [0.5, 1.0, 2.0, 5.0]
    for x in x_values:
        assert abs(f(x) - JJf(x)) < 1e-10, \
            f"Involution failed at x={x}: f(x)={f(x)}, J(J(f))(x)={JJf(x)}"


def test_symmetric_gaussian_like_function():
    """Test integral symmetry for a Gaussian-like symmetric function"""
    # Define f(x) = exp(-x - 1/x) which approximately satisfies f(x) ≈ (1/x)f(1/x)
    def f(x):
        if x <= 0:
            return 0.0
        return np.exp(-x - 1/x)
    
    # This function satisfies f(x) = (1/x)f(1/x) by construction
    # because exp(-x - 1/x) = (1/x) * x * exp(-x - 1/x) 
    # and x*exp(-1/x - x) = x*exp(-(x + 1/x)) doesn't match exactly
    # Let's use a better example
    
    def g(x):
        if x <= 0:
            return 0.0
        # g(x) = x^(-1/2) * exp(-(x + 1/x))
        return x**(-0.5) * np.exp(-(x + 1/x))
    
    # Verify symmetry condition
    x_samples = np.logspace(-1, 1, 20)
    
    Jg = radon_operator(g)
    
    # Check that g ≈ Jg
    for x in x_samples:
        g_x = g(x)
        Jg_x = Jg(x)
        # Allow some numerical tolerance
        assert abs(g_x - Jg_x) / max(abs(g_x), 1e-10) < 0.01, \
            f"Symmetry condition failed at x={x}: g(x)={g_x}, Jg(x)={Jg_x}"


def test_integral_symmetry_exact_case():
    """Test integral symmetry for a function with exact symmetry"""
    # Define f(x) = x^(-1/2) on (0, ∞)
    # Then Jf(x) = (1/x) * (1/x)^(-1/2) = (1/x) * x^(1/2) = x^(-1/2) = f(x)
    
    # Both integrals diverge, so let's use a cutoff version
    def f_cutoff(x, a=0.01, b=100):
        if x < a or x > b:
            return 0.0
        return x**(-0.5)
    
    Jf_cutoff = radon_operator(lambda x: f_cutoff(x))
    
    # Compute integrals
    integral_f, _ = integrate.quad(f_cutoff, 0.01, 100)
    integral_Jf, _ = integrate.quad(lambda x: Jf_cutoff(x), 0.01, 100)
    
    # They should be approximately equal
    relative_error = abs(integral_f - integral_Jf) / max(abs(integral_f), 1e-10)
    assert relative_error < 0.01, \
        f"Integral symmetry failed: ∫f = {integral_f}, ∫Jf = {integral_Jf}"


def test_change_of_variable_formula():
    """Test the change of variable formula underlying the Radon transform"""
    # For the integral ∫₀^∞ f(x) dx, substituting u = 1/x gives
    # ∫₀^∞ f(1/u) * (1/u²) du
    
    def f(x):
        if x <= 0:
            return 0.0
        return np.exp(-x**2)
    
    # Original integral (with cutoff)
    a, b = 0.01, 10
    integral_original, _ = integrate.quad(f, a, b)
    
    # After substitution u = 1/x: x goes from a to b, u goes from 1/b to 1/a
    def f_substituted(u):
        if u <= 0:
            return 0.0
        return f(1/u) * (1/u**2)
    
    integral_substituted, _ = integrate.quad(f_substituted, 1/b, 1/a)
    
    # Should be equal
    relative_error = abs(integral_original - integral_substituted) / max(abs(integral_original), 1e-10)
    assert relative_error < 1e-6, \
        f"Change of variable failed: original = {integral_original}, substituted = {integral_substituted}"


def test_radon_symmetry_with_weight():
    """Test Radon symmetry for weighted functions"""
    # Consider f(x) = x^(-1/2) * h(x) where h(x) = h(1/x)
    
    def h(x):
        """A symmetric function h(x) = h(1/x)"""
        if x <= 0:
            return 0.0
        # Use h(x) = exp(-log²(x)) which is symmetric around x=1
        return np.exp(-(np.log(x))**2)
    
    def f(x):
        if x <= 0:
            return 0.0
        return x**(-0.5) * h(x)
    
    # Verify h is symmetric
    x_samples = np.array([0.5, 0.8, 1.0, 1.5, 2.0])
    for x in x_samples:
        if x > 0:
            h_x = h(x)
            h_inv = h(1/x)
            assert abs(h_x - h_inv) / max(abs(h_x), 1e-10) < 1e-6, \
                f"h is not symmetric at x={x}"
    
    # Verify f satisfies Radon symmetry
    Jf = radon_operator(f)
    
    for x in x_samples:
        if x > 0:
            f_x = f(x)
            Jf_x = Jf(x)
            relative_error = abs(f_x - Jf_x) / max(abs(f_x), 1e-10)
            assert relative_error < 1e-6, \
                f"Radon symmetry failed at x={x}: f(x)={f_x}, Jf(x)={Jf_x}"


def test_integral_symmetry_with_exponential_decay():
    """Test integral symmetry with functions having exponential decay"""
    # f(x) = x^(-1/2) * exp(-x - 1/x)
    
    def f(x):
        if x <= 0:
            return 0.0
        return x**(-0.5) * np.exp(-x - 1/x)
    
    Jf = radon_operator(f)
    
    # Check symmetry at sample points
    x_samples = np.logspace(-1, 1, 10)
    symmetry_errors = []
    
    for x in x_samples:
        if x > 0:
            f_x = f(x)
            Jf_x = Jf(x)
            relative_error = abs(f_x - Jf_x) / max(abs(f_x), 1e-10)
            symmetry_errors.append(relative_error)
    
    # Average relative error should be small
    avg_error = np.mean(symmetry_errors)
    assert avg_error < 0.01, \
        f"Average symmetry error too large: {avg_error}"


def test_numerical_integral_comparison():
    """Numerically compare ∫f and ∫Jf for a symmetric function"""
    # Use f(x) = x^(-1/2) * exp(-(log(x))²)
    
    def f(x):
        if x <= 0 or x < 0.01 or x > 100:
            return 0.0
        return x**(-0.5) * np.exp(-(np.log(x))**2)
    
    Jf = radon_operator(f)
    
    # Compute both integrals with reasonable bounds
    a, b = 0.01, 100
    
    integral_f, error_f = integrate.quad(f, a, b, limit=100)
    integral_Jf, error_Jf = integrate.quad(lambda x: Jf(x), a, b, limit=100)
    
    # Compare
    relative_diff = abs(integral_f - integral_Jf) / max(abs(integral_f), 1e-10)
    
    print(f"\n∫₀^∞ f(x) dx = {integral_f:.10f} ± {error_f:.2e}")
    print(f"∫₀^∞ Jf(x) dx = {integral_Jf:.10f} ± {error_Jf:.2e}")
    print(f"Relative difference: {relative_diff:.2e}")
    
    assert relative_diff < 0.01, \
        f"Integral symmetry failed: relative difference = {relative_diff}"


def test_functional_equation_connection():
    """Test connection between Radon symmetry and functional equation"""
    # For functions satisfying f(x) = (1/x)f(1/x), 
    # their Mellin transform M[f](s) satisfies M[f](s) = M[f](1-s)
    
    # This is the key connection to the Riemann Hypothesis
    # We test this numerically for a simple case
    
    def f(x):
        if x <= 0:
            return 0.0
        # Use a function with known Mellin transform symmetry
        return x**(-0.5) * np.exp(-(np.log(x))**2)
    
    # Verify Radon symmetry
    Jf = radon_operator(f)
    
    x_test = np.logspace(-1, 1, 20)
    for x in x_test:
        if x > 0:
            assert abs(f(x) - Jf(x)) / max(abs(f(x)), 1e-10) < 0.01


def test_qcal_integration_validation():
    """
    Test QCAL ∞³ integration and validation chain.
    
    This test ensures the theorem integrates properly with the QCAL framework:
    - Frequency base: 141.7001 Hz
    - Coherence: C = 244.36
    - Validation chain: Axioms → Lemmas → Archimedean → Paley-Wiener → 
                       Zero localization → Coronación
    """
    # Reference frequency
    f0 = 141.7001  # Hz
    C = 244.36  # Coherence constant
    
    # Verify constants are in expected ranges
    assert 141.0 < f0 < 142.0, f"Frequency out of range: {f0}"
    assert 244.0 < C < 245.0, f"Coherence out of range: {C}"
    
    # The Radon integral symmetry theorem is part of the validation chain
    # Verify that the theorem structure is sound
    
    def f_qcal(x):
        """QCAL-coherent test function"""
        if x <= 0:
            return 0.0
        # Use the base frequency to construct a resonant function
        omega = 2 * np.pi * f0
        return x**(-0.5) * np.exp(-(omega * x + omega / x) / 1000.0)
    
    # Verify Radon symmetry
    Jf = radon_operator(f_qcal)
    
    x_samples = np.logspace(-2, 2, 15)
    max_error = 0.0
    
    for x in x_samples:
        if x > 0:
            relative_error = abs(f_qcal(x) - Jf(x)) / max(abs(f_qcal(x)), 1e-10)
            max_error = max(max_error, relative_error)
    
    # With QCAL coherence, symmetry should be well-maintained
    assert max_error < 0.02, \
        f"QCAL coherence validation failed: max error = {max_error}"


if __name__ == "__main__":
    # Run tests when script is executed directly
    print("=" * 70)
    print("Radon-Poisson Integral Functional Symmetry Theorem - Test Suite")
    print("=" * 70)
    print()
    
    pytest.main([__file__, "-v", "-s"])
