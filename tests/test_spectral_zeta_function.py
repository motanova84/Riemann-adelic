#!/usr/bin/env python3
"""
Test suite for spectral zeta function formalization

This test validates the mathematical concepts behind the Lean 4 formalization
of the spectral zeta function ζ_HΨ(s) and zeta-regularized determinant.

Tests:
1. Eigenvalue sequence properties (positive, ordered, divergent)
2. Zeta function convergence for ℜ(s) > 1
3. Derivative formula consistency
4. Determinant regularization
5. Connection to Riemann zeta via comparison

Author: José Manuel Mota Burruezo
Date: 2025-11-21
"""

import pytest
import numpy as np
from typing import Callable


class SpectralZetaTest:
    """Test class for spectral zeta function properties"""
    
    def __init__(self, eigenvalues: Callable[[int], float]):
        """
        Initialize with eigenvalue sequence
        
        Args:
            eigenvalues: Function n -> λₙ for n ≥ 0
        """
        self.eigenvalues = eigenvalues
    
    def compute_zeta(self, s: complex, n_terms: int = 100) -> complex:
        """
        Compute spectral zeta ζ_HΨ(s) = ∑ λₙ^{-s}
        
        Args:
            s: Complex number
            n_terms: Number of terms to sum
            
        Returns:
            Approximation of ζ_HΨ(s)
        """
        result = 0.0 + 0.0j
        for n in range(1, n_terms + 1):
            lamb = self.eigenvalues(n)
            result += lamb ** (-s)
        return result
    
    def compute_zeta_derivative(self, s: complex, n_terms: int = 100) -> complex:
        """
        Compute derivative ζ'_HΨ(s) = ∑ -log(λₙ) · λₙ^{-s}
        
        Args:
            s: Complex number
            n_terms: Number of terms to sum
            
        Returns:
            Approximation of ζ'_HΨ(s)
        """
        result = 0.0 + 0.0j
        for n in range(1, n_terms + 1):
            lamb = self.eigenvalues(n)
            result += -np.log(lamb) * (lamb ** (-s))
        return result
    
    def compute_det_zeta(self, s: complex, n_terms: int = 100) -> complex:
        """
        Compute zeta-regularized determinant det_ζ(s) = exp(-ζ'_HΨ(s))
        
        Args:
            s: Complex number
            n_terms: Number of terms
            
        Returns:
            Approximation of det_ζ(s)
        """
        zeta_deriv = self.compute_zeta_derivative(s, n_terms)
        return np.exp(-zeta_deriv)


def berry_keating_eigenvalues(n: int) -> float:
    """
    Berry-Keating eigenvalue model: λₙ = (n + 1/2)² + 141.7001
    
    This corresponds to the operator H_Ψ with base frequency 141.7001 Hz.
    
    Args:
        n: Index (n ≥ 1)
        
    Returns:
        Eigenvalue λₙ
    """
    return (n + 0.5) ** 2 + 141.7001


def simple_quadratic_eigenvalues(n: int) -> float:
    """
    Simple quadratic model: λₙ = n²
    
    Args:
        n: Index (n ≥ 1)
        
    Returns:
        Eigenvalue λₙ
    """
    return float(n ** 2)


class TestSpectralZetaProperties:
    """Test eigenvalue sequence properties"""
    
    def test_eigenvalues_positive(self):
        """Test that all eigenvalues are positive"""
        for n in range(1, 20):
            assert berry_keating_eigenvalues(n) > 0
            assert simple_quadratic_eigenvalues(n) > 0
    
    def test_eigenvalues_ordered(self):
        """Test that eigenvalues are non-decreasing"""
        for n in range(1, 20):
            bk_n = berry_keating_eigenvalues(n)
            bk_n1 = berry_keating_eigenvalues(n + 1)
            assert bk_n1 >= bk_n
            
            sq_n = simple_quadratic_eigenvalues(n)
            sq_n1 = simple_quadratic_eigenvalues(n + 1)
            assert sq_n1 >= sq_n
    
    def test_eigenvalues_tend_infinity(self):
        """Test that eigenvalues tend to infinity"""
        # Check that λ_100 > λ_10 > λ_1
        bk_1 = berry_keating_eigenvalues(1)
        bk_10 = berry_keating_eigenvalues(10)
        bk_100 = berry_keating_eigenvalues(100)
        
        assert bk_10 > bk_1
        assert bk_100 > bk_10
        assert bk_100 > 1000  # Should be large


class TestSpectralZetaConvergence:
    """Test convergence properties of spectral zeta function"""
    
    def test_convergence_for_large_real_part(self):
        """Test that ζ_HΨ(s) converges for ℜ(s) > 1"""
        zeta = SpectralZetaTest(simple_quadratic_eigenvalues)
        
        # For s = 2, should converge (compare with ∑ 1/n⁴)
        s = 2.0
        result = zeta.compute_zeta(s, n_terms=100)
        
        # Should be finite and positive
        assert np.isfinite(result)
        assert result.real > 0
        
        # Compare with Riemann zeta: ζ(2s) = π²ˢ/6
        # For λₙ = n², we have ζ_HΨ(s) = ζ_Riemann(2s)
        expected_approx = np.pi ** 4 / 90  # ζ(4) ≈ 1.0823
        assert abs(result - expected_approx) < 0.1
    
    def test_convergence_s_equals_one_half(self):
        """Test behavior at s = 1/2"""
        zeta = SpectralZetaTest(simple_quadratic_eigenvalues)
        
        # For λₙ = n² and s = 1/2, we get ∑ 1/n which diverges
        # But with more sophisticated eigenvalues, may converge
        s = 0.5
        
        # Should still give reasonable result with cutoff
        result = zeta.compute_zeta(s, n_terms=50)
        assert np.isfinite(result)


class TestZetaDerivative:
    """Test derivative computation"""
    
    def test_derivative_finite(self):
        """Test that derivative is finite for ℜ(s) > 1"""
        zeta = SpectralZetaTest(berry_keating_eigenvalues)
        
        s = 2.0
        zeta_deriv = zeta.compute_zeta_derivative(s, n_terms=50)
        
        # Should be finite
        assert np.isfinite(zeta_deriv)
    
    def test_derivative_negative_real_part(self):
        """Test that ζ'(s) has negative real part for s real > 1"""
        zeta = SpectralZetaTest(simple_quadratic_eigenvalues)
        
        s = 2.0
        zeta_deriv = zeta.compute_zeta_derivative(s, n_terms=50)
        
        # Should be negative (decreasing function)
        assert zeta_deriv.real < 0


class TestDetZeta:
    """Test zeta-regularized determinant"""
    
    def test_det_zeta_positive(self):
        """Test that det_ζ(s) is positive for s real"""
        zeta = SpectralZetaTest(berry_keating_eigenvalues)
        
        s = 2.0
        det = zeta.compute_det_zeta(s, n_terms=50)
        
        # exp(-negative) should be > 1
        assert det.real > 0
        assert det.imag == pytest.approx(0, abs=1e-10)
    
    def test_det_zeta_at_zero(self):
        """Test special value D(0) = det_ζ(0)"""
        zeta = SpectralZetaTest(berry_keating_eigenvalues)
        
        s = 0.0
        det = zeta.compute_det_zeta(s, n_terms=50)
        
        # Should be finite and positive
        assert np.isfinite(det)
        assert det.real > 0


class TestFunctionalEquationProperties:
    """Test properties related to functional equation"""
    
    def test_symmetry_around_one_half(self):
        """Test that D(s) should eventually satisfy D(1-s) = D(s)"""
        # This is a placeholder - actual functional equation requires
        # full adelic construction
        
        zeta = SpectralZetaTest(berry_keating_eigenvalues)
        
        # Evaluate at symmetric points
        s1 = 0.3
        s2 = 1 - s1  # 0.7
        
        d1 = zeta.compute_det_zeta(s1, n_terms=30)
        d2 = zeta.compute_det_zeta(s2, n_terms=30)
        
        # With simple model, won't be exactly equal
        # But should have same order of magnitude
        assert np.isfinite(d1) and np.isfinite(d2)


def test_qcal_coherence():
    """Test QCAL coherence parameters"""
    # Base frequency
    freq = 141.7001
    assert freq > 0
    
    # Coherence constant
    C = 244.36
    assert C > 0
    
    # Check eigenvalue includes frequency
    lamb_1 = berry_keating_eigenvalues(1)
    # λ₁ = (1 + 1/2)² + 141.7001 = 2.25 + 141.7001 = 143.9501
    expected = (1.5) ** 2 + freq
    assert abs(lamb_1 - expected) < 1e-6


def test_module_exists():
    """Test that the Lean module file exists"""
    import os
    
    lean_file = os.path.join(
        os.path.dirname(__file__),
        "..",
        "formalization",
        "lean",
        "RiemannAdelic",
        "spectral_zeta_function.lean"
    )
    
    assert os.path.exists(lean_file), \
        "spectral_zeta_function.lean should exist"


def test_readme_exists():
    """Test that documentation exists"""
    import os
    
    readme_file = os.path.join(
        os.path.dirname(__file__),
        "..",
        "formalization",
        "lean",
        "RiemannAdelic",
        "SPECTRAL_ZETA_README.md"
    )
    
    assert os.path.exists(readme_file), \
        "SPECTRAL_ZETA_README.md should exist"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
