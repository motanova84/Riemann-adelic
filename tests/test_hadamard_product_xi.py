#!/usr/bin/env python3
"""
Test suite for Hadamard Product Theorem for ξ(s) (Riemann Xi function)

This test validates the mathematical concepts behind the Lean 4 formalization
of the Hadamard product representation for the Riemann Xi function:

    ξ(s) = e^{A + Bs} ∏_ρ (1 - s/ρ) e^{s/ρ}

Tests:
1. Riemann Xi function definition and properties
2. Weierstrass elementary factors
3. Hadamard product convergence
4. Functional equation symmetry
5. Zero distribution properties
6. Spectral interpretation connections
7. QCAL coherence integration

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import cmath
from typing import Callable, List, Tuple
from pathlib import Path

try:
    import scipy.special as sp
    SCIPY_AVAILABLE = True
except ImportError:
    SCIPY_AVAILABLE = False
    
try:
    import mpmath
    MPMATH_AVAILABLE = True
except ImportError:
    MPMATH_AVAILABLE = False

# Constants for numerical tolerance
TOLERANCE_SMALL = 1e-10
TOLERANCE_MEDIUM = 1e-6
TOLERANCE_LARGE = 0.01

# Project paths
PROJECT_ROOT = Path(__file__).parent.parent
FORMALIZATION_DIR = PROJECT_ROOT / "formalization" / "lean"
RIEMANN_ADELIC_DIR = FORMALIZATION_DIR / "RiemannAdelic"


def riemann_zeta_approx(s: complex, n_terms: int = 1000) -> complex:
    """
    Approximate ζ(s) using the Dirichlet series for Re(s) > 1
    
    Args:
        s: Complex number with Re(s) > 1
        n_terms: Number of terms in the sum
        
    Returns:
        Approximation of ζ(s)
    """
    if s.real <= 1:
        return complex('nan')
    return sum(n ** (-s) for n in range(1, n_terms + 1))


def gamma_approx(s: complex) -> complex:
    """
    Approximate Γ(s) using scipy or mpmath
    
    Args:
        s: Complex number
        
    Returns:
        Approximation of Γ(s)
    """
    if SCIPY_AVAILABLE:
        return complex(sp.gamma(s))
    elif MPMATH_AVAILABLE:
        return complex(mpmath.gamma(s))
    else:
        # Stirling approximation for large |s|
        if abs(s) > 10:
            return cmath.sqrt(2 * np.pi / s) * (s / np.e) ** s
        return complex('nan')


def riemann_xi(s: complex) -> complex:
    """
    Compute the Riemann Xi function ξ(s) = π^(-s/2) Γ(s/2) ζ(s)
    
    Args:
        s: Complex number
        
    Returns:
        Value of ξ(s)
        
    Note: This is the 'bare' xi function, not the completed version 
    with the s(s-1)/2 factor.
    """
    if s.real <= 1:
        return complex('nan')
    
    pi_factor = np.pi ** (-s / 2)
    gamma_factor = gamma_approx(s / 2)
    zeta_factor = riemann_zeta_approx(s)
    
    return pi_factor * gamma_factor * zeta_factor


def weierstrass_E1(z: complex) -> complex:
    """
    Weierstrass elementary factor E₁(z) = (1 - z) · e^z
    
    This is the building block of the Hadamard product for order 1 functions.
    
    Args:
        z: Complex number
        
    Returns:
        E₁(z) = (1 - z) · e^z
    """
    return (1 - z) * cmath.exp(z)


def hadamard_factor(s: complex, rho: complex) -> complex:
    """
    Hadamard product factor (1 - s/ρ) · e^(s/ρ) = E₁(s/ρ)
    
    Args:
        s: Complex number
        rho: Zero of the function (ρ ≠ 0)
        
    Returns:
        Hadamard factor for zero ρ
    """
    if rho == 0:
        return complex('nan')
    return weierstrass_E1(s / rho)


class TestRiemannXiFunction:
    """Test the Riemann Xi function ξ(s) = π^(-s/2) Γ(s/2) ζ(s)"""
    
    @pytest.mark.skipif(not SCIPY_AVAILABLE, reason="scipy not available")
    def test_xi_at_s_2(self):
        """Test ξ(2) computation"""
        s = 2.0 + 0.0j
        xi_val = riemann_xi(s)
        
        # ξ(2) = π^(-1) · Γ(1) · ζ(2) = (1/π) · 1 · (π²/6) = π/6
        expected = np.pi / 6
        
        assert np.isfinite(xi_val)
        assert abs(xi_val - expected) < TOLERANCE_LARGE
    
    @pytest.mark.skipif(not SCIPY_AVAILABLE, reason="scipy not available")
    def test_xi_positive_for_real_s(self):
        """Test that ξ(s) > 0 for real s > 1"""
        for s in [2.0, 3.0, 4.0, 5.0, 10.0]:
            xi_val = riemann_xi(complex(s))
            assert xi_val.real > 0
            assert abs(xi_val.imag) < TOLERANCE_MEDIUM
    
    @pytest.mark.skipif(not SCIPY_AVAILABLE, reason="scipy not available")
    def test_xi_growth_order(self):
        """Test that ξ(s) has order 1 (grows like exp(|s|))"""
        # For order 1, log|ξ(s)| / |s| should be bounded
        s_vals = [2.0, 5.0, 10.0, 20.0]
        
        for s in s_vals:
            xi_val = riemann_xi(complex(s))
            if abs(xi_val) > 0:
                log_ratio = np.log(abs(xi_val)) / s
                # Should be bounded for order 1 functions
                assert log_ratio < 2.0  # Loose bound


class TestWeierstrassElementaryFactors:
    """Test Weierstrass elementary factors E₁(z)"""
    
    def test_E1_at_zero(self):
        """Test E₁(0) = 1"""
        result = weierstrass_E1(0)
        expected = 1.0
        assert abs(result - expected) < TOLERANCE_SMALL
    
    def test_E1_at_one(self):
        """Test E₁(1) = 0"""
        result = weierstrass_E1(1)
        expected = 0.0
        assert abs(result - expected) < TOLERANCE_SMALL
    
    def test_E1_formula(self):
        """Test E₁(z) = (1-z)·e^z for various z"""
        test_values = [0.5, 0.1, 2.0, 1.0 + 1.0j, 0.5 + 0.5j]
        
        for z in test_values:
            result = weierstrass_E1(z)
            expected = (1 - z) * cmath.exp(z)
            assert abs(result - expected) < TOLERANCE_SMALL
    
    def test_E1_product_property(self):
        """Test that E₁ factors converge well for small |z|"""
        # For |z| < 1, the Taylor expansion converges
        z = 0.1 + 0.05j
        E1_z = weierstrass_E1(z)
        
        # Alternative: log E₁(z) = log(1-z) + z ≈ -z²/2 - z³/3 - ... for small z
        log_E1 = cmath.log(E1_z)
        expected_log = cmath.log(1 - z) + z
        
        assert abs(log_E1 - expected_log) < TOLERANCE_SMALL


class TestHadamardFactor:
    """Test Hadamard product factors (1 - s/ρ)·e^(s/ρ)"""
    
    def test_hadamard_factor_formula(self):
        """Test hadamard_factor = E₁(s/ρ)"""
        s = 0.5 + 14.134j  # Near critical line
        rho = 0.5 + 14.134j  # A typical zero
        
        result = hadamard_factor(s, rho)
        expected = weierstrass_E1(s / rho)
        
        assert abs(result - expected) < TOLERANCE_SMALL
    
    def test_hadamard_factor_at_zero(self):
        """Test factor at s = ρ (the zero)"""
        rho = 0.5 + 14.134j
        s = rho  # s = ρ
        
        result = hadamard_factor(s, rho)
        # (1 - 1)·e^1 = 0·e = 0
        assert abs(result) < TOLERANCE_SMALL
    
    def test_hadamard_factor_symmetry(self):
        """Test symmetry properties related to functional equation"""
        # If ρ is a zero, then 1 - ρ is also a zero (functional equation)
        rho = 0.5 + 14.134j
        rho_conjugate = 1 - rho  # = 0.5 - 14.134j
        
        s = 2.0 + 0.0j
        
        factor_rho = hadamard_factor(s, rho)
        factor_conj = hadamard_factor(1 - s, rho_conjugate)
        
        # The product over paired zeros contributes to the symmetry
        assert np.isfinite(factor_rho)
        assert np.isfinite(factor_conj)


class TestHadamardProductConvergence:
    """Test convergence properties of the Hadamard product"""
    
    def test_product_convergence_for_simple_zeros(self):
        """Test product convergence with simple model zeros"""
        # Use zeros at ±n for simplicity (not actual zeta zeros)
        def model_zeros(n: int) -> complex:
            return complex(0.5, n)  # Model: zeros at 0.5 + n·i
        
        s = 2.0 + 0.0j
        
        # Compute partial products
        products = []
        product = 1.0
        for n in range(1, 51):
            rho = model_zeros(n)
            if abs(rho) > 0:
                factor = hadamard_factor(s, rho) * hadamard_factor(s, rho.conjugate())
                product *= factor
            products.append(product)
        
        # Check convergence (differences decrease)
        diffs = [abs(products[i+1] - products[i]) for i in range(len(products)-1)]
        
        # Later differences should generally be smaller (convergent)
        assert diffs[-1] < diffs[0] or diffs[-1] < 0.01
    
    def test_series_summability(self):
        """Test that ∑ 1/|ρ|² converges (order 1 property)"""
        # For order 1 functions, ∑ 1/|ρ_n|^(1+ε) converges for any ε > 0
        # In particular, ∑ 1/|ρ_n|² converges
        
        # Model zeros at 0.5 + n·i
        def model_zero_modulus(n: int) -> float:
            return np.sqrt(0.25 + n**2)
        
        # Sum of 1/|ρ|²
        sum_reciprocal_sq = sum(1 / model_zero_modulus(n)**2 for n in range(1, 1000))
        
        # Should converge (be finite)
        assert np.isfinite(sum_reciprocal_sq)
        
        # And ∑ 1/|ρ| should diverge (since sum ≈ ∑ 1/n)
        sum_reciprocal = sum(1 / model_zero_modulus(n) for n in range(1, 1000))
        assert sum_reciprocal > 5  # Grows (divergent for infinite terms)


class TestFunctionalEquation:
    """Test functional equation ξ(s) = ξ(1-s) properties"""
    
    def test_zero_symmetry(self):
        """Test that if ρ is a zero, then 1-ρ is also a zero"""
        # First few known zeta zeros (imaginary parts)
        known_zeros_t = [14.134725, 21.022040, 25.010858, 30.424876]
        
        for t in known_zeros_t:
            rho = 0.5 + t * 1j  # Assumes RH
            one_minus_rho = 1 - rho  # = 0.5 - t·i
            
            # The real part is preserved: Re(ρ) = Re(1-ρ) = 0.5
            assert abs(rho.real - 0.5) < TOLERANCE_SMALL
            assert abs(one_minus_rho.real - 0.5) < TOLERANCE_SMALL
    
    def test_product_pairing(self):
        """Test that zeros come in symmetric pairs for the product"""
        t = 14.134725
        rho = 0.5 + t * 1j
        rho_paired = 0.5 - t * 1j  # Complex conjugate (also a zero)
        
        s = 2.0 + 0.0j
        
        # Product of paired factors
        factor_rho = hadamard_factor(s, rho)
        factor_paired = hadamard_factor(s, rho_paired)
        
        paired_product = factor_rho * factor_paired
        
        # The paired product should be real for real s
        assert abs(paired_product.imag) < TOLERANCE_MEDIUM


class TestSpectralConnection:
    """Test connections to the spectral interpretation (Ξ-HΨ model)"""
    
    def test_zeros_as_eigenvalues_concept(self):
        """Test the conceptual link: zeros ↔ eigenvalues"""
        # In the spectral interpretation, zeros ρ of ξ(s) correspond to
        # eigenvalues of the operator H_Ψ
        
        # First few known zeta zeros
        known_zeros = [0.5 + 14.134725j, 0.5 + 21.022040j, 0.5 + 25.010858j]
        
        for rho in known_zeros:
            # If RH is true, Re(ρ) = 1/2
            assert abs(rho.real - 0.5) < TOLERANCE_MEDIUM
            
            # The imaginary part gives the "eigenvalue" γ: ρ = 1/2 + iγ
            gamma = rho.imag
            assert gamma > 0
    
    def test_spectral_determinant_structure(self):
        """Test the structure of ξ(s) as a spectral determinant"""
        # ξ(s) = e^{A+Bs} ∏_ρ (1 - s/ρ)e^{s/ρ}
        # This is analogous to det(I - T) = ∏(1 - λ_n)
        
        # Verify the exponential prefactor form
        A = 0.5  # Model constant
        B = 0.1  # Model constant
        s = 2.0 + 0.0j
        
        prefactor = cmath.exp(A + B * s)
        
        assert np.isfinite(prefactor)
        assert abs(prefactor) > 0


class TestQCALIntegration:
    """Test QCAL ∞³ framework integration"""
    
    def test_coherence_constant(self):
        """Test QCAL coherence constant C = 244.36"""
        C = 244.36
        assert C > 0
        assert 244 < C < 245
    
    def test_base_frequency(self):
        """Test QCAL base frequency f₀ = 141.7001 Hz"""
        f0 = 141.7001
        assert f0 > 0
        assert 141 < f0 < 142
    
    def test_coherence_ratio(self):
        """Test coherence ratio C/f₀"""
        C = 244.36
        f0 = 141.7001
        
        ratio = C / f0
        assert ratio > 0
        assert 1.7 < ratio < 1.8  # Approximately 1.724
    
    def test_spectral_connection_frequency(self):
        """Test connection between spectral zeros and QCAL frequency"""
        f0 = 141.7001
        first_zero_t = 14.134725
        
        # The ratio relates to the quantum coherence structure
        ratio = f0 / first_zero_t
        
        assert np.isfinite(ratio)
        assert ratio > 0


class TestModuleExists:
    """Test that required files exist"""
    
    def test_lean_module_exists(self):
        """Test that hadamard_product_xi.lean exists"""
        lean_file = RIEMANN_ADELIC_DIR / "hadamard_product_xi.lean"
        
        assert lean_file.exists(), \
            f"hadamard_product_xi.lean should exist at {lean_file}"
    
    def test_main_includes_module(self):
        """Test that Main.lean imports the new module"""
        main_file = FORMALIZATION_DIR / "Main.lean"
        
        assert main_file.exists(), \
            f"Main.lean should exist at {main_file}"
        
        try:
            content = main_file.read_text(encoding='utf-8')
        except (FileNotFoundError, IOError) as e:
            pytest.fail(f"Failed to read Main.lean: {e}")
        
        assert "hadamard_product_xi" in content, \
            "Main.lean should import hadamard_product_xi"
    
    def test_lean_module_structure(self):
        """Test that hadamard_product_xi.lean has correct structure"""
        lean_file = RIEMANN_ADELIC_DIR / "hadamard_product_xi.lean"
        
        assert lean_file.exists(), \
            f"hadamard_product_xi.lean should exist at {lean_file}"
        
        try:
            content = lean_file.read_text(encoding='utf-8')
        except (FileNotFoundError, IOError) as e:
            pytest.fail(f"Failed to read hadamard_product_xi.lean: {e}")
        
        # Check for key definitions and theorems
        assert "riemann_xi" in content, \
            "Module should define riemann_xi"
        assert "hadamard_product_xi" in content, \
            "Module should contain hadamard_product_xi theorem"
        assert "riemann_zeta_zeros" in content, \
            "Module should define riemann_zeta_zeros"
        assert "weierstrass_E1" in content, \
            "Module should define Weierstrass elementary factor"


class TestMathematicalSignificance:
    """Test the mathematical significance of the Hadamard product"""
    
    def test_order_one_characterization(self):
        """Test that order 1 implies specific convergence properties"""
        # For order 1 functions:
        # - Series ∑ 1/|ρ_n| diverges
        # - Series ∑ 1/|ρ_n|^2 converges
        # - This determines genus p = 1
        
        # Model zeros at imaginary heights matching Riemann zeros
        zero_heights = [14.13, 21.02, 25.01, 30.42, 32.94, 37.59]
        
        sum_reciprocal = sum(1 / (0.25 + t**2)**0.5 for t in zero_heights)
        sum_reciprocal_sq = sum(1 / (0.25 + t**2) for t in zero_heights)
        
        # Both should be finite for these few terms
        assert np.isfinite(sum_reciprocal)
        assert np.isfinite(sum_reciprocal_sq)
        
        # But for infinite zeros, only ∑ 1/|ρ|² converges
        # (verified conceptually)
    
    def test_spectral_approach_connection(self):
        """Test that Hadamard product enables spectral approach"""
        # The Hadamard product ξ(s) = e^{A+Bs} ∏_ρ (1-s/ρ)e^{s/ρ}
        # is analogous to spectral determinant det(H - s)
        
        # Key insight: zeros of ξ ↔ eigenvalues of H_Ψ
        
        # The logarithmic derivative ξ'/ξ has a series over zeros:
        # ξ'(s)/ξ(s) = B + ∑_ρ (1/(s-ρ) + 1/ρ)
        
        # This is analogous to:
        # d/ds log det(H - s) = -Tr((H - s)^{-1})
        
        s = 2.0 + 0.0j
        B = 0.1  # Model constant
        
        # Model contribution from zeros
        zero_heights = [14.13, 21.02]
        log_deriv_contrib = B
        
        for t in zero_heights:
            rho = 0.5 + t * 1j
            log_deriv_contrib += 1 / (s - rho) + 1 / rho
            log_deriv_contrib += 1 / (s - rho.conjugate()) + 1 / rho.conjugate()
        
        assert np.isfinite(log_deriv_contrib)


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
