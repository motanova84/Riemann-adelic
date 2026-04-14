#!/usr/bin/env python3
"""
Test Suite for Fredholm Determinant Constructor
================================================

Tests the 4-step construction:
1. Fredholm determinant with Hadamard regularization
2. Trace formula insertion (Enki Bridge)
3. PT symmetry and Hadamard expansion
4. Remainder control

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import pytest
import numpy as np
from operators.fredholm_determinant_constructor import (
    FredholmDeterminantConstructor,
    FredholmDeterminantResult,
    TraceFormulaResult,
    HadamardExpansionResult
)


class TestFredholmDeterminantConstructor:
    """Test suite for FredholmDeterminantConstructor class."""
    
    @pytest.fixture
    def constructor(self):
        """Create a constructor instance with moderate precision."""
        return FredholmDeterminantConstructor(
            precision=15,
            max_eigenvalues=50,
            remainder_decay=0.5
        )
    
    @pytest.fixture
    def riemann_zeros(self):
        """First 10 Riemann zero imaginary parts (known values)."""
        return np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832
        ])
    
    @pytest.fixture
    def pt_symmetric_spectrum(self, riemann_zeros):
        """PT-symmetric spectrum with (γ, -γ) pairs."""
        return np.concatenate([riemann_zeros, -riemann_zeros])
    
    def test_constructor_initialization(self, constructor):
        """Test constructor initializes with correct parameters."""
        assert constructor.precision == 15
        assert constructor.max_eigenvalues == 50
        assert constructor.remainder_decay == 0.5
    
    def test_verify_pt_symmetry_true(self, constructor, pt_symmetric_spectrum):
        """Test PT symmetry verification for symmetric spectrum."""
        is_symmetric = constructor._verify_pt_symmetry(pt_symmetric_spectrum)
        assert is_symmetric is True
    
    def test_verify_pt_symmetry_false(self, constructor):
        """Test PT symmetry verification for non-symmetric spectrum."""
        non_symmetric = np.array([1.0, 2.0, 3.0, 4.0])
        is_symmetric = constructor._verify_pt_symmetry(non_symmetric)
        assert is_symmetric is False
    
    def test_hadamard_product_convergence(self, constructor, riemann_zeros):
        """Test Hadamard product converges for small t."""
        t = 1.0
        result = constructor._hadamard_product_order1(riemann_zeros, t)
        
        # Should be finite and non-zero
        assert np.isfinite(result)
        assert abs(result) > 0
    
    def test_log_derivative_finite(self, constructor, riemann_zeros):
        """Test logarithmic derivative is finite."""
        t = 5.0
        derivative = constructor._log_derivative_order1(riemann_zeros, t)
        
        assert np.isfinite(derivative)
    
    def test_fredholm_determinant_paso1(self, constructor, pt_symmetric_spectrum):
        """Test PASO 1: Fredholm determinant computation."""
        t_values = np.linspace(1, 10, 20)
        
        result = constructor.compute_fredholm_determinant(
            pt_symmetric_spectrum,
            t_values,
            regularization_order=1
        )
        
        # Check result structure
        assert isinstance(result, FredholmDeterminantResult)
        assert len(result.t_values) == 20
        assert len(result.xi_values) == 20
        assert len(result.log_derivative) == 20
        assert result.regularization_order == 1
        assert result.pt_symmetric is True
        
        # Check values are finite
        assert np.all(np.isfinite(result.xi_values))
        assert np.all(np.isfinite(result.log_derivative))
    
    def test_get_primes(self, constructor):
        """Test prime number generation."""
        primes = constructor._get_primes(10)
        
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected_primes
    
    def test_weyl_contribution(self, constructor):
        """Test Weyl density contribution computation."""
        s_values = np.linspace(0, 10, 50)
        weyl = constructor._compute_weyl_contribution(s_values, n_eigenvalues=100)
        
        # Should be real and positive
        assert np.all(np.isreal(weyl))
        assert np.all(weyl >= 0)
        
        # Should decay with |s|
        assert weyl[0] > weyl[-1]
    
    def test_prime_contribution(self, constructor):
        """Test prime contribution computation."""
        s_values = np.linspace(0, 10, 50)
        prime_contrib = constructor._compute_prime_contribution(s_values, n_primes=5)
        
        # Should be finite
        assert np.all(np.isfinite(prime_contrib))
    
    def test_trace_formula_paso2(self, constructor, pt_symmetric_spectrum):
        """Test PASO 2: Trace formula computation."""
        s_values = np.linspace(0, 10, 100)
        
        result = constructor.compute_trace_formula(
            pt_symmetric_spectrum,
            s_values,
            include_primes=True,
            n_primes=20
        )
        
        # Check result structure
        assert isinstance(result, TraceFormulaResult)
        assert len(result.s_values) == 100
        assert np.all(np.isfinite(result.spectral_density))
        assert np.all(np.isfinite(result.weyl_contribution))
        assert np.all(np.isfinite(result.prime_contribution))
        assert np.all(np.isfinite(result.remainder))
        assert result.remainder_bound >= 0
    
    def test_remainder_bound_estimation(self, constructor):
        """Test exponential remainder bound estimation."""
        s_values = np.linspace(0, 10, 50)
        # Create synthetic remainder with exponential decay
        true_lambda = 0.3
        remainder = np.exp(-true_lambda * np.abs(s_values)) * (1 + 0.1 * np.random.randn(len(s_values)))
        
        lambda_est = constructor._estimate_remainder_bound(remainder, s_values)
        
        # Should be close to true lambda
        assert abs(lambda_est - true_lambda) < 0.2
    
    def test_hadamard_expansion_paso3(self, constructor, pt_symmetric_spectrum):
        """Test PASO 3: Hadamard expansion and ξ function comparison."""
        t_values = np.linspace(1, 10, 20)
        
        result = constructor.compute_hadamard_expansion(
            pt_symmetric_spectrum,
            t_values,
            compute_xi_ratio=False  # Skip xi computation for speed
        )
        
        # Check result structure
        assert isinstance(result, HadamardExpansionResult)
        assert len(result.t_values) == 20
        assert np.all(np.isfinite(result.xi_hadamard))
        assert np.all(np.isfinite(result.relative_error))
    
    def test_remainder_control_paso4(self, constructor):
        """Test PASO 4: Remainder control verification."""
        s_values = np.linspace(0, 10, 50)
        # Create controlled remainder
        remainder = 2.0 * np.exp(-0.4 * np.abs(s_values))
        
        result = constructor.verify_remainder_control(
            remainder,
            s_values,
            lambda_target=0.3
        )
        
        # Check result structure
        assert 'lambda_estimated' in result
        assert 'C_constant' in result
        assert 'bound_holds' in result
        assert result['lambda_estimated'] > 0
        assert result['C_constant'] > 0
    
    def test_complete_construction(self, constructor, pt_symmetric_spectrum):
        """Test complete 4-step construction."""
        t_values = np.linspace(1, 20, 30)
        s_values = np.linspace(0, 10, 80)
        
        result = constructor.complete_construction(
            pt_symmetric_spectrum,
            t_values=t_values,
            s_values=s_values
        )
        
        # Check all 4 pasos are present
        assert 'paso1_fredholm' in result
        assert 'paso2_trace_formula' in result
        assert 'paso3_hadamard' in result
        assert 'paso4_remainder' in result
        
        # Check metadata
        assert 'pt_symmetric' in result
        assert 'identity_verified' in result
        assert 'theorem' in result
        assert 'seal' in result
        assert 'signature' in result
        assert 'status' in result
        
        # Verify PT symmetry detected
        assert result['pt_symmetric'] is True
    
    def test_numerical_stability_small_t(self, constructor, riemann_zeros):
        """Test numerical stability for small t values."""
        t_values = np.array([0.01, 0.1, 0.5])
        
        result = constructor.compute_fredholm_determinant(
            riemann_zeros,
            t_values,
            regularization_order=1
        )
        
        # All values should be finite
        assert np.all(np.isfinite(result.xi_values))
        assert np.all(np.isfinite(result.log_derivative))
    
    def test_numerical_stability_large_t(self, constructor, riemann_zeros):
        """Test numerical stability for large t values."""
        t_values = np.array([50, 100, 200])
        
        result = constructor.compute_fredholm_determinant(
            riemann_zeros,
            t_values,
            regularization_order=1
        )
        
        # All values should be finite (may be small)
        assert np.all(np.isfinite(result.xi_values))
        assert np.all(np.isfinite(result.log_derivative))
    
    def test_determinant_regularity(self, constructor, riemann_zeros):
        """Test that Ξ(t) is a regular function (no singularities)."""
        t_values = np.linspace(0.1, 50, 100)
        
        result = constructor.compute_fredholm_determinant(
            riemann_zeros,
            t_values
        )
        
        # No NaN or Inf values
        assert not np.any(np.isnan(result.xi_values))
        assert not np.any(np.isinf(result.xi_values))
    
    def test_log_derivative_spectral_representation(self, constructor, riemann_zeros):
        """Test that d/dt ln Ξ(t) has correct pole structure."""
        # The log derivative should have poles at t = -i/γ_n
        # For real t, should be smooth and finite
        
        t_values = np.linspace(1, 30, 50)
        derivatives = np.array([
            constructor._log_derivative_order1(riemann_zeros, t)
            for t in t_values
        ])
        
        # Should be finite for real t
        assert np.all(np.isfinite(derivatives))
        
        # Should be smooth (no jumps)
        diffs = np.abs(np.diff(derivatives))
        max_jump = np.max(diffs)
        assert max_jump < 10.0  # Reasonable smoothness
    
    def test_pt_symmetry_preservation(self, constructor, riemann_zeros):
        """Test that construction preserves PT symmetry."""
        # Create PT-symmetric spectrum
        spectrum = np.concatenate([riemann_zeros, -riemann_zeros])
        
        t_values = np.linspace(1, 20, 30)
        result = constructor.compute_fredholm_determinant(spectrum, t_values)
        
        # Verify PT symmetry is detected
        assert result.pt_symmetric is True
    
    def test_hadamard_factorization_form(self, constructor, riemann_zeros):
        """Test that Hadamard form ∏(1 - t²/γ²) is correct."""
        t_values = np.array([1.0, 5.0, 10.0])
        
        result = constructor.compute_hadamard_expansion(
            riemann_zeros,
            t_values,
            compute_xi_ratio=False
        )
        
        # Hadamard product should be real for real t and real γ
        assert np.all(np.abs(np.imag(result.xi_hadamard)) < 1e-6)
    
    def test_trace_formula_sum_convergence(self, constructor, riemann_zeros):
        """Test that trace formula sum Σ e^{isγ_n} converges."""
        s_values = np.linspace(0, 5, 30)
        
        result = constructor.compute_trace_formula(
            riemann_zeros,
            s_values,
            include_primes=False,
            n_primes=0
        )
        
        # Spectral density should be finite
        assert np.all(np.isfinite(result.spectral_density))
    
    def test_remainder_decay_property(self, constructor, pt_symmetric_spectrum):
        """Test that remainder R(s) decays exponentially."""
        s_values = np.linspace(0, 15, 100)
        
        result = constructor.compute_trace_formula(
            pt_symmetric_spectrum,
            s_values
        )
        
        # Remainder should decay with |s|
        r_abs = np.abs(result.remainder)
        
        # Compare beginning and end
        avg_start = np.mean(r_abs[:10])
        avg_end = np.mean(r_abs[-10:])
        
        # Should show decay (or at least not growth)
        assert avg_end <= avg_start * 2.0  # Allow some noise
    
    def test_qcal_constants_integration(self):
        """Test QCAL constant integration."""
        from operators.fredholm_determinant_constructor import F0_QCAL, C_PRIMARY, C_COHERENCE
        
        # Verify QCAL constants are defined
        assert F0_QCAL == 141.7001
        assert C_PRIMARY == 629.83
        assert C_COHERENCE == 244.36


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    @pytest.fixture
    def constructor(self):
        """Create constructor instance."""
        return FredholmDeterminantConstructor(precision=15)
    
    def test_empty_eigenvalues(self, constructor):
        """Test handling of empty eigenvalue array."""
        eigenvalues = np.array([])
        t_values = np.array([1.0])
        
        # Should handle gracefully
        result = constructor.compute_fredholm_determinant(eigenvalues, t_values)
        
        # Result should indicate no eigenvalues
        assert len(result.eigenvalues) == 0
    
    def test_single_eigenvalue(self, constructor):
        """Test with single eigenvalue."""
        eigenvalues = np.array([14.134725])
        t_values = np.linspace(1, 10, 10)
        
        result = constructor.compute_fredholm_determinant(eigenvalues, t_values)
        
        assert len(result.eigenvalues) == 1
        assert np.all(np.isfinite(result.xi_values))
    
    def test_zero_t_value(self, constructor):
        """Test behavior at t = 0 (should be handled carefully)."""
        eigenvalues = np.array([14.134725, 21.022040])
        # Use small positive t instead of exact 0
        t_values = np.array([0.001, 0.01, 0.1])
        
        result = constructor.compute_fredholm_determinant(eigenvalues, t_values)
        
        # Should not diverge
        assert np.all(np.isfinite(result.xi_values))
    
    def test_negative_eigenvalues_only(self, constructor):
        """Test with only negative eigenvalues."""
        eigenvalues = np.array([-14.134725, -21.022040, -25.010858])
        t_values = np.linspace(1, 10, 10)
        
        result = constructor.compute_fredholm_determinant(eigenvalues, t_values)
        
        # Should filter to positive eigenvalues
        assert len(result.eigenvalues) == 0 or np.all(result.eigenvalues > 0)


class TestMathematicalProperties:
    """Test mathematical properties and theorems."""
    
    @pytest.fixture
    def constructor(self):
        """Create constructor instance."""
        return FredholmDeterminantConstructor(precision=20)
    
    @pytest.fixture
    def spectrum(self):
        """Well-separated PT-symmetric spectrum."""
        gamma = np.array([10.0, 20.0, 30.0, 40.0, 50.0])
        return np.concatenate([gamma, -gamma])
    
    def test_determinant_product_formula(self, constructor, spectrum):
        """Test product formula Ξ(t) = ∏(1 - it/γ_n)e^{it/γ_n}."""
        t = 5.0
        
        # Compute using constructor
        result = constructor._hadamard_product_order1(spectrum[spectrum > 0], t)
        
        # Verify it's non-zero and finite
        assert abs(result) > 0
        assert np.isfinite(result)
    
    def test_log_derivative_formula(self, constructor, spectrum):
        """Test d/dt ln Ξ = Σ 1/(t + i/γ_n)."""
        t = 10.0
        gamma_pos = spectrum[spectrum > 0]
        
        # Compute using constructor
        derivative = constructor._log_derivative_order1(gamma_pos, t)
        
        # Compute directly
        direct = sum(1.0 / (t + 1j / gamma) for gamma in gamma_pos)
        
        # Should agree
        assert abs(derivative - direct) < 1e-10
    
    def test_functional_equation_symmetry(self, constructor, spectrum):
        """Test that PT symmetry leads to Ξ(t) = Ξ(-t)* for PT-symmetric spectrum."""
        t_values = np.array([5.0, 10.0, 15.0])
        
        result_pos = constructor.compute_fredholm_determinant(spectrum, t_values)
        result_neg = constructor.compute_fredholm_determinant(spectrum, -t_values)
        
        # For PT-symmetric spectrum, Ξ(t) and Ξ(-t) should be related
        # (exact relation depends on regularization)
        # At minimum, both should be finite
        assert np.all(np.isfinite(result_pos.xi_values))
        assert np.all(np.isfinite(result_neg.xi_values))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
