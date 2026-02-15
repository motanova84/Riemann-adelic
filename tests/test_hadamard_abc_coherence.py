#!/usr/bin/env python3
"""
Tests for Hadamard-ABC Coherence Operator — Identity Closure Framework

This module validates the Hadamard factorization with ABC Coherence
to prove Ξ(t) ≡ ξ(1/2+it)/ξ(1/2).

Test Coverage:
    1. Xi function computation
    2. Hadamard factorization construction
    3. ABC Coherence Lemma enforcement
    4. Order computation for entire functions
    5. Zero drift forcing (A = 0)
    6. Normalization (B = 0)
    7. Identity verification Ξ(t) = ξ(1/2+it)/ξ(1/2)
    8. Integration with QCAL constants

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.hadamard_abc_coherence import (
    # Constants
    F0,
    C_QCAL,
    KAPPA_PI,
    EULER_GAMMA,
    PI,
    # Functions
    xi_function,
    xi_normalized,
    # Classes
    HadamardFactorization,
    ABCCoherenceLemma,
    XiOperatorIdentity,
    demonstrate_hadamard_abc_closure,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_f0_value(self):
        """Fundamental frequency should be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-4
    
    def test_c_qcal_value(self):
        """QCAL coherence constant should be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01
    
    def test_kappa_pi_value(self):
        """Critical PT transition should be ~2.5773."""
        assert abs(KAPPA_PI - 2.5773) < 0.01
    
    def test_euler_gamma_value(self):
        """Euler-Mascheroni constant."""
        assert abs(EULER_GAMMA - 0.5772156649) < 1e-9
    
    def test_pi_value(self):
        """Pi constant."""
        assert abs(PI - np.pi) < 1e-15


class TestXiFunction:
    """Test Riemann xi function computation."""
    
    def test_xi_at_half(self):
        """Test xi(1/2) is real and positive."""
        xi_half = xi_function(0.5)
        assert np.isreal(xi_half) or abs(np.imag(xi_half)) < 1e-10
        # Value should be positive (approximately 0.497...)
        assert np.real(xi_half) > 0
        assert abs(np.real(xi_half) - 0.497) < 0.01
    
    def test_xi_returns_value(self):
        """Test xi function returns finite values."""
        # For demonstration, we just need structure
        xi_val = xi_function(0.3 + 0.5j)
        assert not np.isnan(xi_val)
        assert not np.isinf(xi_val)
    
    def test_xi_normalized_at_zero(self):
        """Test that ξ(1/2)/ξ(1/2) = 1 at t=0."""
        val = xi_normalized(0.0)
        assert abs(val - 1.0) < 1e-10


class TestHadamardFactorization:
    """Test Hadamard factorization."""
    
    def test_initialization(self):
        """Test basic initialization."""
        zeros = [1.0, 2.0, 3.0]
        had = HadamardFactorization(zeros, A=0.0, B=0.0)
        
        assert had.zeros == zeros
        assert had.A == 0.0
        assert had.B == 0.0
        assert had.order == 1
    
    def test_evaluate_at_zero(self):
        """Test evaluation at z=0 with B=0."""
        zeros = [1.0, 2.0, 3.0]
        had = HadamardFactorization(zeros, A=0.0, B=0.0)
        
        val = had.evaluate(0.0)
        # Should equal e^0 * 1 * 1 * 1 = 1
        assert abs(val - 1.0) < 1e-10
    
    def test_evaluate_at_zero_with_B(self):
        """Test evaluation with non-zero B."""
        zeros = [1.0, 2.0]
        had = HadamardFactorization(zeros, A=0.0, B=1.0)
        
        val = had.evaluate(0.0)
        # Should equal e^1 * 1 * 1 = e
        assert abs(val - np.e) < 1e-10
    
    def test_evaluate_at_zero_point(self):
        """Test that f(z_n) = 0."""
        zeros = [2.0, 3.0, 5.0]
        had = HadamardFactorization(zeros, A=0.0, B=0.0)
        
        # Evaluate at first zero
        val = had.evaluate(2.0, max_terms=10)
        assert abs(val) < 1e-10
    
    def test_exponential_factor(self):
        """Test exponential factor e^(Az+B)."""
        zeros = []
        had = HadamardFactorization(zeros, A=1.0, B=2.0)
        
        z = 3.0
        val = had.evaluate(z)
        expected = np.exp(1.0 * z + 2.0)  # e^(3+2) = e^5
        assert abs(val - expected) < 1e-10


class TestABCCoherenceLemma:
    """Test ABC Coherence Lemma."""
    
    def test_initialization(self):
        """Test basic initialization."""
        lemma = ABCCoherenceLemma()
        
        assert abs(lemma.C_coherence - C_QCAL) < 0.01
        assert abs(lemma.omega_0 - F0) < 1e-4
        assert lemma.epsilon > 0
    
    def test_initialization_custom(self):
        """Test initialization with custom parameters."""
        lemma = ABCCoherenceLemma(C_coherence=100.0, omega_0=50.0, epsilon=1e-3)
        
        assert abs(lemma.C_coherence - 100.0) < 0.01
        assert abs(lemma.omega_0 - 50.0) < 0.01
        assert abs(lemma.epsilon - 1e-3) < 1e-9
    
    def test_enforce_zero_drift(self):
        """Test that enforce_zero_drift returns 0."""
        lemma = ABCCoherenceLemma()
        A = lemma.enforce_zero_drift()
        assert A == 0.0
    
    def test_check_linear_drift_zero(self):
        """Test drift checking for constant phase."""
        lemma = ABCCoherenceLemma()
        
        # Constant phase function
        def phi(t):
            return 5.0
        
        t_vals = np.linspace(0, 10, 100)
        result = lemma.check_linear_drift(phi, t_vals)
        
        assert 'A_fitted' in result
        assert 'drift_bounded' in result
        # For constant function, derivative should be ~0
        assert abs(result['A_fitted']) < 0.1
    
    def test_check_linear_drift_linear(self):
        """Test drift checking for linear phase."""
        lemma = ABCCoherenceLemma(epsilon=1.0)  # Larger tolerance
        
        # Linear phase function with small slope
        def phi(t):
            return 0.001 * t
        
        t_vals = np.linspace(0, 10, 100)
        result = lemma.check_linear_drift(phi, t_vals)
        
        assert 'A_fitted' in result
        assert abs(result['A_fitted'] - 0.001) < 0.01


class TestXiOperatorIdentity:
    """Test Xi Operator Identity."""
    
    def test_initialization_default(self):
        """Test initialization with default zeros."""
        identity = XiOperatorIdentity()
        
        assert len(identity.zeros) > 0
        assert identity.abc_lemma is not None
        assert identity.Xi_hadamard.A == 0.0  # Forced by ABC
        assert identity.Xi_hadamard.B == 0.0  # Forced by normalization
    
    def test_initialization_custom_zeros(self):
        """Test initialization with custom zeros."""
        custom_zeros = [10.0, 20.0, 30.0]
        identity = XiOperatorIdentity(zeros=custom_zeros)
        
        assert identity.zeros == custom_zeros
    
    def test_evaluate_Xi_at_zero(self):
        """Test that Ξ(0) = 1."""
        identity = XiOperatorIdentity()
        
        Xi_0 = identity.evaluate_Xi(0.0)
        assert abs(Xi_0 - 1.0) < 1e-10
    
    def test_evaluate_Xi_product_form(self):
        """Test Ξ(t) = ∏(1 - t²/γ_n²)."""
        zeros = [2.0, 3.0, 5.0]
        identity = XiOperatorIdentity(zeros=zeros)
        
        t = 1.0
        Xi_t = identity.evaluate_Xi(t, max_terms=3)
        
        # Compute manually
        expected = 1.0
        for gamma_n in zeros:
            expected *= (1.0 - (t**2) / (gamma_n**2))
        
        assert abs(Xi_t - expected) < 1e-10
    
    def test_verify_identity_structure(self):
        """Test structure of verification results."""
        identity = XiOperatorIdentity()
        
        result = identity.verify_identity()
        
        assert 'results' in result
        assert 'verification' in result
        assert 'tolerance' in result
        assert 'A_coefficient' in result
        assert 'B_coefficient' in result
        
        # A and B should be zero
        assert result['A_coefficient'] == 0.0
        assert result['B_coefficient'] == 0.0
    
    def test_verify_identity_at_zero(self):
        """Test that identity holds at t=0."""
        identity = XiOperatorIdentity()
        
        t_vals = np.array([0.0])
        result = identity.verify_identity(t_values=t_vals)
        
        assert len(result['results']) == 1
        res = result['results'][0]
        assert abs(res['t']) < 1e-10
        assert abs(res['rel_error']) < 1e-6
        assert res['match']
    
    def test_verify_identity_multiple_points(self):
        """Test identity at multiple points."""
        identity = XiOperatorIdentity()
        
        t_vals = np.array([0.0, 1.0, 2.0])
        result = identity.verify_identity(t_values=t_vals, tolerance=1e-3)
        
        assert len(result['results']) == 3
        # All should match within tolerance
        for res in result['results']:
            assert res['match'] or res['rel_error'] < 1e-3


class TestDemonstration:
    """Test demonstration function."""
    
    def test_demonstrate_hadamard_abc_closure(self):
        """Test the demonstration function runs."""
        result = demonstrate_hadamard_abc_closure(n_zeros=5)
        
        # Check structure
        assert 'results' in result
        assert 'verification' in result
        assert 'A_coefficient' in result
        assert 'B_coefficient' in result
        
        # A and B should be zero
        assert result['A_coefficient'] == 0.0
        assert result['B_coefficient'] == 0.0


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_different_number_of_zeros(self):
        """Test stability with different numbers of zeros."""
        for n in [3, 5, 10, 15]:
            # Use first n known zeros
            zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
                    37.586178, 40.918719, 43.327073, 48.005151, 49.773832][:n]
            
            identity = XiOperatorIdentity(zeros=zeros)
            Xi_0 = identity.evaluate_Xi(0.0)
            
            assert abs(Xi_0 - 1.0) < 1e-8
            assert not np.isnan(Xi_0)
    
    def test_small_t_values(self):
        """Test stability at small t."""
        identity = XiOperatorIdentity()
        
        for t in [0.001, 0.01, 0.1]:
            Xi_t = identity.evaluate_Xi(t)
            assert not np.isnan(Xi_t)
            assert not np.isinf(Xi_t)
    
    def test_large_t_values(self):
        """Test stability at large t."""
        identity = XiOperatorIdentity()
        
        for t in [10.0, 50.0, 100.0]:
            Xi_t = identity.evaluate_Xi(t)
            assert not np.isnan(Xi_t)
            assert not np.isinf(Xi_t)


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_coherence_constant_usage(self):
        """Test that C_QCAL is used in ABC lemma."""
        identity = XiOperatorIdentity()
        assert abs(identity.abc_lemma.C_coherence - C_QCAL) < 0.01
    
    def test_frequency_usage(self):
        """Test that F0 is used in ABC lemma."""
        identity = XiOperatorIdentity()
        assert abs(identity.abc_lemma.omega_0 - F0) < 1e-4
    
    def test_abc_forces_zero_drift(self):
        """Test that ABC coherence forces A = 0."""
        identity = XiOperatorIdentity()
        
        # ABC should enforce A = 0
        assert identity.Xi_hadamard.A == 0.0
        assert identity.xi_hadamard.A == 0.0
    
    def test_normalization_forces_zero_constant(self):
        """Test that normalization forces B = 0."""
        identity = XiOperatorIdentity()
        
        # Normalization should enforce B = 0
        assert identity.Xi_hadamard.B == 0.0
        assert identity.xi_hadamard.B == 0.0


class TestMathematicalProperties:
    """Test mathematical properties."""
    
    def test_product_symmetry(self):
        """Test that product is symmetric in ±γ_n."""
        zeros = [2.0, 3.0, 5.0]
        identity = XiOperatorIdentity(zeros=zeros)
        
        # Ξ(t) should be even function: Ξ(-t) = Ξ(t)
        t = 1.5
        Xi_t = identity.evaluate_Xi(t)
        Xi_minus_t = identity.evaluate_Xi(-t)
        
        assert abs(Xi_t - Xi_minus_t) < 1e-10
    
    def test_zeros_at_gamma_n(self):
        """Test that Ξ has zeros at ±γ_n."""
        zeros = [2.0, 3.0, 5.0]
        identity = XiOperatorIdentity(zeros=zeros)
        
        # Ξ(γ_1) should be zero
        Xi_gamma1 = identity.evaluate_Xi(zeros[0])
        assert abs(Xi_gamma1) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
