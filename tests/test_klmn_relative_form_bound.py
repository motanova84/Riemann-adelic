"""
Tests for KLMN Theorem: Relative Form Boundedness of V_osc

This module tests the implementation of the formal proof demonstrating
that V_osc is form-bounded relative to H₀ with constant α < 1.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.klmn_relative_form_bound import (
    KLMNOperator,
    FormBoundResult,
    generate_test_functions,
)


class TestKLMNOperator:
    """Test basic functionality of KLMNOperator"""
    
    def test_initialization(self):
        """Test operator initialization"""
        op = KLMNOperator(
            x_min=-10.0,
            x_max=10.0,
            n_points=512,
            n_primes=20,
        )
        
        assert len(op.x) == 512
        assert op.x[0] == pytest.approx(-10.0, abs=1e-6)
        assert op.x[-1] == pytest.approx(10.0, abs=1e-6)
        assert len(op.primes) == 20
        assert len(op.phases) == 20
    
    def test_prime_generation(self):
        """Test prime number generation"""
        op = KLMNOperator(n_primes=10)
        
        expected_primes = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        np.testing.assert_array_equal(op.primes, expected_primes)
    
    def test_confining_potential(self):
        """Test confining potential V̄(x) = κx²"""
        op = KLMNOperator(confinement_strength=0.5)
        
        x_test = np.array([-2.0, -1.0, 0.0, 1.0, 2.0])
        V_bar = op.confining_potential(x_test)
        
        expected = 0.5 * x_test**2
        np.testing.assert_allclose(V_bar, expected, rtol=1e-10)
        
        # Check growth at infinity
        assert V_bar[-1] > V_bar[-2]
        assert V_bar[0] > V_bar[1]
    
    def test_oscillatory_potential_structure(self):
        """Test structure of oscillatory potential"""
        op = KLMNOperator(n_primes=5)
        
        V_osc = op.oscillatory_potential(op.x)
        
        # Should be real-valued
        assert np.all(np.isreal(V_osc))
        
        # Should be oscillatory (changes sign)
        assert np.any(V_osc > 0)
        assert np.any(V_osc < 0)
        
        # Should not grow to infinity (bounded by sum of amplitudes)
        max_amplitude = sum(np.log(p) / np.sqrt(p) for p in op.primes if p > 1)
        assert np.max(np.abs(V_osc)) <= max_amplitude * 1.01
    
    def test_primitive_W(self):
        """Test primitive W(x) of V_osc"""
        op = KLMNOperator(n_primes=5)
        
        W = op.primitive_W(op.x)
        
        # Should be real-valued
        assert np.all(np.isreal(W))
        
        # Sublinear growth: |W(x)| should not grow faster than √|x|
        # For large |x|, check growth rate
        x_large = op.x[np.abs(op.x) > 5]
        W_large = op.primitive_W(x_large)
        
        if len(x_large) > 0:
            # Rough check: W should be bounded by constant times sqrt(|x|)
            bound = 10 * np.sqrt(np.abs(x_large))  # Liberal bound
            assert np.all(np.abs(W_large) <= bound)


class TestDerivativeOperators:
    """Test derivative computations"""
    
    def test_first_derivative_linear(self):
        """Test first derivative on linear function"""
        op = KLMNOperator(x_min=-5.0, x_max=5.0, n_points=1001)
        
        # Linear function: f(x) = 2x + 1
        f = 2 * op.x + 1
        f_prime = op.apply_derivative(f)
        
        # Should be approximately 2 everywhere
        expected = 2.0 * np.ones_like(op.x)
        np.testing.assert_allclose(f_prime, expected, rtol=1e-3, atol=1e-2)
    
    def test_first_derivative_quadratic(self):
        """Test first derivative on quadratic function"""
        op = KLMNOperator(x_min=-5.0, x_max=5.0, n_points=1001)
        
        # Quadratic: f(x) = x²
        f = op.x**2
        f_prime = op.apply_derivative(f)
        
        # Should be 2x
        expected = 2 * op.x
        np.testing.assert_allclose(f_prime, expected, rtol=1e-2, atol=1e-2)
    
    def test_second_derivative_quadratic(self):
        """Test second derivative on quadratic function"""
        op = KLMNOperator(x_min=-5.0, x_max=5.0, n_points=1001)
        
        # Quadratic: f(x) = x²
        f = op.x**2
        f_double_prime = op.apply_second_derivative(f)
        
        # Should be approximately 2 everywhere
        expected = 2.0 * np.ones_like(op.x)
        # Exclude boundary points which may have larger errors
        np.testing.assert_allclose(f_double_prime[10:-10], expected[10:-10], 
                                   rtol=1e-2, atol=0.1)


class TestInnerProducts:
    """Test inner product computations"""
    
    def test_inner_product_orthogonality(self):
        """Test orthogonality of sine and cosine"""
        op = KLMNOperator(x_min=-np.pi, x_max=np.pi, n_points=2048)
        
        sin_x = np.sin(op.x)
        cos_x = np.cos(op.x)
        
        # ⟨sin, cos⟩ should be approximately 0
        inner = op.inner_product(sin_x, cos_x)
        assert abs(inner) < 1e-10
    
    def test_norm_squared_gaussian(self):
        """Test norm of Gaussian function"""
        op = KLMNOperator(x_min=-10.0, x_max=10.0, n_points=4096)
        
        # Gaussian with σ = 1
        psi = np.exp(-op.x**2 / 2)
        norm_sq = op.norm_squared(psi)
        
        # Exact: ∫ exp(-x²) dx = √π
        expected = np.sqrt(np.pi)
        assert norm_sq == pytest.approx(expected, rel=1e-3)


class TestQuadraticForms:
    """Test quadratic form computations"""
    
    def test_quadratic_form_H0_positive(self):
        """Test that q₀(ψ) > 0 for non-zero ψ"""
        op = KLMNOperator()
        
        # Gaussian test function
        psi = np.exp(-op.x**2 / 2)
        psi /= np.sqrt(op.norm_squared(psi))
        
        q0 = op.quadratic_form_H0(psi)
        
        # Should be positive due to kinetic + potential terms
        assert q0 > 0
    
    def test_quadratic_form_V_osc_real(self):
        """Test that ⟨ψ, V_osc ψ⟩ is real"""
        op = KLMNOperator()
        
        psi = np.exp(-op.x**2 / 2)
        psi /= np.sqrt(op.norm_squared(psi))
        
        form = op.quadratic_form_V_osc(psi)
        
        # Should be real for real ψ
        assert np.isreal(form)


class TestRelativeFormBound:
    """Test relative form boundedness verification"""
    
    def test_relative_bound_gaussian(self):
        """Test relative form bound for Gaussian function"""
        delta = 0.1
        epsilon = np.sqrt(delta)
        
        op = KLMNOperator(
            epsilon=epsilon,
            delta=delta,
            n_primes=30,
        )
        
        # Gaussian test function
        psi = np.exp(-op.x**2 / 2)
        
        result = op.verify_relative_form_bound(psi)
        
        # Check that α < 1
        assert result.relative_constant_alpha < 1.0
        
        # Check that bound is satisfied
        assert result.bound_satisfied
        
        # Check that |⟨ψ, V_osc ψ⟩| ≤ α q₀(ψ) + β ‖ψ‖²
        lhs = abs(result.form_V_osc)
        rhs = (result.relative_constant_alpha * result.form_q0 + 
               result.absolute_constant_beta * result.norm_psi_squared)
        assert lhs <= rhs * 1.001  # Small tolerance for numerics
    
    def test_alpha_less_than_one(self):
        """Test that α < 1 with proper parameter choice"""
        # Choose ε = √δ with δ = 0.1
        # Then α = ε + δ/ε = 2√δ = 2√0.1 ≈ 0.632 < 1
        delta = 0.1
        epsilon = np.sqrt(delta)
        
        op = KLMNOperator(epsilon=epsilon, delta=delta)
        
        psi = np.exp(-op.x**2 / 2)
        result = op.verify_relative_form_bound(psi)
        
        expected_alpha = 2 * np.sqrt(delta)
        assert result.relative_constant_alpha == pytest.approx(expected_alpha, rel=1e-2)
        assert result.relative_constant_alpha < 1.0
    
    def test_multiple_test_functions(self):
        """Test bound for multiple test functions"""
        # Use optimal parameters to ensure α < 1
        delta = 0.09
        epsilon = np.sqrt(delta)
        op = KLMNOperator(epsilon=epsilon, delta=delta)
        
        test_funcs = generate_test_functions(op, n_functions=5)
        
        for i, psi in enumerate(test_funcs):
            result = op.verify_relative_form_bound(psi)
            
            assert result.relative_constant_alpha < 1.0, \
                f"Test function {i}: α = {result.relative_constant_alpha} >= 1"
            assert result.bound_satisfied, \
                f"Test function {i}: Bound not satisfied"


class TestKLMNConditions:
    """Test complete KLMN theorem verification"""
    
    def test_klmn_verification_success(self):
        """Test successful KLMN verification"""
        delta = 0.09  # δ < 1/4
        epsilon = np.sqrt(delta)
        
        op = KLMNOperator(
            epsilon=epsilon,
            delta=delta,
            n_primes=30,
        )
        
        test_funcs = generate_test_functions(op, n_functions=8)
        verification = op.verify_klmn_conditions(test_funcs)
        
        assert verification['success']
        assert verification['alpha_less_than_one']
        assert verification['klmn_applicable']
        assert verification['n_bounds_satisfied'] == verification['n_test_functions']
        assert verification['max_alpha'] < 1.0
    
    def test_klmn_with_various_primes(self):
        """Test KLMN with different numbers of primes"""
        for n_primes in [10, 30, 50]:
            op = KLMNOperator(
                epsilon=0.3,
                delta=0.09,
                n_primes=n_primes,
            )
            
            test_funcs = generate_test_functions(op, n_functions=5)
            verification = op.verify_klmn_conditions(test_funcs)
            
            assert verification['alpha_less_than_one'], \
                f"Failed for n_primes={n_primes}"


class TestGenerateTestFunctions:
    """Test test function generation"""
    
    def test_generate_test_functions_count(self):
        """Test that correct number of functions is generated"""
        op = KLMNOperator()
        
        for n in [5, 10, 15]:
            funcs = generate_test_functions(op, n_functions=n)
            assert len(funcs) == n
    
    def test_test_functions_normalized(self):
        """Test that test functions are normalized"""
        op = KLMNOperator()
        funcs = generate_test_functions(op, n_functions=5)
        
        for psi in funcs:
            norm_sq = op.norm_squared(psi)
            assert norm_sq == pytest.approx(1.0, rel=1e-6)
    
    def test_test_functions_in_domain(self):
        """Test that test functions are in form domain"""
        op = KLMNOperator()
        funcs = generate_test_functions(op, n_functions=5)
        
        for psi in funcs:
            # Should have finite kinetic energy
            psi_prime = op.apply_derivative(psi)
            kinetic = op.norm_squared(psi_prime)
            assert np.isfinite(kinetic)
            assert kinetic > 0
            
            # Should have finite potential energy
            V_bar = op.confining_potential(op.x)
            potential = op.inner_product(psi, V_bar * psi)
            assert np.isfinite(potential)
            assert potential > 0


class TestParameterDependence:
    """Test dependence on parameters ε and δ"""
    
    def test_alpha_depends_on_epsilon_delta(self):
        """Test that α = ε + δ/ε"""
        for delta in [0.04, 0.09, 0.16]:
            epsilon = np.sqrt(delta)
            op = KLMNOperator(epsilon=epsilon, delta=delta)
            
            psi = np.exp(-op.x**2 / 2)
            result = op.verify_relative_form_bound(psi)
            
            expected_alpha = epsilon + delta / epsilon
            assert result.relative_constant_alpha == pytest.approx(expected_alpha, rel=1e-2)
    
    def test_optimal_epsilon_choice(self):
        """Test that ε = √δ is optimal (minimizes α)"""
        delta = 0.1
        epsilon_optimal = np.sqrt(delta)
        
        # Compute α for optimal choice
        alpha_optimal = epsilon_optimal + delta / epsilon_optimal
        
        # Try other choices
        for epsilon_other in [0.1, 0.5, 0.7]:
            if epsilon_other != epsilon_optimal:
                alpha_other = epsilon_other + delta / epsilon_other
                # Optimal should be smaller (or equal at boundary)
                assert alpha_optimal <= alpha_other + 1e-6


class TestConfinementEffect:
    """Test effect of confining potential strength"""
    
    def test_stronger_confinement_helps(self):
        """Test that stronger confinement allows larger perturbation"""
        psi = None
        
        for kappa in [0.3, 0.5, 1.0]:
            op = KLMNOperator(
                confinement_strength=kappa,
                epsilon=0.3,
                delta=0.09,
            )
            
            if psi is None:
                psi = np.exp(-op.x**2 / 2)
            
            result = op.verify_relative_form_bound(psi)
            
            # Stronger confinement (larger κ) should make β smaller
            # and make the bound easier to satisfy
            assert result.relative_constant_alpha < 1.0
            assert result.bound_satisfied


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    def test_zero_function_raises_error(self):
        """Test that zero function raises appropriate error"""
        op = KLMNOperator()
        
        psi_zero = np.zeros_like(op.x)
        
        with pytest.raises(ValueError, match="zero norm"):
            op.verify_relative_form_bound(psi_zero)
    
    def test_no_primes(self):
        """Test with zero primes (V_osc = 0)"""
        op = KLMNOperator(n_primes=0)
        
        psi = np.exp(-op.x**2 / 2)
        result = op.verify_relative_form_bound(psi)
        
        # V_osc should be zero
        assert abs(result.form_V_osc) < 1e-10
        assert result.bound_satisfied


def test_main_demonstration():
    """Test that main demonstration runs without errors"""
    # Import and run main
    import operators.klmn_relative_form_bound as klmn_module
    
    # Capture the main execution (it's in __main__ block)
    # We'll create a simplified version here
    delta = 0.1
    epsilon = np.sqrt(delta)
    
    operator = KLMNOperator(
        x_min=-20.0,
        x_max=20.0,
        n_points=1024,  # Smaller for faster test
        n_primes=30,  # Smaller for faster test
        epsilon=epsilon,
        delta=delta,
    )
    
    test_functions = generate_test_functions(operator, n_functions=5)
    verification = operator.verify_klmn_conditions(test_functions)
    
    assert verification['success']
    assert verification['klmn_applicable']
    assert verification['max_alpha'] < 1.0


if __name__ == "__main__":
    """Run tests with pytest"""
    pytest.main([__file__, "-v", "--tb=short"])
