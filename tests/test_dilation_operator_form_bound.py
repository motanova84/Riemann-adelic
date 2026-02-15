"""
Tests for dilation operator and form-boundedness of x² by T²

Validates:
1. Operator T = -i(x∂_x + 1/2) implementation
2. Hardy inequality in y-coordinates
3. Form-boundedness |⟨ψ, x²ψ⟩| ≤ a‖Tψ‖² + b‖ψ‖²
4. Mellin transform shift property
5. KLMN theorem conditions
"""

import pytest
import numpy as np
import sys
import os

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from dilation_operator_form_bound import (
    DilationOperator,
    generate_test_function,
    verify_klmn_conditions,
    FormBoundResult
)


class TestDilationOperator:
    """Test basic dilation operator functionality"""
    
    def test_operator_initialization(self):
        """Test that operator initializes correctly"""
        op = DilationOperator(x_min=1e-4, x_max=100.0, n_points=512)
        
        assert op.x_min == 1e-4
        assert op.x_max == 100.0
        assert op.n_points == 512
        assert len(op.x) == 512
        assert len(op.y) == 512
        
    def test_coordinate_transformation(self):
        """Test y = ln(x) transformation"""
        op = DilationOperator(n_points=512)
        
        # y should be ln(x)
        y_expected = np.log(op.x)
        np.testing.assert_allclose(op.y, y_expected, rtol=1e-10)
        
        # y should be uniformly spaced
        dy = np.diff(op.y)
        np.testing.assert_allclose(dy, op.dy, rtol=1e-10)
        
    def test_inner_product(self):
        """Test L² inner product"""
        op = DilationOperator(n_points=512)
        
        # Test with simple functions
        psi1 = np.exp(-op.x)
        psi2 = np.exp(-2*op.x)
        
        # Inner product should be real and positive
        ip = op.inner_product(psi1, psi1)
        assert np.abs(np.imag(ip)) < 1e-10
        assert np.real(ip) > 0
        
        # Conjugate symmetry
        ip12 = op.inner_product(psi1, psi2)
        ip21 = op.inner_product(psi2, psi1)
        np.testing.assert_allclose(ip12, np.conj(ip21), rtol=1e-8)
        
    def test_norm_computation(self):
        """Test L² norm computation"""
        op = DilationOperator(n_points=512)
        
        # Normalized function should have norm ≈ 1
        psi = generate_test_function(op.x, mode='gaussian')
        norm = op.norm(psi)
        
        assert 0.9 < norm < 1.1  # Should be close to 1
        
    def test_T_operator_action(self):
        """Test action of T = -i(x∂_x + 1/2)"""
        op = DilationOperator(n_points=1024)
        
        # For ψ(x) = x^α, Tψ = -i(α + 1/2)x^α
        alpha = 1.5
        psi = op.x**alpha
        T_psi = op.apply_T(psi)
        T_psi_expected = -1j * (alpha + 0.5) * op.x**alpha
        
        # Should match up to numerical derivative error
        np.testing.assert_allclose(T_psi, T_psi_expected, rtol=0.1)
        
    def test_V_operator_action(self):
        """Test potential operator V(x) = x²"""
        op = DilationOperator(n_points=512)
        
        psi = np.exp(-op.x)
        V_psi = op.apply_V(psi)
        V_psi_expected = op.x**2 * psi
        
        np.testing.assert_allclose(V_psi, V_psi_expected, rtol=1e-12)


class TestCoordinateTransformations:
    """Test transformations between x and y coordinates"""
    
    def test_transform_to_y(self):
        """Test ψ(x) → φ(y) transformation"""
        op = DilationOperator(n_points=512)
        
        psi_x = np.exp(-op.x)
        phi_y = op.transform_to_y(psi_x)
        
        # φ(y) = √x ψ(x) = e^(y/2) ψ(e^y)
        phi_y_expected = np.sqrt(op.x) * psi_x
        np.testing.assert_allclose(phi_y, phi_y_expected, rtol=1e-12)
        
    def test_transform_roundtrip(self):
        """Test ψ → φ → ψ roundtrip"""
        op = DilationOperator(n_points=512)
        
        psi_original = generate_test_function(op.x, mode='gaussian')
        phi_y = op.transform_to_y(psi_original)
        psi_recovered = op.transform_to_x(phi_y)
        
        np.testing.assert_allclose(psi_recovered, psi_original, rtol=1e-10)
        
    def test_norm_preservation(self):
        """Test that transformation preserves L² norm"""
        op = DilationOperator(n_points=1024)
        
        psi_x = generate_test_function(op.x, mode='gaussian')
        phi_y = op.transform_to_y(psi_x)
        
        # ∫|ψ(x)|² dx = ∫|φ(y)|² dy
        norm_x = op.norm(psi_x)
        norm_y = np.sqrt(np.trapezoid(np.abs(phi_y)**2, op.y))
        
        np.testing.assert_allclose(norm_x, norm_y, rtol=0.01)


class TestHardyInequality:
    """Test Hardy inequality verification"""
    
    def test_hardy_inequality_gaussian(self):
        """Test Hardy inequality for Gaussian function"""
        op = DilationOperator(n_points=2048)
        
        psi = generate_test_function(op.x, mode='gaussian')
        phi_y = op.transform_to_y(psi)
        
        hardy_C, satisfied = op.verify_hardy_inequality(phi_y)
        
        assert satisfied, "Hardy inequality should be satisfied"
        assert hardy_C > 0, "Hardy constant should be positive"
        assert hardy_C < 100, "Hardy constant should be reasonable"
        
    def test_hardy_inequality_exponential(self):
        """Test Hardy inequality for exponential decay"""
        op = DilationOperator(n_points=2048)
        
        psi = generate_test_function(op.x, mode='exponential')
        phi_y = op.transform_to_y(psi)
        
        hardy_C, satisfied = op.verify_hardy_inequality(phi_y)
        
        assert satisfied, "Hardy inequality should be satisfied"
        assert hardy_C > 0
        
    def test_hardy_inequality_schwartz(self):
        """Test Hardy inequality for Schwartz function"""
        op = DilationOperator(n_points=2048)
        
        psi = generate_test_function(op.x, mode='schwartz')
        phi_y = op.transform_to_y(psi)
        
        hardy_C, satisfied = op.verify_hardy_inequality(phi_y)
        
        assert satisfied, "Hardy inequality should be satisfied"
        assert hardy_C > 0


class TestFormBoundedness:
    """Test form-boundedness of x² by T²"""
    
    def test_form_boundedness_gaussian(self):
        """Test form-boundedness for Gaussian"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='gaussian')
        
        result = op.verify_form_boundedness(psi)
        
        assert result.form_bound_satisfied, \
            "Form-boundedness should be satisfied"
        assert result.relative_constant_a < 1.0, \
            "Relative constant a should be < 1"
        assert result.hardy_constant > 0
        assert result.quadratic_form_V >= 0
        assert result.norm_T_psi_squared >= 0
        assert result.norm_psi_squared > 0
        
    def test_form_boundedness_exponential(self):
        """Test form-boundedness for exponential decay"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='exponential')
        
        result = op.verify_form_boundedness(psi)
        
        assert result.form_bound_satisfied
        assert result.relative_constant_a < 1.0
        
    def test_form_boundedness_schwartz(self):
        """Test form-boundedness for Schwartz function"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='schwartz')
        
        result = op.verify_form_boundedness(psi)
        
        assert result.form_bound_satisfied
        assert result.relative_constant_a < 1.0
        
    def test_form_bound_inequality(self):
        """Test explicit inequality |⟨ψ,Vψ⟩| ≤ a‖Tψ‖² + b‖ψ‖²"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='gaussian')
        
        result = op.verify_form_boundedness(psi)
        
        lhs = result.quadratic_form_V
        rhs = (result.relative_constant_a * result.norm_T_psi_squared + 
               result.absolute_constant_b * result.norm_psi_squared)
        
        # LHS ≤ RHS (with small tolerance)
        assert lhs <= rhs * 1.1, f"LHS={lhs} should be ≤ RHS={rhs}"
        
    def test_constant_a_less_than_one(self):
        """Test that constant a < 1 for all test functions"""
        op = DilationOperator(n_points=2048)
        
        for mode in ['gaussian', 'exponential', 'schwartz']:
            psi = generate_test_function(op.x, mode=mode)
            result = op.verify_form_boundedness(psi)
            
            assert result.relative_constant_a < 1.0, \
                f"Constant a={result.relative_constant_a} should be < 1 for {mode}"


class TestMellinTransform:
    """Test Mellin transform properties"""
    
    def test_mellin_transform_computation(self):
        """Test basic Mellin transform computation"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='gaussian')
        
        # Compute for a few λ values
        lambda_vals = [0.0, 1.0, -1.0]
        for lam in lambda_vals:
            psi_hat = op.mellin_transform(psi, lam)
            assert np.isfinite(psi_hat), \
                f"Mellin transform should be finite at λ={lam}"
            
    def test_mellin_shift_property(self):
        """Test that x² acts as shift in Mellin space"""
        op = DilationOperator(n_points=2048)
        psi = generate_test_function(op.x, mode='gaussian')
        
        lambda_samples = np.linspace(-1, 1, 5)
        mellin_direct, mellin_shifted = op.verify_mellin_shift(psi, lambda_samples)
        
        # Should match up to numerical error
        for i, lam in enumerate(lambda_samples):
            error = np.abs(mellin_direct[i] - mellin_shifted[i])
            relative_error = error / (np.abs(mellin_direct[i]) + 1e-10)
            
            # Allow for some numerical error in the transforms
            assert relative_error < 0.5, \
                f"Mellin shift error too large at λ={lam}: {relative_error}"


class TestKLMNConditions:
    """Test KLMN theorem conditions"""
    
    def test_klmn_all_conditions(self):
        """Test that all KLMN conditions are satisfied"""
        op = DilationOperator(n_points=2048)
        
        test_functions = [
            generate_test_function(op.x, mode='gaussian'),
            generate_test_function(op.x, mode='exponential'),
            generate_test_function(op.x, mode='schwartz')
        ]
        
        results = verify_klmn_conditions(op, test_functions)
        
        assert results['T_squared_self_adjoint']
        assert results['V_symmetric']
        assert results['all_satisfied'], \
            "All form-boundedness conditions should be satisfied"
        assert results['max_relative_constant'] < 1.0, \
            f"Max constant a={results['max_relative_constant']} should be < 1"
        
    def test_klmn_multiple_functions(self):
        """Test KLMN with multiple test functions"""
        op = DilationOperator(n_points=2048)
        
        # Generate 5 different test functions
        test_functions = []
        for mode in ['gaussian', 'exponential', 'schwartz']:
            test_functions.append(generate_test_function(op.x, mode=mode))
        
        results = verify_klmn_conditions(op, test_functions)
        
        assert len(results['form_boundedness_verified']) == len(test_functions)
        
        # All should satisfy form-boundedness
        for fb_result in results['form_boundedness_verified']:
            assert fb_result.form_bound_satisfied
            assert fb_result.relative_constant_a < 1.0


class TestNumericalStability:
    """Test numerical stability of implementations"""
    
    def test_different_grid_sizes(self):
        """Test consistency across different grid sizes"""
        grid_sizes = [512, 1024, 2048]
        results = []
        
        for n in grid_sizes:
            op = DilationOperator(n_points=n)
            psi = generate_test_function(op.x, mode='gaussian')
            result = op.verify_form_boundedness(psi)
            results.append(result)
        
        # Hardy constants should be similar across grid sizes
        hardy_constants = [r.hardy_constant for r in results]
        assert np.std(hardy_constants) / np.mean(hardy_constants) < 0.2, \
            "Hardy constant should be stable across grid sizes"
        
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf"""
        op = DilationOperator(n_points=1024)
        
        for mode in ['gaussian', 'exponential', 'schwartz']:
            psi = generate_test_function(op.x, mode=mode)
            result = op.verify_form_boundedness(psi)
            
            assert np.isfinite(result.quadratic_form_V)
            assert np.isfinite(result.norm_T_psi_squared)
            assert np.isfinite(result.norm_psi_squared)
            assert np.isfinite(result.hardy_constant)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
