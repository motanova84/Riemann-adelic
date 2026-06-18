#!/usr/bin/env python3
"""
Tests for Correlation Kernel Operator (VÍA 🥇)
==============================================

Comprehensive test suite for the correlation kernel framework that derives
κ_int as the maximum eigenvalue of the spectral correlation operator.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from correlation_kernel_operator import (
    weyl_density,
    weyl_counting_function,
    correlation_kernel,
    kernel_matrix,
    verify_kernel_symmetry,
    verify_hilbert_schmidt,
    verify_positive_definiteness,
    compute_kappa_int,
    analytical_kappa_int,
    validate_correlation_kernel_framework,
    F0,
    PHI,
    KAPPA_THEORETICAL
)


# =============================================================================
# TEST 1: WEYL DENSITY AND COUNTING FUNCTION
# =============================================================================

class TestWeylDensity:
    """Test Weyl density ρ̄(x) = (1/2π) ln(x)."""
    
    def test_weyl_density_basic(self):
        """Test basic Weyl density computation."""
        x = np.array([1.0, np.e, 10.0])
        rho = weyl_density(x)
        
        # ρ̄(1) = 0
        assert abs(rho[0]) < 1e-10
        
        # ρ̄(e) = 1/(2π)
        assert abs(rho[1] - 1/(2*np.pi)) < 1e-10
        
        # ρ̄(10) = ln(10)/(2π)
        expected = np.log(10) / (2 * np.pi)
        assert abs(rho[2] - expected) < 1e-10
    
    def test_weyl_density_positive_only(self):
        """Test that Weyl density requires positive x."""
        with pytest.raises(ValueError):
            weyl_density(np.array([0.0, 1.0]))
        
        with pytest.raises(ValueError):
            weyl_density(np.array([-1.0, 1.0]))
    
    def test_weyl_density_monotonic(self):
        """Test that Weyl density is monotonically increasing."""
        x = np.linspace(1.0, 100.0, 50)
        rho = weyl_density(x)
        
        # Should be strictly increasing
        assert np.all(np.diff(rho) > 0)


class TestWeylCountingFunction:
    """Test Weyl counting function N̄(x)."""
    
    def test_counting_function_basic(self):
        """Test basic counting function computation."""
        x = np.array([1.0, 10.0, 100.0])
        N = weyl_counting_function(x)
        
        # All should be finite
        assert np.all(np.isfinite(N))
        
        # Should be increasing
        assert N[1] > N[0]
        assert N[2] > N[1]
    
    def test_counting_function_derivative(self):
        """Test that dN̄/dx ≈ ρ̄(x)."""
        x = np.linspace(2.0, 50.0, 100)
        N = weyl_counting_function(x)
        rho = weyl_density(x)
        
        # Numerical derivative
        dx = x[1] - x[0]
        dN_dx = np.gradient(N, dx)
        
        # Should match density (within numerical error)
        relative_error = np.abs(dN_dx - rho) / (rho + 1e-10)
        assert np.mean(relative_error) < 0.05  # 5% average error


# =============================================================================
# TEST 2: CORRELATION KERNEL
# =============================================================================

class TestCorrelationKernel:
    """Test correlation kernel K(x,y)."""
    
    def test_kernel_symmetry(self):
        """Test K(x,y) = K(y,x)."""
        x = 5.0
        y = 10.0
        
        K_xy = correlation_kernel(x, y)
        K_yx = correlation_kernel(y, x)
        
        assert abs(K_xy - K_yx) < 1e-10
    
    def test_kernel_diagonal(self):
        """Test kernel behavior on diagonal x=y."""
        x = np.array([5.0, 10.0, 20.0])
        
        # K(x,x) should be regularized (not infinite)
        K_diag = correlation_kernel(x, x)
        
        assert np.all(np.isfinite(K_diag))
    
    def test_kernel_decay(self):
        """Test kernel decays as |x-y| increases."""
        x = 10.0
        y_values = np.array([11.0, 15.0, 20.0, 30.0])
        
        K_values = correlation_kernel(x, y_values)
        
        # Should generally decay (in magnitude)
        # Note: oscillations from sine, so we check trend
        magnitudes = np.abs(K_values)
        
        # At least the furthest should be smaller than nearest
        assert magnitudes[-1] < magnitudes[0]
    
    def test_kernel_finite(self):
        """Test kernel values are finite."""
        x = np.linspace(1.0, 50.0, 20)
        y = np.linspace(1.0, 50.0, 20)
        X, Y = np.meshgrid(x, y)
        
        K = correlation_kernel(X, Y)
        
        assert np.all(np.isfinite(K))


class TestKernelMatrix:
    """Test kernel matrix construction."""
    
    def test_kernel_matrix_symmetry(self):
        """Test that kernel matrix is symmetric."""
        x_grid = np.linspace(2.0, 20.0, 30)
        K = kernel_matrix(x_grid)
        
        # Check symmetry
        asymmetry = np.max(np.abs(K - K.T))
        assert asymmetry < 1e-10
    
    def test_kernel_matrix_shape(self):
        """Test kernel matrix has correct shape."""
        n = 25
        x_grid = np.linspace(1.0, 30.0, n)
        K = kernel_matrix(x_grid)
        
        assert K.shape == (n, n)
    
    def test_kernel_matrix_finite(self):
        """Test all matrix elements are finite."""
        x_grid = np.linspace(1.0, 40.0, 35)
        K = kernel_matrix(x_grid)
        
        assert np.all(np.isfinite(K))


# =============================================================================
# TEST 3: KERNEL PROPERTIES
# =============================================================================

class TestKernelProperties:
    """Test mathematical properties of the kernel."""
    
    def test_verify_kernel_symmetry(self):
        """Test kernel symmetry verification."""
        x_grid = np.linspace(2.0, 25.0, 30)
        is_symmetric, max_asymmetry = verify_kernel_symmetry(x_grid)
        
        assert is_symmetric
        assert max_asymmetry < 1e-9
    
    def test_verify_hilbert_schmidt(self):
        """Test Hilbert-Schmidt property."""
        is_hs, hs_norm = verify_hilbert_schmidt(
            x_min=1.0,
            x_max=30.0,
            n_grid=40
        )
        
        assert is_hs
        assert np.isfinite(hs_norm)
        assert hs_norm > 0
    
    def test_verify_positive_definiteness(self):
        """Test positive definiteness."""
        x_grid = np.linspace(2.0, 20.0, 30)
        is_positive, eigenvalues = verify_positive_definiteness(x_grid)
        
        # Should be (mostly) positive
        # Small negative values due to numerics are OK
        assert is_positive or np.min(eigenvalues) > -1e-8


# =============================================================================
# TEST 4: EIGENVALUE COMPUTATION
# =============================================================================

class TestEigenvalueComputation:
    """Test κ_int eigenvalue computation."""
    
    def test_compute_kappa_int_basic(self):
        """Test basic κ_int computation."""
        result = compute_kappa_int(
            x_min=1.0,
            x_max=30.0,
            n_grid=80,
            return_eigenfunction=True,
            auto_scale=True
        )
        
        # Check result structure
        assert 'kappa_int' in result
        assert 'eigenvalues' in result
        assert 'x_grid' in result
        assert 'eigenfunction' in result
        assert 'scaling_factor' in result
        
        # κ_int should be positive and finite
        kappa = result['kappa_int']
        assert np.isfinite(kappa)
        assert kappa > 0
    
    def test_eigenvalues_sorted(self):
        """Test eigenvalues are sorted descending."""
        result = compute_kappa_int(x_min=1.0, x_max=25.0, n_grid=60)
        
        eigenvalues = result['eigenvalues']
        
        # Should be sorted descending
        assert np.all(np.diff(eigenvalues) <= 0)
    
    def test_maximum_eigenvalue(self):
        """Test κ_int is indeed the maximum eigenvalue."""
        result = compute_kappa_int(x_min=1.0, x_max=30.0, n_grid=70)
        
        kappa_int = result['kappa_int']
        eigenvalues = result['eigenvalues']
        
        # κ_int should be the first (largest) eigenvalue
        assert abs(kappa_int - eigenvalues[0]) < 1e-12
        
        # Should be larger than all others
        assert np.all(kappa_int >= eigenvalues)
    
    def test_eigenfunction_normalization(self):
        """Test eigenfunction is normalized."""
        result = compute_kappa_int(
            x_min=1.0,
            x_max=25.0,
            n_grid=60,
            return_eigenfunction=True
        )
        
        eigenfunction = result['eigenfunction']
        
        # Discrete L² norm
        norm_squared = np.sum(eigenfunction**2)
        
        # Should be approximately 1 (up to grid spacing)
        # The eigenvectors from eigh are normalized
        assert abs(norm_squared - 1.0) < 0.1


# =============================================================================
# TEST 5: ANALYTICAL FORMULA
# =============================================================================

class TestAnalyticalFormula:
    """Test analytical κ_int = 4π/(f₀·Φ) formula."""
    
    def test_analytical_kappa_int_default(self):
        """Test analytical formula with default parameters."""
        kappa = analytical_kappa_int()
        
        # Should match KAPPA_THEORETICAL
        assert abs(kappa - KAPPA_THEORETICAL) < 1e-10
    
    def test_analytical_formula_value(self):
        """Test analytical formula gives expected value."""
        kappa = analytical_kappa_int(f0=F0, phi=PHI)
        
        # Expected: 4π / (141.7001 * 1.618...) ≈ 2.577
        expected = 4 * np.pi / (F0 * PHI)
        
        assert abs(kappa - expected) < 1e-10
        assert 2.5 < kappa < 2.6  # Rough check
    
    def test_analytical_formula_custom_params(self):
        """Test analytical formula with custom parameters."""
        f0_custom = 100.0
        phi_custom = 2.0
        
        kappa = analytical_kappa_int(f0=f0_custom, phi=phi_custom)
        
        expected = 4 * np.pi / (f0_custom * phi_custom)
        assert abs(kappa - expected) < 1e-10


# =============================================================================
# TEST 6: NUMERICAL VS ANALYTICAL COMPARISON
# =============================================================================

class TestNumericalVsAnalytical:
    """Compare numerical and analytical κ_int."""
    
    def test_basic_agreement(self):
        """Test that numerical and analytical κ_int agree with auto-scaling."""
        # Numerical computation with auto-scaling
        result = compute_kappa_int(x_min=1.0, x_max=50.0, n_grid=120, auto_scale=True)
        kappa_numerical = result['kappa_int']
        
        # Analytical formula
        kappa_analytical = analytical_kappa_int()
        
        # With auto-scaling, they should match very closely
        relative_error = abs(kappa_numerical - kappa_analytical) / kappa_analytical
        
        assert relative_error < 0.01  # 1% tolerance with auto-scaling
    
    def test_convergence_with_grid_size(self):
        """Test numerical κ_int converges as grid size increases."""
        grid_sizes = [50, 80, 120]
        kappas = []
        
        for n in grid_sizes:
            result = compute_kappa_int(x_min=1.0, x_max=40.0, n_grid=n)
            kappas.append(result['kappa_int'])
        
        # Should be converging (variations decreasing)
        variations = [abs(kappas[i+1] - kappas[i]) for i in range(len(kappas)-1)]
        
        # Later variations should generally be smaller
        # (though not guaranteed monotonically)
        assert np.mean(variations) < 0.5  # Reasonable variation


# =============================================================================
# TEST 7: COMPLETE VALIDATION FRAMEWORK
# =============================================================================

class TestValidationFramework:
    """Test complete validation framework."""
    
    def test_validate_framework_runs(self):
        """Test that validation framework runs without errors."""
        results = validate_correlation_kernel_framework(
            x_min=1.0,
            x_max=30.0,
            n_grid=80,
            verbose=False
        )
        
        # Should return results dictionary
        assert isinstance(results, dict)
        assert 'status' in results
        assert 'tests_passed' in results
        assert 'tests_total' in results
    
    def test_validate_framework_status(self):
        """Test validation framework returns valid status."""
        results = validate_correlation_kernel_framework(
            x_min=1.0,
            x_max=35.0,
            n_grid=90,
            verbose=False
        )
        
        status = results['status']
        assert status in ['PASSED', 'MOSTLY_PASSED', 'FAILED', 'INCOMPLETE']
    
    def test_validate_framework_symmetry_check(self):
        """Test symmetry check in validation."""
        results = validate_correlation_kernel_framework(
            x_min=2.0,
            x_max=25.0,
            n_grid=60,
            verbose=False
        )
        
        assert 'symmetry' in results
        assert 'passed' in results['symmetry']
        
        # Symmetry should pass
        assert results['symmetry']['passed']
    
    def test_validate_framework_kappa_values(self):
        """Test κ_int values in validation."""
        results = validate_correlation_kernel_framework(
            x_min=1.0,
            x_max=40.0,
            n_grid=100,
            verbose=False
        )
        
        # Should have both numerical and analytical κ
        assert 'kappa_numerical' in results
        assert 'kappa_analytical' in results
        
        kappa_num = results['kappa_numerical']
        kappa_ana = results['kappa_analytical']
        
        # Both should be positive and finite
        assert np.isfinite(kappa_num) and kappa_num > 0
        assert np.isfinite(kappa_ana) and kappa_ana > 0
    
    def test_validate_framework_comparison(self):
        """Test numerical-analytical comparison in validation."""
        results = validate_correlation_kernel_framework(
            x_min=1.0,
            x_max=35.0,
            n_grid=85,
            verbose=False
        )
        
        assert 'comparison' in results
        comparison = results['comparison']
        
        assert 'relative_error' in comparison
        assert 'agrees' in comparison
        
        # Error should be finite
        assert np.isfinite(comparison['relative_error'])


# =============================================================================
# TEST 8: EDGE CASES AND ROBUSTNESS
# =============================================================================

class TestEdgeCases:
    """Test edge cases and numerical robustness."""
    
    def test_small_domain(self):
        """Test with small domain."""
        result = compute_kappa_int(x_min=1.0, x_max=5.0, n_grid=30)
        
        assert np.isfinite(result['kappa_int'])
        assert result['kappa_int'] > 0
    
    def test_large_domain(self):
        """Test with large domain."""
        result = compute_kappa_int(x_min=1.0, x_max=100.0, n_grid=80)
        
        assert np.isfinite(result['kappa_int'])
        assert result['kappa_int'] > 0
    
    def test_sparse_grid(self):
        """Test with sparse grid."""
        result = compute_kappa_int(x_min=1.0, x_max=30.0, n_grid=20)
        
        assert np.isfinite(result['kappa_int'])
        assert result['kappa_int'] > 0
    
    def test_dense_grid(self):
        """Test with dense grid."""
        result = compute_kappa_int(x_min=1.0, x_max=30.0, n_grid=200)
        
        assert np.isfinite(result['kappa_int'])
        assert result['kappa_int'] > 0


# =============================================================================
# TEST 9: MATHEMATICAL CONSISTENCY
# =============================================================================

class TestMathematicalConsistency:
    """Test mathematical consistency of the framework."""
    
    def test_kappa_in_expected_range(self):
        """Test κ_int is in expected range around 2.577."""
        result = compute_kappa_int(x_min=1.0, x_max=40.0, n_grid=100, auto_scale=True)
        kappa = result['kappa_int']
        
        # κ_int should be close to 2.577
        assert 2.5 < kappa < 2.6
    
    def test_eigenvalue_spectrum_decay(self):
        """Test eigenvalues decay reasonably."""
        result = compute_kappa_int(x_min=1.0, x_max=35.0, n_grid=80)
        eigenvalues = result['eigenvalues']
        
        # First eigenvalue should be significantly larger than mean
        mean_eigenvalue = np.mean(eigenvalues)
        assert eigenvalues[0] > 2 * mean_eigenvalue
    
    def test_theoretical_constant_value(self):
        """Test KAPPA_THEORETICAL is approximately 2.577."""
        assert abs(KAPPA_THEORETICAL - 2.577) < 0.05


# =============================================================================
# INTEGRATION TEST
# =============================================================================

class TestIntegration:
    """Integration test of full framework."""
    
    def test_full_pipeline(self):
        """Test complete pipeline from kernel to κ_int."""
        # 1. Create grid
        x_grid = np.linspace(1.0, 30.0, 70)
        
        # 2. Build kernel matrix
        K = kernel_matrix(x_grid)
        
        # 3. Verify properties
        is_sym, _ = verify_kernel_symmetry(x_grid)
        assert is_sym
        
        # 4. Compute eigenvalues
        result = compute_kappa_int(x_min=1.0, x_max=30.0, n_grid=70)
        kappa_num = result['kappa_int']
        
        # 5. Compare with analytical
        kappa_ana = analytical_kappa_int()
        
        # 6. Check agreement
        assert np.isfinite(kappa_num)
        assert np.isfinite(kappa_ana)
        
        # Should be same order of magnitude
        ratio = kappa_num / kappa_ana
        assert 0.5 < ratio < 2.0


# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
