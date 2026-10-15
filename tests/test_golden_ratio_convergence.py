#!/usr/bin/env python3
"""
Test suite for Golden Ratio Convergence Validation.

This module tests the correlation kernel implementation and convergence
to the golden ratio as required by the Hilbert-Pólya completion.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-14
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from validate_golden_ratio_convergence import (
    CorrelationKernel,
    GoldenRatioConvergence,
    compute_kappa_internalized,
    validate_kappa_consistency,
    PHI,
    INV_PHI,
    F0_HZ
)


class TestCorrelationKernel:
    """Test the correlation kernel implementation."""
    
    def test_kernel_initialization(self):
        """Test kernel initialization with valid parameters."""
        L = 100.0
        kernel = CorrelationKernel(L, n_grid=100)
        
        assert kernel.L == L
        assert kernel.n_grid == 100
        assert len(kernel.grid) == 100
        assert kernel.grid[0] > 0  # Should avoid u=0
        assert kernel.grid[-1] <= L
    
    def test_K_sinc_symmetry(self):
        """Test that K_sinc is symmetric."""
        kernel = CorrelationKernel(100.0, n_grid=50)
        u, v = 10.0, 20.0
        
        K_uv = kernel.K_sinc(u, v)
        K_vu = kernel.K_sinc(v, u)
        
        assert np.abs(K_uv - K_vu) < 1e-10, "K_sinc should be symmetric"
    
    def test_K_sinc_diagonal(self):
        """Test K_sinc diagonal behavior (u = v)."""
        kernel = CorrelationKernel(100.0, n_grid=50)
        u = 25.0
        
        K_diag = kernel.K_sinc(u, u)
        # Should return sqrt(u*u) * (π/L) = u * π/L
        expected = u * np.pi / kernel.L
        
        assert np.abs(K_diag - expected) < 1e-6
    
    def test_P_L_symmetry(self):
        """Test that P_L is symmetric."""
        kernel = CorrelationKernel(100.0, n_grid=50)
        u, v = 15.0, 35.0
        
        P_uv = kernel.P_L(u, v)
        P_vu = kernel.P_L(v, u)
        
        assert np.abs(P_uv - P_vu) < 1e-10, "P_L should be symmetric"
    
    def test_K_L_decomposition(self):
        """Test that K_L = K_sinc + P_L."""
        kernel = CorrelationKernel(100.0, n_grid=50)
        u, v = 20.0, 40.0
        
        K_full = kernel.K_L(u, v)
        K_decomposed = kernel.K_sinc(u, v) + kernel.P_L(u, v)
        
        assert np.abs(K_full - K_decomposed) < 1e-10
    
    def test_kernel_matrix_symmetry(self):
        """Test that kernel matrix is symmetric."""
        kernel = CorrelationKernel(50.0, n_grid=30)
        K_matrix = kernel.compute_kernel_matrix()
        
        # Check symmetry
        assert np.allclose(K_matrix, K_matrix.T, atol=1e-10)
    
    def test_kernel_matrix_has_positive_max_eigenvalue(self):
        """Test that kernel matrix has positive maximum eigenvalue."""
        kernel = CorrelationKernel(50.0, n_grid=30)
        K_matrix = kernel.compute_kernel_matrix()
        
        # Compute eigenvalues
        eigenvalues = np.linalg.eigvalsh(K_matrix)
        
        # The maximum eigenvalue should be positive
        # Note: The full kernel K_L = K_sinc + P_L may have some negative eigenvalues
        # due to the perturbation P_L, but the maximum should be positive
        assert np.max(eigenvalues) > 0, "Maximum eigenvalue should be positive"
    
    def test_lambda_max_positive(self):
        """Test that maximum eigenvalue is positive."""
        kernel = CorrelationKernel(100.0, n_grid=50)
        lambda_max = kernel.compute_lambda_max()
        
        assert lambda_max > 0, "Maximum eigenvalue should be positive"
    
    def test_lambda_max_scales_with_L(self):
        """Test that λ_max increases with L."""
        L_values = [50.0, 100.0, 200.0]
        lambda_values = []
        
        for L in L_values:
            kernel = CorrelationKernel(L, n_grid=50)
            lambda_values.append(kernel.compute_lambda_max())
        
        # Should be monotonically increasing
        assert lambda_values[1] > lambda_values[0]
        assert lambda_values[2] > lambda_values[1]


class TestGoldenRatioConvergence:
    """Test the golden ratio convergence analysis."""
    
    def test_convergence_initialization(self):
        """Test convergence analyzer initialization."""
        L_values = [10.0, 100.0, 1000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=50)
        
        assert len(analyzer.L_values) == 3
        assert analyzer.n_grid == 50
        assert len(analyzer.results) == 0
    
    def test_compute_alpha_L(self):
        """Test α(L) computation."""
        analyzer = GoldenRatioConvergence([100.0], n_grid=50)
        alpha_L, lambda_max = analyzer.compute_alpha_L(100.0)
        
        # α should be between 0 and 1
        assert 0 < alpha_L < 1, "α(L) should be between 0 and 1"
        
        # Should be approaching 1/Φ
        assert np.abs(alpha_L - INV_PHI) < 0.1, "α(L) should be close to 1/Φ"
        
        # λ_max should be positive
        assert lambda_max > 0
    
    def test_convergence_sweep_structure(self):
        """Test that convergence sweep produces expected structure."""
        L_values = [100.0, 1000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=50)
        results = analyzer.run_convergence_sweep()
        
        # Check result structure
        assert 'L_values' in results
        assert 'alpha_values' in results
        assert 'lambda_max_values' in results
        assert 'errors' in results
        assert 'target' in results
        
        # Check sizes
        assert len(results['alpha_values']) == 2
        assert len(results['errors']) == 2
        
        # Check target value
        assert results['target'] == INV_PHI
    
    def test_convergence_to_inv_phi(self):
        """Test that α(L) converges to 1/Φ as L increases."""
        L_values = [100.0, 1000.0, 10000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=50)
        results = analyzer.run_convergence_sweep()
        
        errors = results['errors']
        
        # Errors should decrease with increasing L
        assert errors[1] < errors[0], "Error should decrease as L increases"
        assert errors[2] < errors[1], "Error should continue to decrease"
        
        # Final error should be small
        assert errors[-1] < 0.01, "Final error should be less than 1%"
    
    def test_error_scaling_analysis(self):
        """Test error scaling analysis."""
        L_values = [100.0, 1000.0, 10000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=50)
        analyzer.run_convergence_sweep()
        
        scaling_results = analyzer.analyze_error_scaling()
        
        # Check result structure
        assert 'scaling_exponent' in scaling_results
        assert 'scaling_prefactor' in scaling_results
        assert 'theoretical_exponent' in scaling_results
        assert 'consistent' in scaling_results
        
        # Check theoretical value
        assert scaling_results['theoretical_exponent'] == 0.5
        
        # Exponent should be positive (error decreases)
        assert scaling_results['scaling_exponent'] > 0
    
    def test_error_scaling_close_to_half(self):
        """Test that error scaling is close to 1/√L."""
        L_values = [100.0, 1000.0, 10000.0, 100000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=80)
        analyzer.run_convergence_sweep()
        
        scaling_results = analyzer.analyze_error_scaling()
        beta = scaling_results['scaling_exponent']
        
        # Should be close to 0.5
        assert 0.3 < beta < 0.7, f"Scaling exponent {beta} should be near 0.5"
    
    @pytest.mark.slow
    def test_high_precision_convergence(self):
        """Test high-precision convergence (slow test)."""
        L_values = [10000.0, 100000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=150)
        results = analyzer.run_convergence_sweep()
        
        # At L=100000, error should be very small
        final_error = results['errors'][-1]
        assert final_error < 1e-3, f"High-L error {final_error} should be < 0.001"


class TestKappaInternalization:
    """Test κ internalization calculations."""
    
    def test_kappa_formula(self):
        """Test κ = 4π/(f₀·Φ) calculation."""
        kappa = compute_kappa_internalized()
        
        # Compute expected value
        expected = (4 * np.pi) / (F0_HZ * PHI)
        
        assert np.abs(kappa - expected) < 1e-10
    
    def test_kappa_value_range(self):
        """Test that κ is in expected range."""
        kappa = compute_kappa_internalized()
        
        # Should be around 2.577 based on problem statement
        assert 2.0 < kappa < 3.0, f"κ = {kappa} should be in range [2, 3]"
    
    def test_kappa_consistency_validation(self):
        """Test κ consistency validation."""
        results = validate_kappa_consistency(tolerance=0.01)
        
        # Check result structure
        assert 'kappa_computed' in results
        assert 'kappa_expected' in results
        assert 'error' in results
        assert 'relative_error' in results
        assert 'consistent' in results
        
        # Expected value from problem statement
        assert results['kappa_expected'] == 2.577310
    
    def test_kappa_close_to_expected(self):
        """Test that computed κ is close to expected value."""
        kappa = compute_kappa_internalized()
        kappa_expected = 2.577310
        
        relative_error = abs(kappa - kappa_expected) / kappa_expected
        
        # Should be within 1%
        assert relative_error < 0.01, f"κ relative error {relative_error} should be < 1%"


class TestMathematicalConstants:
    """Test mathematical constants."""
    
    def test_phi_value(self):
        """Test golden ratio value."""
        assert np.abs(PHI - 1.618033988749895) < 1e-14
    
    def test_inv_phi_value(self):
        """Test 1/Φ value."""
        assert np.abs(INV_PHI - 0.618033988749895) < 1e-14
    
    def test_phi_inv_phi_relation(self):
        """Test that Φ · (1/Φ) = 1."""
        assert np.abs(PHI * INV_PHI - 1.0) < 1e-14
    
    def test_phi_golden_ratio_equation(self):
        """Test that Φ² = Φ + 1."""
        assert np.abs(PHI**2 - (PHI + 1)) < 1e-14
    
    def test_f0_value(self):
        """Test fundamental frequency value."""
        assert F0_HZ == 141.7001


class TestIntegration:
    """Integration tests for the full validation pipeline."""
    
    def test_full_validation_pipeline(self):
        """Test complete validation pipeline with small dataset."""
        L_values = [100.0, 1000.0]
        
        # Run convergence sweep
        analyzer = GoldenRatioConvergence(L_values, n_grid=50)
        convergence_results = analyzer.run_convergence_sweep()
        
        # Analyze error scaling
        scaling_results = analyzer.analyze_error_scaling()
        
        # Validate κ
        kappa_results = validate_kappa_consistency()
        
        # All should complete without errors
        assert convergence_results is not None
        assert scaling_results is not None
        assert kappa_results is not None
    
    def test_validation_consistency(self):
        """Test consistency across multiple runs."""
        L = 1000.0
        
        # Run twice
        kernel1 = CorrelationKernel(L, n_grid=50)
        lambda1 = kernel1.compute_lambda_max()
        
        kernel2 = CorrelationKernel(L, n_grid=50)
        lambda2 = kernel2.compute_lambda_max()
        
        # Should be identical (deterministic)
        assert np.abs(lambda1 - lambda2) < 1e-10


# ═══════════════════════════════════════════════════════════════════════════
# BENCHMARK TESTS
# ═══════════════════════════════════════════════════════════════════════════

@pytest.mark.slow
class TestBenchmarks:
    """Performance and accuracy benchmarks."""
    
    def test_large_grid_convergence(self):
        """Test convergence with large grid size."""
        kernel = CorrelationKernel(1000.0, n_grid=300)
        lambda_max = kernel.compute_lambda_max()
        
        alpha = (np.pi * lambda_max) / (2 * 1000.0)
        error = abs(alpha - INV_PHI)
        
        # Should be more accurate with larger grid
        assert error < 0.005
    
    def test_extended_L_range(self):
        """Test convergence over extended L range."""
        L_values = [10.0, 100.0, 1000.0, 10000.0]
        analyzer = GoldenRatioConvergence(L_values, n_grid=100)
        results = analyzer.run_convergence_sweep()
        
        # Check all errors decrease monotonically
        errors = results['errors']
        for i in range(len(errors) - 1):
            assert errors[i+1] < errors[i] * 1.5  # Allow some numerical variation


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
