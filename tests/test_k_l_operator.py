#!/usr/bin/env python3
"""
Tests for K_L Operator (Fredholm-Hankel Kernel)

Tests the K_L operator implementation and the convergence to golden ratio.

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
Date: 2026-02-14
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.k_l_operator import (
    sinc_kernel,
    build_K_L_matrix,
    compute_max_eigenvalue,
    compute_C_observable,
    compute_kappa_pi,
    KLOperatorExperiment,
    PHI,
    INV_PHI,
    F0
)


class TestSincKernel:
    """Test the sinc kernel function."""
    
    def test_sinc_kernel_diagonal(self):
        """Test sinc kernel at u = v (should be √(u²)/L = u/L)."""
        u = 5.0
        L = 10.0
        result = sinc_kernel(u, u, L)
        expected = u / L
        assert np.abs(result - expected) < 1e-10
    
    def test_sinc_kernel_off_diagonal(self):
        """Test sinc kernel at u ≠ v."""
        u, v = 3.0, 1.0
        L = 10.0
        result = sinc_kernel(u, v, L)
        
        # Manual calculation: sinc((u-v)/L) * √(uv) / L
        expected = np.sinc((u - v) / L) * np.sqrt(u * v) / L
        assert np.abs(result - expected) < 1e-10
    
    def test_sinc_kernel_symmetry(self):
        """Test that K(u,v) = K(v,u)."""
        u, v = 4.7, 2.3
        L = 10.0
        assert np.abs(sinc_kernel(u, v, L) - sinc_kernel(v, u, L)) < 1e-12
    
    def test_sinc_kernel_near_diagonal(self):
        """Test numerical stability near diagonal."""
        u = 5.0
        L = 10.0
        for delta in [1e-3, 1e-6, 1e-9, 1e-12]:
            v = u + delta
            result = sinc_kernel(u, v, L)
            # Should be continuous
            assert np.isfinite(result)
            assert result > 0


class TestKLMatrix:
    """Test K_L matrix construction."""
    
    def test_matrix_symmetry(self):
        """Test that K_L matrix is symmetric."""
        K = build_K_L_matrix(L=10.0, N=50)
        assert np.allclose(K, K.T, atol=1e-10)
    
    def test_matrix_positive_semidefinite(self):
        """Test that K_L matrix has non-negative eigenvalues."""
        K = build_K_L_matrix(L=10.0, N=50)
        eigenvalues = np.linalg.eigvalsh(K)
        assert np.all(eigenvalues >= -1e-10)  # Allow small numerical error
    
    def test_matrix_dimensions(self):
        """Test matrix has correct dimensions."""
        N = 100
        K = build_K_L_matrix(L=5.0, N=N)
        assert K.shape == (N, N)
    
    def test_matrix_small_L(self):
        """Test matrix construction for small L."""
        K = build_K_L_matrix(L=1.0, N=20)
        assert K.shape == (20, 20)
        assert np.all(np.isfinite(K))
    
    def test_matrix_large_L(self):
        """Test matrix construction for large L."""
        K = build_K_L_matrix(L=100.0, N=100)
        assert K.shape == (100, 100)
        assert np.all(np.isfinite(K))


class TestMaxEigenvalue:
    """Test maximum eigenvalue computation."""
    
    def test_eigenvalues_real(self):
        """Test that eigenvalues are real (K is symmetric)."""
        lambda_max, eigenvalues = compute_max_eigenvalue(L=10.0, N=50)
        assert np.all(np.isreal(eigenvalues))
        assert np.isreal(lambda_max)
    
    def test_eigenvalues_positive(self):
        """Test that eigenvalues are non-negative."""
        lambda_max, eigenvalues = compute_max_eigenvalue(L=10.0, N=50)
        assert np.all(eigenvalues >= -1e-10)
    
    def test_lambda_max_is_maximum(self):
        """Test that lambda_max is indeed the maximum eigenvalue."""
        lambda_max, eigenvalues = compute_max_eigenvalue(L=10.0, N=50)
        assert lambda_max >= np.max(eigenvalues) - 1e-10
    
    def test_eigenvalue_scaling_with_L(self):
        """Test that λ_max grows approximately linearly with L."""
        L_values = [10, 20, 40, 80]
        lambdas = []
        
        for L in L_values:
            lambda_max, _ = compute_max_eigenvalue(L, N=100)
            lambdas.append(lambda_max)
        
        # Check that λ_max roughly doubles when L doubles
        for i in range(len(L_values) - 1):
            ratio = lambdas[i+1] / lambdas[i]
            L_ratio = L_values[i+1] / L_values[i]
            # Should be close to 2 (linear scaling)
            assert np.abs(ratio - L_ratio) < 0.5


class TestCObservable:
    """Test C(L) observable computation."""
    
    def test_C_in_reasonable_range(self):
        """Test that C(L) is in reasonable range."""
        C = compute_C_observable(L=100.0, N=200)
        # Should be somewhere between 0.5 and 0.7
        assert 0.4 < C < 0.8
    
    def test_C_convergence_trend(self):
        """Test that C(L) trends toward 1/Φ as L increases."""
        L_values = [10, 30, 100]
        C_values = []
        
        for L in L_values:
            C = compute_C_observable(L, N=min(100 + int(L), 500))
            C_values.append(C)
        
        # Check monotonic approach to 1/Φ
        errors = [abs(C - INV_PHI) for C in C_values]
        # Errors should generally decrease
        # (allowing for some numerical noise)
        assert errors[-1] < errors[0]
    
    def test_C_close_to_golden_ratio(self):
        """Test that C(L) approaches 1/Φ for large L."""
        # For L=1000, should be within 1% of 1/Φ
        C = compute_C_observable(L=1000.0, N=1000)
        error = abs(C - INV_PHI) / INV_PHI
        assert error < 0.01


class TestKappaPi:
    """Test κ_Π computation."""
    
    def test_kappa_pi_value(self):
        """Test that κ_Π has expected value."""
        kappa = compute_kappa_pi()
        # κ_Π = 4π/(141.7001 × 1.618...) ≈ 2.5773
        expected = 4 * np.pi / (F0 * PHI)
        assert np.abs(kappa - expected) < 1e-10
    
    def test_kappa_pi_reasonable_range(self):
        """Test that κ_Π is in reasonable range."""
        kappa = compute_kappa_pi()
        assert 2.0 < kappa < 3.0
    
    def test_kappa_pi_with_custom_f0(self):
        """Test κ_Π with custom frequency."""
        f0_custom = 100.0
        kappa = compute_kappa_pi(f0=f0_custom)
        expected = 4 * np.pi / (f0_custom * PHI)
        assert np.abs(kappa - expected) < 1e-10


class TestKLOperatorExperiment:
    """Test the experimentum crucis experiment class."""
    
    def test_experiment_initialization(self):
        """Test experiment initialization."""
        experiment = KLOperatorExperiment()
        assert len(experiment.L_values) > 0
        assert len(experiment.L_values) == len(experiment.N_values)
    
    def test_experiment_custom_L_values(self):
        """Test experiment with custom L values."""
        L_custom = [10, 20, 30]
        experiment = KLOperatorExperiment(L_values=L_custom)
        assert experiment.L_values == L_custom
    
    def test_experiment_run_quick(self):
        """Test running quick experiment."""
        L_values = [10, 30, 100]
        experiment = KLOperatorExperiment(L_values=L_values)
        summary = experiment.run(verbose=False)
        
        assert 'results' in summary
        assert len(summary['results']) == 3
        assert 'verdict' in summary
    
    def test_experiment_results_structure(self):
        """Test that experiment results have correct structure."""
        experiment = KLOperatorExperiment(L_values=[10, 30])
        summary = experiment.run(verbose=False)
        
        for result in summary['results']:
            assert 'L' in result
            assert 'N' in result
            assert 'lambda_max' in result
            assert 'C_L' in result
            assert 'error' in result
    
    def test_experiment_convergence_analysis(self):
        """Test convergence analysis."""
        experiment = KLOperatorExperiment(L_values=[10, 30, 100, 300])
        summary = experiment.run(verbose=False)
        
        assert 'convergence' in summary
        if summary['convergence']:
            assert 'alpha' in summary['convergence']
            assert 'r_squared' in summary['convergence']
    
    def test_experiment_verdict(self):
        """Test that experiment generates a verdict."""
        experiment = KLOperatorExperiment(L_values=[10, 30, 100])
        summary = experiment.run(verbose=False)
        
        verdict = summary['verdict']
        assert isinstance(verdict, str)
        assert len(verdict) > 0


class TestGoldenRatioConvergence:
    """Integration tests for golden ratio convergence."""
    
    @pytest.mark.slow
    def test_convergence_to_phi_large_L(self):
        """Test that C(L) converges to 1/Φ for very large L."""
        L = 10000
        N = 2000
        C = compute_C_observable(L, N)
        
        error = abs(C - INV_PHI)
        # For L=10000, error should be < 1e-4
        assert error < 1e-4
    
    @pytest.mark.slow
    def test_diffusive_scaling(self):
        """Test that error scales as 1/√L (diffusive)."""
        # Use logarithmically spaced L values
        L_values = [100, 300, 1000, 3000]
        N_values = [500, 866, 1000, 1500]
        
        errors = []
        for L, N in zip(L_values, N_values):
            C = compute_C_observable(L, N)
            error = abs(C - INV_PHI)
            errors.append(error)
        
        # Fit log(error) vs log(L)
        log_L = np.log(L_values)
        log_error = np.log(errors)
        
        coeffs = np.polyfit(log_L, log_error, 1)
        alpha = -coeffs[0]
        
        # α should be close to 0.5 for diffusive scaling
        assert np.abs(alpha - 0.5) < 0.1
    
    def test_mathematical_constants(self):
        """Test that mathematical constants are correct."""
        # Golden ratio
        assert np.abs(PHI - (1 + np.sqrt(5))/2) < 1e-15
        
        # Inverse golden ratio
        assert np.abs(INV_PHI - 1/PHI) < 1e-15
        assert np.abs(INV_PHI - 0.618033988749895) < 1e-14
        
        # Fundamental frequency
        assert F0 == 141.7001


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
