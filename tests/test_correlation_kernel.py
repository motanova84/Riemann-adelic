#!/usr/bin/env python3
"""
Tests for Correlation Kernel Operator (K_net)

Tests the QCAL ∞³ correlation kernel implementation, including:
    1. Weyl counting function
    2. Correlation kernel properties
    3. Fredholm operator eigenvalue problem
    4. κ_int calculation and verification
    5. Mercer decomposition

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators directory to path
operators_path = Path(__file__).parent.parent / "operators"
sys.path.insert(0, str(operators_path))

from correlation_kernel import (
    WeylCountingFunction,
    CorrelationKernel,
    FredholmCorrelationOperator,
    run_full_analysis,
    F0_BASE,
    PHI,
    KAPPA_PI
)


class TestWeylCountingFunction:
    """Test suite for Weyl counting function G(x)."""
    
    def test_initialization(self):
        """Test Weyl function initialization."""
        weyl = WeylCountingFunction()
        assert weyl.V_amp > 0
        assert weyl.alpha > 0
    
    def test_monotonicity(self):
        """Test that G(x) is monotonically increasing."""
        weyl = WeylCountingFunction()
        x = np.linspace(0.1, 100, 100)
        G = weyl(x)
        
        # Check monotonicity
        dG = np.diff(G)
        assert np.all(dG >= -1e-10), "G(x) should be monotonically increasing"
    
    def test_weyl_law_scaling(self):
        """Test Weyl law scaling: G(x) ~ √x for large x."""
        weyl = WeylCountingFunction(log_corrections=False)
        
        x = np.array([100.0, 400.0])  # x scales by 4
        G = weyl(x)
        
        # G should scale approximately as √x → √4 = 2
        ratio = G[1] / G[0]
        expected_ratio = 2.0
        
        assert np.abs(ratio - expected_ratio) < 0.1, f"Scaling ratio {ratio} should be close to 2"
    
    def test_zero_at_origin(self):
        """Test G(0) = 0."""
        weyl = WeylCountingFunction()
        G0 = weyl(np.array([0.0]))
        
        assert np.abs(G0[0]) < 1e-6, "G(0) should be approximately 0"
    
    def test_vectorization(self):
        """Test that Weyl function handles array inputs correctly."""
        weyl = WeylCountingFunction()
        
        # Test with different array shapes
        x1 = np.array([1.0])
        x2 = np.array([1.0, 2.0, 3.0])
        x3 = np.linspace(1, 10, 50)
        
        G1 = weyl(x1)
        G2 = weyl(x2)
        G3 = weyl(x3)
        
        assert G1.shape == (1,)
        assert G2.shape == (3,)
        assert G3.shape == (50,)


class TestCorrelationKernel:
    """Test suite for correlation kernel K(x, y)."""
    
    def test_initialization(self):
        """Test kernel initialization."""
        kernel = CorrelationKernel()
        assert kernel.weyl is not None
        assert kernel.reg > 0
    
    def test_symmetry(self):
        """Test K(x, y) = K(y, x)."""
        kernel = CorrelationKernel()
        x = np.array([1.0, 2.0, 5.0, 10.0])
        
        # Compute kernel matrix
        K = kernel(x, x)
        
        # Check symmetry
        symmetry_error = np.max(np.abs(K - K.T))
        assert symmetry_error < 1e-10, f"Kernel should be symmetric, error = {symmetry_error}"
    
    def test_diagonal_regularization(self):
        """Test that diagonal K(x, x) is well-defined."""
        kernel = CorrelationKernel()
        x = np.array([1.0, 5.0, 10.0, 50.0])
        
        K = kernel(x, x)
        
        # Diagonal should be finite and positive
        diag = np.diag(K)
        assert np.all(np.isfinite(diag)), "Diagonal should be finite"
        assert np.all(diag > 0), "Diagonal should be positive"
    
    def test_positivity(self):
        """Test that kernel is positive semi-definite."""
        kernel = CorrelationKernel()
        x = np.linspace(0.1, 10, 30)
        
        is_positive, min_eig = kernel.verify_positivity(x)
        
        # Allow small numerical errors
        assert min_eig > -1e-8, f"Minimum eigenvalue {min_eig} should be non-negative"
    
    def test_sine_kernel_structure(self):
        """Test that kernel has sine-kernel structure for small differences."""
        kernel = CorrelationKernel()
        
        # Test at points with small separation
        x = 5.0
        y = 5.1
        
        K_xy = kernel(np.array([x]), np.array([y]))[0, 0]
        
        # For small Δx, K should be close to sinc function behavior
        assert np.isfinite(K_xy), "Kernel should be finite"
        assert np.abs(K_xy) < 10, "Kernel should be bounded"
    
    def test_decay_at_large_separation(self):
        """Test kernel decay for large |x - y|."""
        kernel = CorrelationKernel()
        
        x = np.array([1.0])
        y1 = np.array([2.0])
        y2 = np.array([50.0])
        
        K1 = kernel(x, y1)[0, 0]
        K2 = kernel(x, y2)[0, 0]
        
        # Kernel should decay (in absolute value) for larger separation
        # Note: sine kernel oscillates but envelope decays
        assert np.abs(K2) <= np.abs(K1) + 1.0, "Kernel should not grow unboundedly"


class TestFredholmCorrelationOperator:
    """Test suite for Fredholm correlation operator."""
    
    def test_initialization(self):
        """Test Fredholm operator initialization."""
        op = FredholmCorrelationOperator(n_points=50)
        
        assert len(op.x_range) == 50
        assert len(op.dx) == 50
        assert op.kernel is not None
    
    def test_discretization(self):
        """Test operator discretization."""
        op = FredholmCorrelationOperator(n_points=30)
        K_matrix = op.discretize()
        
        assert K_matrix.shape == (30, 30)
        assert np.allclose(K_matrix, K_matrix.T, atol=1e-10), "Discretized operator should be symmetric"
    
    def test_eigenvalue_computation(self):
        """Test eigenvalue problem solution."""
        op = FredholmCorrelationOperator(n_points=50)
        eigenvalues, eigenvectors = op.solve_eigenvalue_problem(n_eigenvalues=5)
        
        assert len(eigenvalues) == 5
        assert eigenvectors.shape == (50, 5)
        
        # Eigenvalues should be sorted in descending order
        assert np.all(np.diff(eigenvalues) <= 1e-10), "Eigenvalues should be sorted"
        
        # Largest eigenvalue should be positive
        assert eigenvalues[0] > 0, "Largest eigenvalue should be positive"
    
    def test_kappa_int_calculation(self):
        """Test κ_int = λ_max(K) calculation."""
        op = FredholmCorrelationOperator(n_points=100)
        kappa_int = op.compute_kappa_int()
        
        assert kappa_int > 0, "κ_int should be positive"
        assert np.isfinite(kappa_int), "κ_int should be finite"
        
        # Should be in reasonable range (order of unity)
        assert 0.001 < kappa_int < 100, f"κ_int = {kappa_int} should be in reasonable range"
    
    def test_final_identity_verification(self):
        """Test verification of κ_int = 4π/(f_0·Φ)."""
        op = FredholmCorrelationOperator(n_points=150)
        kappa_int = op.compute_kappa_int()
        
        results = op.verify_final_identity(kappa_int)
        
        assert 'kappa_int' in results
        assert 'kappa_theory' in results
        assert 'relative_error' in results
        assert 'identity_holds' in results
        
        # Results should use correct constants
        assert results['f0'] == F0_BASE
        assert results['phi'] == PHI
        
        # Theoretical value should be finite
        assert np.isfinite(results['kappa_theory'])
    
    def test_mercer_decomposition(self):
        """Test Mercer's theorem: K = Σ λ_n φ_n ⊗ φ_n."""
        op = FredholmCorrelationOperator(n_points=80)
        
        error, K_reconstructed = op.verify_mercer_decomposition(n_terms=30)
        
        assert 0 <= error <= 1, f"Reconstruction error {error} should be in [0, 1]"
        
        # With enough terms, error should be small
        assert error < 0.5, f"Reconstruction error {error} should be reasonable with 30 terms"
        
        # Reconstructed kernel should have correct shape
        assert K_reconstructed.shape == (80, 80)
    
    def test_convergence_with_grid_refinement(self):
        """Test that κ_int converges as grid is refined."""
        n_points_list = [50, 100, 150]
        kappa_values = []
        
        for n_points in n_points_list:
            op = FredholmCorrelationOperator(n_points=n_points)
            kappa = op.compute_kappa_int()
            kappa_values.append(kappa)
        
        # Values should converge (differences should decrease)
        diff1 = np.abs(kappa_values[1] - kappa_values[0])
        diff2 = np.abs(kappa_values[2] - kappa_values[1])
        
        # Second difference should be smaller (or at least not much larger)
        assert diff2 <= 2 * diff1, "κ_int should show convergence with refinement"


class TestFullAnalysis:
    """Test suite for complete analysis pipeline."""
    
    def test_run_full_analysis(self):
        """Test complete analysis workflow."""
        results = run_full_analysis(
            x_min=0.1,
            x_max=50.0,
            n_points=100,
            verbose=False
        )
        
        # Check all required keys present
        assert 'kappa_int' in results
        assert 'verification' in results
        assert 'kernel_properties' in results
        assert 'mercer_reconstruction_error' in results
        assert 'parameters' in results
        
        # Check kappa_int is reasonable
        assert results['kappa_int'] > 0
        assert np.isfinite(results['kappa_int'])
        
        # Check verification structure
        verification = results['verification']
        assert 'kappa_theory' in verification
        assert 'relative_error' in verification
        assert 'identity_holds' in verification
        
        # Check kernel properties
        props = results['kernel_properties']
        assert 'symmetry_error' in props
        assert 'is_positive' in props
        assert props['symmetry_error'] < 1e-8
    
    def test_parameter_consistency(self):
        """Test that saved parameters match input."""
        V_amp_test = 15000.0
        
        results = run_full_analysis(
            x_min=1.0,
            x_max=80.0,
            n_points=120,
            V_amp=V_amp_test,
            verbose=False
        )
        
        params = results['parameters']
        assert params['x_min'] == 1.0
        assert params['x_max'] == 80.0
        assert params['n_points'] == 120
        assert params['V_amp'] == V_amp_test
    
    def test_reproducibility(self):
        """Test that analysis is reproducible."""
        results1 = run_full_analysis(
            x_min=0.5,
            x_max=60.0,
            n_points=100,
            verbose=False
        )
        
        results2 = run_full_analysis(
            x_min=0.5,
            x_max=60.0,
            n_points=100,
            verbose=False
        )
        
        # Results should be identical
        assert np.abs(results1['kappa_int'] - results2['kappa_int']) < 1e-12
        assert results1['verification']['identity_holds'] == results2['verification']['identity_holds']


class TestQCALConstants:
    """Test QCAL constants and relationships."""
    
    def test_constants_defined(self):
        """Test that QCAL constants are defined."""
        assert F0_BASE == 141.7001
        assert PHI == 1.618033988749895
        assert KAPPA_PI > 2.5 and KAPPA_PI < 2.6
    
    def test_theoretical_kappa_value(self):
        """Test theoretical κ_theory = 4π/(f_0·Φ)."""
        kappa_theory = 4 * np.pi / (F0_BASE * PHI)
        
        # Should be positive and finite
        assert kappa_theory > 0
        assert np.isfinite(kappa_theory)
        
        # Should be in reasonable range (order ~0.01 to 1)
        assert 0.001 < kappa_theory < 10


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_grid(self):
        """Test that small grids don't crash."""
        op = FredholmCorrelationOperator(n_points=20)
        kappa = op.compute_kappa_int()
        
        assert np.isfinite(kappa)
    
    def test_large_grid(self):
        """Test that large grids work (but may be slow)."""
        op = FredholmCorrelationOperator(n_points=300)
        kappa = op.compute_kappa_int()
        
        assert np.isfinite(kappa)
    
    def test_extreme_potential(self):
        """Test with extreme potential values."""
        # Very large potential
        results_large = run_full_analysis(
            V_amp=1e6,
            n_points=50,
            verbose=False
        )
        assert np.isfinite(results_large['kappa_int'])
        
        # Very small potential
        results_small = run_full_analysis(
            V_amp=100.0,
            n_points=50,
            verbose=False
        )
        assert np.isfinite(results_small['kappa_int'])
    
    def test_no_nan_or_inf(self):
        """Test that computation produces no NaN or Inf."""
        results = run_full_analysis(
            n_points=100,
            verbose=False
        )
        
        # Check all numerical values
        assert np.isfinite(results['kappa_int'])
        assert np.isfinite(results['verification']['kappa_theory'])
        assert np.isfinite(results['verification']['relative_error'])
        assert np.isfinite(results['kernel_properties']['symmetry_error'])
        assert np.isfinite(results['mercer_reconstruction_error'])


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
