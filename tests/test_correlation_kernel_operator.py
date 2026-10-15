#!/usr/bin/env python3
"""
test_correlation_kernel_operator.py

Tests for the correlation kernel operator implementation.

Tests cover:
1. Kernel properties (symmetry, positive semi-definiteness)
2. Eigenvalue computation
3. Analytical formula validation
4. QCAL constant integration
5. Convergence behavior
6. Numerical stability

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: February 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from operators.correlation_kernel_operator import (
    CorrelationKernelOperator,
    F0,
    PHI,
    KAPPA_PI_THEORETICAL
)


class TestCorrelationKernelOperator:
    """Test suite for CorrelationKernelOperator."""
    
    @pytest.fixture
    def operator_small(self):
        """Small operator for quick tests."""
        return CorrelationKernelOperator(f0=F0, N=50)
    
    @pytest.fixture
    def operator_medium(self):
        """Medium-sized operator for more accurate tests."""
        return CorrelationKernelOperator(f0=F0, N=200)
    
    def test_initialization(self, operator_small):
        """Test proper initialization of operator."""
        assert operator_small.f0 == F0
        assert operator_small.L == pytest.approx(1.0 / F0, rel=1e-10)
        assert operator_small.N == 50
        assert len(operator_small.u_grid) == 49  # N-1 (excluding u=0)
    
    def test_sinc_kernel_diagonal(self, operator_small):
        """Test that sinc kernel diagonal is 1 (limit of sinc(0))."""
        u = operator_small.u_grid
        K_sinc = operator_small.sinc_kernel(u, u)
        
        # Diagonal elements should be 1
        diagonal = np.diag(K_sinc)
        assert np.allclose(diagonal, 1.0, rtol=1e-10)
    
    def test_sinc_kernel_symmetry(self, operator_small):
        """Test that sinc kernel is symmetric."""
        u = operator_small.u_grid
        K_sinc = operator_small.sinc_kernel(u, u)
        
        # Should be symmetric
        assert np.allclose(K_sinc, K_sinc.T, rtol=1e-10)
    
    def test_kernel_matrix_symmetry(self, operator_small):
        """Test that full kernel matrix is symmetric."""
        K = operator_small.compute_kernel_matrix()
        
        assert np.allclose(K, K.T, rtol=1e-10), "Kernel matrix should be symmetric"
    
    def test_kernel_matrix_positive_weights(self, operator_small):
        """Test that kernel has positive weights from √(uv)."""
        K = operator_small.compute_kernel_matrix()
        
        # All elements should be non-negative (sinc can be negative but weight is positive)
        # The dominant contribution should be positive
        assert np.all(np.diag(K) > 0), "Diagonal elements should be positive"
    
    def test_eigenvalues_real(self, operator_small):
        """Test that eigenvalues are real (kernel is symmetric)."""
        eigenvals = operator_small.compute_eigenvalues()
        
        # All eigenvalues should be real
        assert np.all(np.isreal(eigenvals))
    
    def test_eigenvalues_sorted(self, operator_small):
        """Test that eigenvalues are sorted in descending order."""
        eigenvals = operator_small.compute_eigenvalues()
        
        # Should be sorted descending
        assert np.all(eigenvals[:-1] >= eigenvals[1:])
    
    def test_maximum_eigenvalue_positive(self, operator_small):
        """Test that maximum eigenvalue is positive."""
        kappa_max = operator_small.get_maximum_eigenvalue()
        
        assert kappa_max > 0, "Maximum eigenvalue should be positive"
    
    def test_analytical_formula(self):
        """Test analytical formula κ = 4π/(f₀·Φ)."""
        operator = CorrelationKernelOperator(f0=F0, N=100)
        kappa_ana = operator.get_analytical_kappa()
        
        # Compute manually
        expected = 4 * np.pi / (F0 * PHI)
        
        assert kappa_ana == pytest.approx(expected, rel=1e-12)
        assert kappa_ana == pytest.approx(KAPPA_PI_THEORETICAL, rel=1e-12)
    
    def test_numerical_vs_analytical(self, operator_medium):
        """Test that numerical matches analytical within tolerance."""
        results = operator_medium.validate_derivation()
        
        # Should match within 5% (depends on discretization)
        assert results['relative_error'] < 0.05, \
            f"Numerical κ should match analytical within 5%, got {results['relative_error']}"
    
    def test_convergence_with_N(self):
        """Test that result converges as N increases."""
        N_values = [50, 100, 200]
        kappa_values = []
        
        for N in N_values:
            op = CorrelationKernelOperator(f0=F0, N=N)
            kappa_values.append(op.get_maximum_eigenvalue())
        
        # Errors should decrease
        kappa_ana = 4 * np.pi / (F0 * PHI)
        errors = [abs(k - kappa_ana) for k in kappa_values]
        
        # Each successive error should generally be smaller
        # (might not be perfectly monotonic due to discretization artifacts)
        assert errors[-1] < errors[0], "Error should decrease with larger N"
    
    def test_qcal_constants(self):
        """Test that QCAL constants are correct."""
        # f₀ = 141.7001 Hz
        assert F0 == pytest.approx(141.7001, rel=1e-10)
        
        # Φ = (1+√5)/2
        expected_phi = (1 + np.sqrt(5)) / 2
        assert PHI == pytest.approx(expected_phi, rel=1e-12)
        
        # κ_Π = 4π/(f₀·Φ)
        expected_kappa = 4 * np.pi / (F0 * PHI)
        assert KAPPA_PI_THEORETICAL == pytest.approx(expected_kappa, rel=1e-12)
    
    def test_golden_ratio_identity(self):
        """Test golden ratio identity Φ = 1 + 1/Φ."""
        assert PHI == pytest.approx(1 + 1/PHI, rel=1e-12)
    
    def test_golden_ratio_squared(self):
        """Test golden ratio property Φ² = Φ + 1."""
        assert PHI**2 == pytest.approx(PHI + 1, rel=1e-12)
    
    def test_kappa_value_range(self, operator_medium):
        """Test that κ is in expected range around 2.577."""
        kappa_num = operator_medium.get_maximum_eigenvalue()
        
        # Should be close to 2.577
        assert 2.4 < kappa_num < 2.7, \
            f"κ should be around 2.577, got {kappa_num}"
    
    def test_validate_derivation_keys(self, operator_small):
        """Test that validation returns all expected keys."""
        results = operator_small.validate_derivation()
        
        expected_keys = [
            'kappa_numerical',
            'kappa_analytical',
            'relative_error',
            'f0',
            'phi',
            'L',
            'N_points',
            'kappa_pi_theoretical'
        ]
        
        for key in expected_keys:
            assert key in results, f"Missing key: {key}"
    
    def test_eigenfunction_normalization(self, operator_small):
        """Test that eigenfunctions can be normalized."""
        eigenvals, eigenvecs = operator_small.compute_eigenvalues(return_vectors=True)
        
        # Pick first eigenfunction
        psi = eigenvecs[:, 0]
        
        # Compute norm
        norm_sq = np.sum(psi**2) * operator_small.du
        
        # Should be normalizable (finite norm)
        assert norm_sq > 0 and np.isfinite(norm_sq)
    
    def test_different_f0_values(self):
        """Test operator with different f₀ values."""
        f0_values = [100.0, 141.7001, 200.0]
        
        for f0 in f0_values:
            op = CorrelationKernelOperator(f0=f0, N=50)
            
            # Should compute without errors
            kappa = op.get_maximum_eigenvalue()
            assert kappa > 0
            
            # Analytical formula should scale correctly
            kappa_ana = op.get_analytical_kappa()
            expected = 4 * np.pi / (f0 * PHI)
            assert kappa_ana == pytest.approx(expected, rel=1e-12)
    
    def test_kernel_matrix_bounds(self, operator_small):
        """Test that kernel matrix elements are bounded."""
        K = operator_small.compute_kernel_matrix()
        
        # Should be finite
        assert np.all(np.isfinite(K))
        
        # Diagonal should be bounded by L (maximum u*v weight)
        max_diagonal = np.max(np.abs(np.diag(K)))
        assert max_diagonal <= operator_small.L
    
    def test_reproducibility(self):
        """Test that results are reproducible."""
        op1 = CorrelationKernelOperator(f0=F0, N=100)
        op2 = CorrelationKernelOperator(f0=F0, N=100)
        
        kappa1 = op1.get_maximum_eigenvalue()
        kappa2 = op2.get_maximum_eigenvalue()
        
        assert kappa1 == pytest.approx(kappa2, rel=1e-12)
    
    def test_validation_report_generation(self, operator_small):
        """Test that validation report generates without errors."""
        report = operator_small.generate_validation_report()
        
        assert isinstance(report, str)
        assert len(report) > 0
        assert 'κ' in report
        assert 'VALIDATION' in report
    
    def test_no_nan_or_inf(self, operator_small):
        """Test that computations don't produce NaN or Inf."""
        K = operator_small.compute_kernel_matrix()
        eigenvals = operator_small.compute_eigenvalues()
        
        assert not np.any(np.isnan(K))
        assert not np.any(np.isinf(K))
        assert not np.any(np.isnan(eigenvals))
        assert not np.any(np.isinf(eigenvals))


class TestKappaTheoretical:
    """Tests for theoretical value of κ."""
    
    def test_kappa_pi_value(self):
        """Test that κ_Π ≈ 2.5773."""
        assert KAPPA_PI_THEORETICAL == pytest.approx(2.577310, abs=1e-5)
    
    def test_kappa_from_formula(self):
        """Test κ = 4π/(f₀·Φ) calculation."""
        kappa = 4 * np.pi / (F0 * PHI)
        
        # Should be approximately 2.5773
        assert kappa == pytest.approx(2.577310, abs=1e-5)
    
    def test_components_product(self):
        """Test that f₀·Φ gives expected value."""
        product = F0 * PHI
        
        # f₀·Φ ≈ 141.7001 · 1.618033989 ≈ 229.285
        assert product == pytest.approx(229.285, abs=0.01)
        
        # Then 4π/(f₀·Φ) ≈ 12.566/(229.285) ≈ 2.5773
        kappa = 4 * np.pi / product
        assert kappa == pytest.approx(2.5773, abs=0.001)


def test_main_execution():
    """Test that main() runs without errors."""
    from operators.correlation_kernel_operator import main
    
    # Should run without raising exceptions
    # (we can't test output easily, but can ensure no crashes)
    try:
        # Redirect output to avoid cluttering test output
        import io
        import sys
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        
        main()
        
        sys.stdout = old_stdout
        success = True
    except Exception as e:
        sys.stdout = old_stdout
        success = False
        pytest.fail(f"main() raised exception: {e}")
    
    assert success


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
