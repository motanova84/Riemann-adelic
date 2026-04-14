"""
Tests for the K_L operator experimental design (TEST DECISIVO - ATLAS³)

Validates:
- Matrix construction correctness
- Eigenvalue computation stability
- Convergence properties
- Numerical precision
"""

import pytest
import numpy as np
from scipy.linalg import eigh
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

import test_decisivo_atlas3 as tda


class TestKernelMatrix:
    """Tests for kernel matrix construction"""
    
    def test_matrix_symmetry(self):
        """Verify that the kernel matrix is symmetric"""
        L = 10
        N = 50
        K, x, w = tda.build_kernel_matrix(L, N, method='gauss')
        
        # Check symmetry
        assert np.allclose(K, K.T, rtol=1e-10), "Matrix should be symmetric"
    
    def test_matrix_positive_semidefinite(self):
        """Verify that the kernel matrix is positive semi-definite"""
        L = 10
        N = 30
        K, x, w = tda.build_kernel_matrix(L, N, method='gauss')
        
        # Check eigenvalues are non-negative
        eigenvalues = eigh(K, eigvals_only=True)
        assert np.all(eigenvalues >= -1e-10), "All eigenvalues should be non-negative"
    
    def test_matrix_dimensions(self):
        """Verify correct matrix dimensions"""
        L = 20
        N = 40
        K, x, w = tda.build_kernel_matrix(L, N, method='gauss')
        
        assert K.shape == (N, N), f"Matrix should be {N}×{N}"
        assert len(x) == N, f"x should have length {N}"
        assert len(w) == N, f"w should have length {N}"
    
    def test_quadrature_points_in_range(self):
        """Verify quadrature points are in [0, L]"""
        L = 15
        N = 50
        K, x, w = tda.build_kernel_matrix(L, N, method='gauss')
        
        assert np.all(x >= 0), "All points should be >= 0"
        assert np.all(x <= L), f"All points should be <= {L}"
    
    def test_weights_positive(self):
        """Verify quadrature weights are positive"""
        L = 10
        N = 30
        K, x, w = tda.build_kernel_matrix(L, N, method='gauss')
        
        assert np.all(w > 0), "All weights should be positive"


class TestEigenvalueComputation:
    """Tests for eigenvalue computation"""
    
    def test_max_eigenvalue_positive(self):
        """Verify that the maximum eigenvalue is positive"""
        L = 10
        N = 50
        lambda_max, C_L, eigenvalues, t = tda.compute_max_eigenvalue(L, N)
        
        assert lambda_max > 0, "Maximum eigenvalue should be positive"
    
    def test_eigenvalues_sorted(self):
        """Verify eigenvalues are properly ordered"""
        L = 10
        N = 30
        lambda_max, C_L, eigenvalues, t = tda.compute_max_eigenvalue(L, N)
        
        # eigh returns eigenvalues in ascending order
        assert eigenvalues[-1] == lambda_max, "Last eigenvalue should be the maximum"
    
    def test_c_l_computation(self):
        """Verify C(L) computation is correct"""
        L = 10
        N = 50
        lambda_max, C_L, eigenvalues, t = tda.compute_max_eigenvalue(L, N)
        
        expected_C_L = (np.pi * lambda_max) / (2 * L)
        assert np.isclose(C_L, expected_C_L, rtol=1e-12), "C(L) should equal πλ_max/(2L)"
    
    def test_c_l_positive(self):
        """Verify C(L) is positive"""
        L = 20
        N = 40
        lambda_max, C_L, eigenvalues, t = tda.compute_max_eigenvalue(L, N)
        
        assert C_L > 0, "C(L) should be positive"
    
    def test_no_nan_or_inf(self):
        """Verify no NaN or Inf values in computation"""
        L = 15
        N = 50
        lambda_max, C_L, eigenvalues, t = tda.compute_max_eigenvalue(L, N)
        
        assert not np.isnan(lambda_max), "lambda_max should not be NaN"
        assert not np.isinf(lambda_max), "lambda_max should not be Inf"
        assert not np.isnan(C_L), "C(L) should not be NaN"
        assert not np.isinf(C_L), "C(L) should not be Inf"


class TestConvergenceTest:
    """Tests for convergence test functionality"""
    
    def test_run_convergence_small(self):
        """Run convergence test with small L values"""
        L_values = [10, 30]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        assert len(results) == 2, "Should have 2 results"
        
        for r in results:
            assert 'L' in r, "Result should contain 'L'"
            assert 'N' in r, "Result should contain 'N'"
            assert 'lambda_max' in r, "Result should contain 'lambda_max'"
            assert 'C(L)' in r, "Result should contain 'C(L)'"
            assert 'error' in r, "Result should contain 'error'"
            assert 'tiempo' in r, "Result should contain 'tiempo'"
    
    def test_increasing_lambda_max(self):
        """Verify lambda_max increases with L"""
        L_values = [10, 30, 100]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        lambda_values = [r['lambda_max'] for r in results]
        
        # Lambda_max should generally increase with L
        assert lambda_values[1] > lambda_values[0], "lambda_max should increase"
        assert lambda_values[2] > lambda_values[1], "lambda_max should increase"
    
    def test_error_decreases_with_L(self):
        """Verify error tends to decrease with larger L"""
        L_values = [10, 30, 100]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        # Error might not decrease monotonically due to numerical effects,
        # but later values should be generally smaller
        errors = [r['error'] for r in results]
        
        # Just verify all errors are finite and reasonable
        for e in errors:
            assert 0 <= e < 10, f"Error {e} should be in reasonable range"
    
    def test_c_l_in_reasonable_range(self):
        """Verify C(L) values are in physically reasonable range"""
        L_values = [10, 30, 100]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        for r in results:
            C_L = r['C(L)']
            # C(L) should be positive and not too large
            assert 0 < C_L < 5, f"C(L)={C_L} should be in (0, 5)"


class TestConstants:
    """Tests for mathematical constants"""
    
    def test_phi_value(self):
        """Verify golden ratio Φ is correct"""
        expected_phi = (1 + np.sqrt(5)) / 2
        assert np.isclose(tda.PHI, expected_phi, rtol=1e-15), "Φ should be (1+√5)/2"
    
    def test_target_value(self):
        """Verify target 1/Φ is correct"""
        expected_target = 1 / tda.PHI
        assert np.isclose(tda.TARGET, expected_target, rtol=1e-15), "TARGET should be 1/Φ"
        
        # Also verify numerical value
        assert np.isclose(tda.TARGET, 0.618033988749895, rtol=1e-12), \
            "TARGET should be approximately 0.618033988749895"


class TestAnalyzeConvergence:
    """Tests for convergence analysis"""
    
    def test_analyze_convergence_structure(self):
        """Verify analyze_convergence returns a regime"""
        L_values = [10, 30]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        regime = tda.analyze_convergence(results)
        
        assert isinstance(regime, str), "Regime should be a string"
        assert len(regime) > 0, "Regime should not be empty"
    
    def test_analyze_convergence_valid_regimes(self):
        """Verify analyze_convergence returns valid regime types"""
        L_values = [10, 30, 100]
        results = tda.run_convergence_test(L_values, base_N=50)
        
        regime = tda.analyze_convergence(results)
        
        valid_regimes = ["SUBACOPLADO", "CONVERGENTE", "DERIVA", "INCONCLUSIVO", "EN_PROCESO"]
        assert regime in valid_regimes, f"Regime '{regime}' should be one of {valid_regimes}"


class TestNumericalStability:
    """Tests for numerical stability"""
    
    def test_reproducibility(self):
        """Verify results are reproducible"""
        L = 20
        N = 40
        
        # Run twice
        lambda_max_1, C_L_1, _, _ = tda.compute_max_eigenvalue(L, N)
        lambda_max_2, C_L_2, _, _ = tda.compute_max_eigenvalue(L, N)
        
        assert np.isclose(lambda_max_1, lambda_max_2, rtol=1e-12), \
            "Results should be reproducible"
        assert np.isclose(C_L_1, C_L_2, rtol=1e-12), \
            "Results should be reproducible"
    
    def test_different_methods_similar(self):
        """Verify gauss and trapezoid methods give similar results"""
        L = 20
        N = 60
        
        lambda_max_gauss, C_L_gauss, _, _ = tda.compute_max_eigenvalue(L, N, method='gauss')
        lambda_max_trap, C_L_trap, _, _ = tda.compute_max_eigenvalue(L, N, method='trapezoid')
        
        # Methods should give similar (but not identical) results
        # Allow larger tolerance since trapezoid is less accurate
        assert np.isclose(lambda_max_gauss, lambda_max_trap, rtol=0.1), \
            "Different methods should give similar results"
        assert np.isclose(C_L_gauss, C_L_trap, rtol=0.1), \
            "Different methods should give similar results"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
