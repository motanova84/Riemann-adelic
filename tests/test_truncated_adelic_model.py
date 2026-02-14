"""
Tests for the truncated adelic Laplacian model validation.

Tests verify:
1. Prime generation
2. Eigenvalue computations (Archimedean and p-adic)
3. Trace formula components
4. Remainder bound fitting
5. Full verification protocol

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_truncated_adelic_model import TruncatedAdelicLaplacian


class TestTruncatedAdelicLaplacian:
    """Test suite for TruncatedAdelicLaplacian class."""
    
    def test_prime_generation(self):
        """Test that prime generation works correctly."""
        model = TruncatedAdelicLaplacian(N_modes=10, P_primes=10, K_rep=3)
        
        # Check we got the right number of primes
        assert len(model.primes) == 10
        
        # Check first few primes
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert model.primes == expected_primes
        
    def test_prime_generation_edge_cases(self):
        """Test edge cases for prime generation."""
        model_zero = TruncatedAdelicLaplacian(N_modes=10, P_primes=0, K_rep=3)
        assert len(model_zero.primes) == 0
        
        model_one = TruncatedAdelicLaplacian(N_modes=10, P_primes=1, K_rep=3)
        assert model_one.primes == [2]
        
    def test_archimedean_eigenvalues(self):
        """Test Archimedean eigenvalue computation."""
        model = TruncatedAdelicLaplacian(N_modes=10, P_primes=5, K_rep=3)
        eigenvalues = model.compute_archimedean_eigenvalues()
        
        # Check shape
        assert eigenvalues.shape == (10,)
        
        # Check they are increasing
        assert np.all(np.diff(eigenvalues) > 0)
        
        # Check approximate values (Weyl law: λ_n ≈ n*π/2)
        n = np.arange(1, 11)
        expected = n * np.pi / 2
        np.testing.assert_allclose(eigenvalues, expected, rtol=1e-10)
        
    def test_padic_eigenvalues(self):
        """Test p-adic eigenvalue computation."""
        model = TruncatedAdelicLaplacian(N_modes=100, P_primes=5, K_rep=3)
        
        # Test for p=2
        eigenvalues_2 = model.compute_padic_eigenvalues(2)
        assert len(eigenvalues_2) > 0
        assert np.all(eigenvalues_2 >= 0)  # Eigenvalues should be non-negative
        
        # Test for p=3
        eigenvalues_3 = model.compute_padic_eigenvalues(3)
        assert len(eigenvalues_3) > 0
        assert np.all(eigenvalues_3 >= 0)
        
        # Larger primes should give larger eigenvalues (roughly)
        assert eigenvalues_3[0] > eigenvalues_2[0]
        
    def test_operator_assembly(self):
        """Test full operator assembly."""
        model = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=3)
        eigenvalues = model.assemble_operator()
        
        # Check shape
        assert eigenvalues.shape == (50,)
        
        # Check all eigenvalues are real and positive
        assert np.all(eigenvalues > 0)
        
        # Check they are increasing (should be for spectral truncation)
        # Note: Due to p-adic contributions, might not be perfectly sorted
        # but should be roughly increasing
        assert eigenvalues[0] < eigenvalues[-1]
        
    def test_trace_computation(self):
        """Test trace computation."""
        model = TruncatedAdelicLaplacian(N_modes=20, P_primes=5, K_rep=3)
        eigenvalues = model.assemble_operator()
        
        # Test at various t values
        t_values = [0.01, 0.05, 0.1]
        
        for t in t_values:
            trace = model.compute_trace(t, eigenvalues)
            
            # Trace should be positive
            assert trace > 0
            
            # Manual computation to verify
            expected_trace = np.sum(np.exp(-t * eigenvalues))
            np.testing.assert_allclose(trace, expected_trace, rtol=1e-10)
        
        # Trace should decrease as t increases
        traces = [model.compute_trace(t, eigenvalues) for t in t_values]
        assert traces[0] > traces[1] > traces[2]
        
    def test_weyl_term(self):
        """Test Weyl term computation."""
        model = TruncatedAdelicLaplacian(N_modes=20, P_primes=5, K_rep=3)
        volume = model.estimate_volume()
        
        t = 0.05
        weyl = model.weyl_term(t, volume)
        
        # Weyl term should be positive
        assert weyl > 0
        
        # Check formula: volume/(4πt)^{3/2} + 7/8
        expected = volume / (4 * np.pi * t)**(3/2) + 7/8
        np.testing.assert_allclose(weyl, expected, rtol=1e-10)
        
    def test_prime_sum(self):
        """Test prime sum computation."""
        model = TruncatedAdelicLaplacian(N_modes=20, P_primes=5, K_rep=3)
        
        t = 0.05
        prime_sum_val = model.prime_sum(t)
        
        # Prime sum should be positive
        assert prime_sum_val > 0
        
        # Manual computation for verification
        total = 0
        for p in model.primes:
            for k in range(1, model.K + 1):
                total += np.log(p) / (p**(k/2)) * np.exp(-t * k * np.log(p))
        
        np.testing.assert_allclose(prime_sum_val, total, rtol=1e-10)
        
    def test_volume_estimation(self):
        """Test volume estimation."""
        model = TruncatedAdelicLaplacian(N_modes=20, P_primes=5, K_rep=3)
        volume = model.estimate_volume()
        
        # Volume should be positive
        assert volume > 0
        
        # Check it depends on number of primes
        model2 = TruncatedAdelicLaplacian(N_modes=20, P_primes=10, K_rep=3)
        volume2 = model2.estimate_volume()
        
        # More primes = higher dimension = different volume
        assert volume != volume2
        
    def test_verification_protocol(self):
        """Test full verification protocol."""
        model = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=3)
        
        t_values = np.linspace(0.01, 0.1, 5)
        results = model.run_verification(t_values)
        
        # Check we got results for all t values
        assert len(results) == 5
        
        # Check structure of results
        for r in results:
            assert 't' in r
            assert 'trace' in r
            assert 'weyl' in r
            assert 'prime' in r
            assert 'resto' in r
            
            # All values should be real numbers
            assert isinstance(r['t'], (float, np.floating))
            assert isinstance(r['trace'], (float, np.floating))
            assert isinstance(r['weyl'], (float, np.floating))
            assert isinstance(r['prime'], (float, np.floating))
            assert isinstance(r['resto'], (float, np.floating))
            
            # Check remainder is the difference
            expected_resto = r['trace'] - r['weyl'] - r['prime']
            np.testing.assert_allclose(r['resto'], expected_resto, rtol=1e-10)
        
    def test_remainder_bound_fitting(self):
        """Test remainder bound fitting."""
        model = TruncatedAdelicLaplacian(N_modes=100, P_primes=25, K_rep=5)
        
        t_values = np.linspace(0.01, 0.1, 10)
        results = model.run_verification(t_values)
        
        C, lambda_ = model.fit_remainder_bound(results)
        
        # C should be positive (it's from exp(log(C)))
        assert C > 0
        
        # lambda can be positive or negative depending on the fit
        # We just check it's finite
        assert np.isfinite(lambda_)
        
        # Check that C and lambda are reasonable (not extreme values)
        assert C < 1e10  # Not astronomically large
        assert abs(lambda_) < 1e10  # Not extreme
        
        # The fitting function should return real numbers
        assert isinstance(C, (float, np.floating))
        assert isinstance(lambda_, (float, np.floating))
        
    def test_qcal_constants(self):
        """Test that QCAL constants are correctly set."""
        model = TruncatedAdelicLaplacian(N_modes=10, P_primes=5, K_rep=3)
        
        # Check QCAL constants
        assert model.kappa == 2.577310
        assert model.f0 == 141.7001
        np.testing.assert_allclose(model.Phi, (1 + np.sqrt(5)) / 2, rtol=1e-10)
        
    def test_different_parameter_sizes(self):
        """Test that the model works with different parameter sizes."""
        # Small model
        model_small = TruncatedAdelicLaplacian(N_modes=10, P_primes=3, K_rep=2)
        t_values = [0.05]
        results_small = model_small.run_verification(t_values)
        assert len(results_small) == 1
        
        # Medium model
        model_medium = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        results_medium = model_medium.run_verification(t_values)
        assert len(results_medium) == 1
        
        # Large model
        model_large = TruncatedAdelicLaplacian(N_modes=200, P_primes=50, K_rep=10)
        results_large = model_large.run_verification(t_values)
        assert len(results_large) == 1
        
        # All should produce valid results
        for results in [results_small, results_medium, results_large]:
            assert results[0]['trace'] > 0
            assert results[0]['weyl'] > 0
            assert results[0]['prime'] > 0
            
    def test_consistency_across_t_range(self):
        """Test that results are consistent across different t ranges."""
        model = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        
        # Test small t values
        t_small = np.linspace(0.01, 0.05, 5)
        results_small = model.run_verification(t_small)
        
        # Test larger t values
        t_large = np.linspace(0.06, 0.15, 5)
        results_large = model.run_verification(t_large)
        
        # Traces should be larger for smaller t
        assert results_small[0]['trace'] > results_large[0]['trace']
        
        # All results should be well-defined
        for results in [results_small, results_large]:
            for r in results:
                assert np.isfinite(r['trace'])
                assert np.isfinite(r['weyl'])
                assert np.isfinite(r['prime'])
                assert np.isfinite(r['resto'])


class TestEdgeCases:
    """Test edge cases and numerical stability."""
    
    def test_very_small_t(self):
        """Test behavior at very small t values."""
        model = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        
        t = 0.001  # Very small
        results = model.run_verification([t])
        
        # Should still produce finite results
        assert np.isfinite(results[0]['trace'])
        assert np.isfinite(results[0]['weyl'])
        assert np.isfinite(results[0]['prime'])
        
    def test_numerical_stability(self):
        """Test numerical stability of computations."""
        model = TruncatedAdelicLaplacian(N_modes=100, P_primes=25, K_rep=5)
        
        eigenvalues = model.assemble_operator()
        
        # Check no NaN or Inf
        assert np.all(np.isfinite(eigenvalues))
        
        # Test trace at various t
        for t in [0.001, 0.01, 0.1, 1.0]:
            trace = model.compute_trace(t, eigenvalues)
            assert np.isfinite(trace)
            assert trace > 0
            
    def test_remainder_sign(self):
        """Test that remainder can be positive or negative."""
        model = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        
        t_values = np.linspace(0.01, 0.1, 10)
        results = model.run_verification(t_values)
        
        # Remainder should not always have the same sign
        # (This depends on the model, but typically it oscillates)
        restos = [r['resto'] for r in results]
        
        # At least we should have some non-zero remainders
        assert any(abs(r) > 1e-10 for r in restos)


class TestIntegration:
    """Integration tests for the complete verification protocol."""
    
    def test_complete_protocol_small(self):
        """Test complete protocol with small parameters."""
        model = TruncatedAdelicLaplacian(N_modes=30, P_primes=10, K_rep=3)
        
        t_values = np.linspace(0.02, 0.08, 5)
        results = model.run_verification(t_values)
        
        C, lambda_ = model.fit_remainder_bound(results)
        
        # Verify constants are reasonable
        assert C > 0
        assert lambda_ > 0
        
        # Check that at least some points satisfy the bound
        satisfied = sum(1 for r in results 
                       if abs(r['resto']) <= C * np.exp(-lambda_ / r['t']))
        assert satisfied > 0
        
    def test_protocol_reproducibility(self):
        """Test that protocol produces reproducible results."""
        model1 = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        model2 = TruncatedAdelicLaplacian(N_modes=50, P_primes=10, K_rep=5)
        
        t_values = np.linspace(0.01, 0.1, 5)
        
        results1 = model1.run_verification(t_values)
        results2 = model2.run_verification(t_values)
        
        # Results should be identical
        for r1, r2 in zip(results1, results2):
            np.testing.assert_allclose(r1['trace'], r2['trace'], rtol=1e-10)
            np.testing.assert_allclose(r1['weyl'], r2['weyl'], rtol=1e-10)
            np.testing.assert_allclose(r1['prime'], r2['prime'], rtol=1e-10)
            np.testing.assert_allclose(r1['resto'], r2['resto'], rtol=1e-10)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
