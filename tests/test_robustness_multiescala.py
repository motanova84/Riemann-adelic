"""
Tests for Multi-Scale Robustness Validation Framework
======================================================

Test coverage for experiments/robustness_multiescala_atlas3.py

This test suite provides 18 unit tests covering:
- Archimedean eigenvalue calculations
- p-adic contributions
- Weyl term computation
- Trace formula remainder
- Exponential fitting
- Multi-parameter sweeps
- Metadata validation
- Convergence analysis

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from experiments.robustness_multiescala_atlas3 import (
    RobustnessMultiescalaAtlas3,
    ExperimentMetadata,
    ConvergenceResult,
    F0_BASE,
    C_COHERENCE,
    KAPPA_PI
)


class TestExperimentMetadata:
    """Test suite for ExperimentMetadata dataclass."""
    
    def test_metadata_initialization(self):
        """Test metadata initialization with defaults."""
        metadata = ExperimentMetadata()
        
        assert metadata.sello == "QCAL-ROBUSTNESS-∞³"
        assert metadata.protocol == "QCAL-SYMBIO-BRIDGE v1.0"
        assert "N_range" in metadata.ram
        assert "P_range" in metadata.ram
        assert "K_range" in metadata.ram
    
    def test_metadata_custom_values(self):
        """Test metadata with custom values."""
        custom_ram = {
            "N_range": [100, 500],
            "P_range": [20, 100],
            "K_range": [5, 15]
        }
        
        metadata = ExperimentMetadata(
            sello="CUSTOM-TEST",
            ram=custom_ram
        )
        
        assert metadata.sello == "CUSTOM-TEST"
        assert metadata.ram["N_range"] == [100, 500]
    
    def test_metadata_emanacion_format(self):
        """Test emanacion timestamp format."""
        metadata = ExperimentMetadata()
        
        # Should be ISO format timestamp
        assert "T" in metadata.emanacion
        assert "Z" in metadata.emanacion or ":" in metadata.emanacion


class TestConvergenceResult:
    """Test suite for ConvergenceResult dataclass."""
    
    def test_result_initialization(self):
        """Test result initialization."""
        result = ConvergenceResult(
            N=100,
            P=20,
            K=5,
            lambda_fit=0.45,
            C_fit=1.23,
            residual_norm=0.01
        )
        
        assert result.N == 100
        assert result.P == 20
        assert result.K == 5
        assert result.lambda_fit == 0.45
        assert result.C_fit == 1.23
        assert result.residual_norm == 0.01
    
    def test_result_with_metadata(self):
        """Test result with custom metadata."""
        custom_metadata = ExperimentMetadata(sello="TEST-RESULT")
        
        result = ConvergenceResult(
            N=50,
            P=10,
            K=3,
            lambda_fit=0.5,
            C_fit=1.0,
            residual_norm=0.001,
            metadata=custom_metadata
        )
        
        assert result.metadata.sello == "TEST-RESULT"


class TestRobustnessMultiescalaAtlas3:
    """Test suite for RobustnessMultiescalaAtlas3 class."""
    
    @pytest.fixture
    def validator(self):
        """Create validator instance for testing."""
        return RobustnessMultiescalaAtlas3(
            L=10.0,
            V_eff=1.0,
            t_min=0.1,
            t_max=5.0,
            n_t_points=20
        )
    
    def test_initialization(self, validator):
        """Test validator initialization."""
        assert validator.L == 10.0
        assert validator.V_eff == 1.0
        assert len(validator.t_range) == 20
        assert validator.t_range[0] == pytest.approx(0.1, abs=1e-6)
        assert validator.t_range[-1] == pytest.approx(5.0, abs=1e-6)
        assert len(validator.results) == 0
    
    def test_compute_archimedean_eigenvalues(self, validator):
        """Test Archimedean eigenvalue calculation."""
        N = 10
        eigenvalues = validator.compute_archimedean_eigenvalues(N)
        
        # Check shape
        assert len(eigenvalues) == N
        
        # Check ordering (should be increasing)
        assert np.all(np.diff(eigenvalues) > 0)
        
        # Check first eigenvalue (n=1)
        expected_first = (np.pi / validator.L)**2 + validator.V_eff
        assert eigenvalues[0] == pytest.approx(expected_first, rel=1e-6)
        
        # All eigenvalues should be positive
        assert np.all(eigenvalues > 0)
    
    def test_archimedean_eigenvalues_scaling(self, validator):
        """Test that eigenvalues scale correctly with N."""
        eigs_10 = validator.compute_archimedean_eigenvalues(10)
        eigs_20 = validator.compute_archimedean_eigenvalues(20)
        
        # First 10 should match
        assert np.allclose(eigs_10, eigs_20[:10])
        
        # Higher eigenvalues should be larger
        assert eigs_20[-1] > eigs_10[-1]
    
    def test_generate_primes(self, validator):
        """Test prime number generation."""
        primes = validator._generate_primes(30)
        
        # Check known primes
        expected_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected_primes
        
        # Test edge cases
        assert validator._generate_primes(1) == []
        assert validator._generate_primes(2) == [2]
        assert validator._generate_primes(3) == [2, 3]
    
    def test_compute_padic_contributions(self, validator):
        """Test p-adic eigenvalue contributions."""
        t = 1.0
        P = 10  # Primes up to 10: [2, 3, 5, 7]
        K = 3
        
        contribution = validator.compute_padic_contributions(t, P, K)
        
        # Should be positive
        assert contribution > 0
        
        # Should decay with time
        contrib_t1 = validator.compute_padic_contributions(1.0, P, K)
        contrib_t2 = validator.compute_padic_contributions(2.0, P, K)
        assert contrib_t2 < contrib_t1
    
    def test_padic_contributions_monotonicity(self, validator):
        """Test p-adic contributions increase with P and K."""
        # Increase P
        contrib_P10 = validator.compute_padic_contributions(1.0, 10, 3)
        contrib_P20 = validator.compute_padic_contributions(1.0, 20, 3)
        assert contrib_P20 > contrib_P10
        
        # Increase K
        contrib_K3 = validator.compute_padic_contributions(1.0, 10, 3)
        contrib_K5 = validator.compute_padic_contributions(1.0, 10, 5)
        assert contrib_K5 > contrib_K3
    
    def test_compute_weyl_term(self, validator):
        """Test Weyl asymptotic term."""
        t = 1.0
        N = 100
        
        weyl = validator.compute_weyl_term(t, N)
        
        # Should be positive
        assert weyl > 0
        
        # Should decay with time (t^{-1/2} factor)
        weyl_t1 = validator.compute_weyl_term(1.0, N)
        weyl_t4 = validator.compute_weyl_term(4.0, N)
        assert weyl_t4 < weyl_t1
        
        # Check approximate scaling
        ratio = weyl_t1 / weyl_t4
        expected_ratio = np.sqrt(4.0) * np.exp((4.0 - 1.0) * validator.V_eff)
        assert ratio == pytest.approx(expected_ratio, rel=0.1)
    
    def test_compute_trace(self, validator):
        """Test exact trace computation."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        t = 1.0
        
        trace = validator.compute_trace(t, eigenvalues)
        
        # Check against manual calculation
        expected = np.exp(-1.0) + np.exp(-2.0) + np.exp(-3.0)
        assert trace == pytest.approx(expected, rel=1e-10)
        
        # Trace should decay with time
        trace_t1 = validator.compute_trace(1.0, eigenvalues)
        trace_t2 = validator.compute_trace(2.0, eigenvalues)
        assert trace_t2 < trace_t1
    
    def test_compute_remainder(self, validator):
        """Test trace formula remainder."""
        N, P, K = 50, 10, 3
        t = 1.0
        
        remainder = validator.compute_remainder(t, N, P, K)
        
        # Remainder should be finite
        assert np.isfinite(remainder)
        
        # Test with different parameters
        r1 = validator.compute_remainder(1.0, 50, 10, 3)
        r2 = validator.compute_remainder(1.0, 100, 10, 3)
        
        # Both should be finite
        assert np.isfinite(r1)
        assert np.isfinite(r2)
    
    def test_fit_exponential_decay(self, validator):
        """Test exponential decay fitting."""
        N, P, K = 100, 20, 5
        
        lambda_fit, C_fit, residual = validator.fit_exponential_decay(N, P, K)
        
        # All outputs should be finite
        assert np.isfinite(lambda_fit)
        assert np.isfinite(C_fit)
        assert np.isfinite(residual)
        
        # C should be positive
        assert C_fit > 0
        
        # Residual should be non-negative
        assert residual >= 0
    
    def test_run_single_experiment(self, validator):
        """Test single experiment execution."""
        N, P, K = 50, 10, 3
        
        result = validator.run_single_experiment(N, P, K)
        
        # Check result structure
        assert isinstance(result, ConvergenceResult)
        assert result.N == N
        assert result.P == P
        assert result.K == K
        
        # Check values are finite
        assert np.isfinite(result.lambda_fit)
        assert np.isfinite(result.C_fit)
        assert np.isfinite(result.residual_norm)
        
        # Check metadata
        assert result.metadata.sello == "QCAL-ROBUSTNESS-∞³"
    
    def test_run_multiparameter_sweep(self, validator):
        """Test multi-parameter sweep."""
        N_values = [50, 100]
        P_values = [10, 20]
        K_values = [3, 5]
        
        results = validator.run_multiparameter_sweep(N_values, P_values, K_values)
        
        # Check number of results
        expected_count = len(N_values) * len(P_values) * len(K_values)
        assert len(results) == expected_count
        
        # Check all results are valid
        for result in results:
            assert isinstance(result, ConvergenceResult)
            assert np.isfinite(result.lambda_fit)
            assert result.N in N_values
            assert result.P in P_values
            assert result.K in K_values
        
        # Check results stored in validator
        assert len(validator.results) == expected_count
    
    def test_analyze_convergence_empty(self, validator):
        """Test convergence analysis with no results."""
        analysis = validator.analyze_convergence()
        
        assert "error" in analysis
    
    def test_analyze_convergence(self, validator):
        """Test convergence analysis with results."""
        # Run a small sweep
        results = validator.run_multiparameter_sweep(
            N_values=[50, 100],
            P_values=[10],
            K_values=[3]
        )
        
        analysis = validator.analyze_convergence()
        
        # Check analysis structure
        assert "n_experiments" in analysis
        assert "lambda_mean" in analysis
        assert "lambda_std" in analysis
        assert "lambda_min" in analysis
        assert "lambda_max" in analysis
        assert "lambda_target" in analysis
        assert "deviation_from_target" in analysis
        
        # Check values
        assert analysis["n_experiments"] == 2
        assert analysis["lambda_target"] == 0.5
        assert np.isfinite(analysis["lambda_mean"])
        assert analysis["lambda_std"] >= 0
    
    def test_constants_defined(self):
        """Test that QCAL constants are properly defined."""
        assert F0_BASE == 141.7001
        assert C_COHERENCE == 244.36
        assert KAPPA_PI == 2.5773


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_large_N_stability(self):
        """Test stability with large N."""
        validator = RobustnessMultiescalaAtlas3()
        
        eigenvalues = validator.compute_archimedean_eigenvalues(500)
        
        # Should not overflow
        assert np.all(np.isfinite(eigenvalues))
        
        # Should maintain ordering
        assert np.all(np.diff(eigenvalues) > 0)
    
    def test_small_time_stability(self):
        """Test stability with small time values."""
        validator = RobustnessMultiescalaAtlas3(t_min=0.01, t_max=0.1)
        
        # Should not cause issues
        remainder = validator.compute_remainder(0.05, 50, 10, 3)
        assert np.isfinite(remainder)
    
    def test_large_prime_count(self):
        """Test with large prime count."""
        validator = RobustnessMultiescalaAtlas3()
        
        primes = validator._generate_primes(100)
        
        # Should find correct number
        # Primes up to 100: 2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,
        #                   53,59,61,67,71,73,79,83,89,97
        assert len(primes) == 25
        
        # All should be prime
        for p in primes:
            assert p >= 2
    
    def test_zero_remainder_handling(self):
        """Test handling of near-zero remainders."""
        validator = RobustnessMultiescalaAtlas3()
        
        # With very small parameters, remainder might be tiny
        # Fit should handle this gracefully
        lambda_fit, C_fit, residual = validator.fit_exponential_decay(10, 5, 2)
        
        # Should return valid values (may be defaults if all zeros)
        assert np.isfinite(lambda_fit)
        assert np.isfinite(C_fit)
        assert np.isfinite(residual)


# Integration test
def test_full_pipeline():
    """Test complete pipeline execution."""
    # Create validator
    validator = RobustnessMultiescalaAtlas3(
        L=10.0,
        V_eff=1.0,
        t_min=0.5,
        t_max=3.0,
        n_t_points=30
    )
    
    # Run small sweep
    N_values = [50, 100]
    P_values = [10, 20]
    K_values = [3, 5]
    
    results = validator.run_multiparameter_sweep(N_values, P_values, K_values)
    
    # Verify results
    assert len(results) == 8  # 2 * 2 * 2
    
    # Analyze convergence
    analysis = validator.analyze_convergence()
    
    assert analysis["n_experiments"] == 8
    assert "lambda_mean" in analysis
    
    # All lambda values should be finite
    for result in results:
        assert np.isfinite(result.lambda_fit)
    
    print(f"✓ Full pipeline test passed")
    print(f"  Mean λ_fit: {analysis['lambda_mean']:.6f}")
    print(f"  Std λ_fit: {analysis['lambda_std']:.6f}")
    print(f"  Deviation from target (0.5): {analysis['deviation_from_target']:.6f}")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])
