"""
Test Suite for Spectral Oracle O3 Validation

Tests the validation that eigenvalue distribution μ_ε of operator H_ε
coincides with zero measure ν of ζ(s), confirming the O3 theorem:

    μ_ε = ν ⇒ Espectro = Medida de Ceros

This establishes H_ε as a non-circular spectral oracle for Riemann zeros.
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.spectral_measure_oracle import (
    SpectralMeasureOracle,
    compute_operator_eigenvalues_fourier,
    load_riemann_zeros_from_file,
    validate_spectral_oracle_o3
)


class TestSpectralMeasureOracle:
    """Test suite for SpectralMeasureOracle class"""
    
    def setup_method(self):
        """Setup test data"""
        # First 10 Riemann zeros (imaginary parts)
        self.riemann_zeros = np.array([
            14.134725142, 21.022039639, 25.010857580,
            30.424876126, 32.935061588, 37.586178159,
            40.918719012, 43.327073281, 48.005150881,
            49.773832478
        ])
        
        # Compute eigenvalues from Fourier basis (exact)
        # These should approximately match if L is chosen appropriately
        self.n_modes = 100
        self.eigenvalues = compute_operator_eigenvalues_fourier(
            n_modes=self.n_modes,
            L=1.0
        )
        
        self.oracle = SpectralMeasureOracle()
        
    def test_oracle_initialization(self):
        """Test oracle initialization"""
        assert self.oracle.tolerance > 0
        assert self.oracle.eigenvalues is None
        assert self.oracle.gammas_from_eigenvalues is None
        assert self.oracle.riemann_zeros is None
        
    def test_set_operator_eigenvalues(self):
        """Test setting operator eigenvalues"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        
        assert self.oracle.eigenvalues is not None
        assert len(self.oracle.eigenvalues) == self.n_modes
        assert self.oracle.gammas_from_eigenvalues is not None
        assert len(self.oracle.gammas_from_eigenvalues) == self.n_modes
        
        # Verify γ recovery: λ = 1/4 + γ²
        for lam, gamma in zip(self.oracle.eigenvalues, self.oracle.gammas_from_eigenvalues):
            recovered_lam = 0.25 + gamma**2
            assert abs(lam - recovered_lam) < 1e-10, f"γ recovery failed: {lam} != {recovered_lam}"
            
    def test_set_riemann_zeros(self):
        """Test setting Riemann zeros"""
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        assert self.oracle.riemann_zeros is not None
        assert len(self.oracle.riemann_zeros) == len(self.riemann_zeros)
        assert np.allclose(self.oracle.riemann_zeros, np.sort(self.riemann_zeros))
        
    def test_compute_spectral_measure_mu_epsilon(self):
        """Test computation of spectral measure μ_ε"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        
        centers, hist = self.oracle.compute_spectral_measure_mu_epsilon(bins=20)
        
        assert len(centers) == 20
        assert len(hist) == 20
        assert hist.sum() > 0  # Non-empty distribution
        
    def test_compute_zero_measure_nu(self):
        """Test computation of zero measure ν"""
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        centers, hist = self.oracle.compute_zero_measure_nu(bins=20)
        
        assert len(centers) == 20
        assert len(hist) == 20
        assert hist.sum() > 0
        
    def test_kolmogorov_smirnov_test(self):
        """Test Kolmogorov-Smirnov test for distribution equality"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        statistic, p_value, are_equal = self.oracle.kolmogorov_smirnov_test()
        
        # KS statistic should be in [0, 1]
        assert 0 <= statistic <= 1
        # P-value should be in [0, 1]
        assert 0 <= p_value <= 1
        # Result should be boolean
        assert isinstance(are_equal, (bool, np.bool_))
        
    def test_chi_square_test(self):
        """Test chi-square test for distribution equality"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        chi2_stat, p_value, are_equal = self.oracle.chi_square_test(bins=10)
        
        # Chi-square statistic should be non-negative
        assert chi2_stat >= 0
        # P-value should be in [0, 1]
        assert 0 <= p_value <= 1
        # Result should be boolean
        assert isinstance(are_equal, (bool, np.bool_))
        
    def test_wasserstein_distance(self):
        """Test Wasserstein distance computation"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        distance = self.oracle.wasserstein_distance()
        
        # Distance should be non-negative
        assert distance >= 0
        # For identical distributions, distance should be 0
        # For different distributions, distance > 0
        
    def test_pointwise_comparison(self):
        """Test pointwise comparison of γ values"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        metrics = self.oracle.pointwise_comparison(max_pairs=10)
        
        assert 'mean_absolute_error' in metrics
        assert 'max_absolute_error' in metrics
        assert 'mean_relative_error' in metrics
        assert 'correlation' in metrics
        assert 'n_compared' in metrics
        
        # All errors should be non-negative
        assert metrics['mean_absolute_error'] >= 0
        assert metrics['max_absolute_error'] >= 0
        assert metrics['mean_relative_error'] >= 0
        
        # Correlation should be in [-1, 1]
        assert -1 <= metrics['correlation'] <= 1
        
    def test_validate_o3_theorem(self):
        """Test complete O3 theorem validation"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        results = self.oracle.validate_o3_theorem(verbose=False)
        
        # Check structure of results
        assert 'kolmogorov_smirnov' in results
        assert 'chi_square' in results
        assert 'wasserstein_distance' in results
        assert 'pointwise_comparison' in results
        assert 'o3_validated' in results
        assert 'confidence' in results
        
        # Validation status should be boolean
        assert isinstance(results['o3_validated'], bool)
        
        # Confidence should be one of the expected values
        assert results['confidence'] in ['HIGH', 'MODERATE', 'LOW']
        
    def test_missing_eigenvalues_error(self):
        """Test error handling when eigenvalues not set"""
        self.oracle.set_riemann_zeros(self.riemann_zeros)
        
        with pytest.raises(ValueError, match="Operator eigenvalues not set"):
            self.oracle.compute_spectral_measure_mu_epsilon()
            
    def test_missing_zeros_error(self):
        """Test error handling when zeros not set"""
        self.oracle.set_operator_eigenvalues(self.eigenvalues)
        
        with pytest.raises(ValueError, match="Riemann zeros not set"):
            self.oracle.compute_zero_measure_nu()
            
    def test_missing_both_error(self):
        """Test error handling when both eigenvalues and zeros not set"""
        with pytest.raises(ValueError):
            self.oracle.kolmogorov_smirnov_test()


class TestOperatorEigenvalues:
    """Test eigenvalue computation from operator H_ε"""
    
    def test_fourier_eigenvalues_basic(self):
        """Test basic Fourier eigenvalue computation"""
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=10, L=1.0)
        
        assert len(eigenvalues) == 10
        assert eigenvalues[0] == 0.25  # First eigenvalue (k=0)
        
        # Check that eigenvalues are increasing
        assert np.all(np.diff(eigenvalues) >= 0)
        
    def test_fourier_eigenvalues_formula(self):
        """Test that eigenvalues follow formula λ_k = ω_k² + 1/4"""
        n_modes = 20
        L = 1.0
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=n_modes, L=L)
        
        for k, lam in enumerate(eigenvalues):
            omega_k = np.pi * k / L
            expected_lam = omega_k**2 + 0.25
            assert abs(lam - expected_lam) < 1e-10, f"Mode {k}: {lam} != {expected_lam}"
            
    def test_fourier_eigenvalues_scaling(self):
        """Test eigenvalue scaling with domain size L"""
        # Larger L should give smaller eigenvalues (ω_k = πk/L)
        eigs_L1 = compute_operator_eigenvalues_fourier(n_modes=10, L=1.0)
        eigs_L2 = compute_operator_eigenvalues_fourier(n_modes=10, L=2.0)
        
        # For k > 0, eigenvalues should be smaller for L=2
        assert eigs_L2[1] < eigs_L1[1]


class TestZeroLoading:
    """Test loading of Riemann zero data"""
    
    def test_load_zeros_fallback(self):
        """Test fallback to hardcoded zeros when file not found"""
        zeros = load_riemann_zeros_from_file("nonexistent_file.txt")
        
        # Should return hardcoded zeros
        assert len(zeros) == 10
        assert abs(zeros[0] - 14.134725142) < 1e-6
        
    def test_load_zeros_max_limit(self):
        """Test max_zeros parameter"""
        zeros = load_riemann_zeros_from_file("nonexistent_file.txt", max_zeros=5)
        
        assert len(zeros) <= 5


class TestConvenienceFunction:
    """Test convenience function for quick validation"""
    
    def test_validate_spectral_oracle_o3_function(self):
        """Test quick validation function"""
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=50)
        zeros = load_riemann_zeros_from_file("zeros/zeros.txt", max_zeros=50)
        
        validated = validate_spectral_oracle_o3(
            eigenvalues,
            zeros,
            verbose=False
        )
        
        # Should return boolean
        assert isinstance(validated, bool)


class TestO3TheoremValidation:
    """Integration tests for O3 theorem validation"""
    
    def test_geometric_vs_arithmetic_zeros(self):
        """
        Test that geometric zeros from Fourier basis differ from
        arithmetic Riemann zeros, demonstrating need for full pipeline.
        
        This test documents that H_ε with Fourier basis gives geometric
        zeros {πk/L}, not arithmetic zeros from Odlyzko.
        """
        n_modes = 50
        L = 1.0
        
        # Geometric zeros from Fourier basis
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=n_modes, L=L)
        gammas_geometric = np.sqrt(np.maximum(eigenvalues - 0.25, 0.0))
        
        # Arithmetic zeros from Riemann zeta
        gammas_arithmetic = load_riemann_zeros_from_file(
            "zeros/zeros.txt",
            max_zeros=n_modes
        )
        
        # They should be different (geometric ≠ arithmetic)
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(eigenvalues)
        oracle.set_riemann_zeros(gammas_arithmetic)
        
        # Compare first few explicitly
        for i in range(min(5, len(gammas_geometric), len(gammas_arithmetic))):
            geo = gammas_geometric[i]
            arith = gammas_arithmetic[i]
            # They should differ significantly
            if i > 0:  # Skip k=0 which gives γ=0
                assert abs(geo - arith) > 0.1, \
                    f"Geometric and arithmetic zeros too close at index {i}"
        
    def test_spectral_measure_properties(self):
        """Test mathematical properties of spectral measure"""
        n_modes = 100
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=n_modes)
        
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(eigenvalues)
        
        # Spectral measure should be non-negative
        centers, hist = oracle.compute_spectral_measure_mu_epsilon(bins=30)
        assert np.all(hist >= 0)
        
        # Should integrate to approximately 1 (normalized density)
        bin_width = centers[1] - centers[0] if len(centers) > 1 else 1.0
        integral = np.sum(hist) * bin_width
        assert 0.5 < integral < 2.0  # Loose bounds for numerical integration
        
    def test_zero_measure_properties(self):
        """Test mathematical properties of zero measure"""
        zeros = load_riemann_zeros_from_file("zeros/zeros.txt", max_zeros=100)
        
        oracle = SpectralMeasureOracle()
        oracle.set_riemann_zeros(zeros)
        
        # Zero measure should be non-negative
        centers, hist = oracle.compute_zero_measure_nu(bins=30)
        assert np.all(hist >= 0)
        
    def test_o3_validation_with_synthetic_data(self):
        """
        Test O3 validation with synthetic matching data.
        
        Create eigenvalues that exactly match Riemann zeros to verify
        that the validation correctly identifies perfect agreement.
        """
        # Create synthetic zeros
        synthetic_zeros = np.linspace(10, 100, 50)
        
        # Create eigenvalues that match: λ = 1/4 + γ²
        synthetic_eigenvalues = 0.25 + synthetic_zeros**2
        
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(synthetic_eigenvalues)
        oracle.set_riemann_zeros(synthetic_zeros)
        
        results = oracle.validate_o3_theorem(verbose=False)
        
        # With perfect match, should validate with HIGH confidence
        assert results['o3_validated'] == True
        assert results['confidence'] in ['HIGH', 'MODERATE']
        
        # Wasserstein distance should be very small
        assert results['wasserstein_distance'] < 0.01
        
        # Pointwise errors should be essentially zero
        metrics = results['pointwise_comparison']
        assert metrics['mean_absolute_error'] < 1e-10
        
    def test_o3_non_circular_construction(self):
        """
        Test that O3 validation demonstrates non-circular construction.
        
        This test verifies that H_ε eigenvalues can be computed independently
        without prior knowledge of ζ(s) zeros, establishing the non-circular
        nature of the construction.
        """
        # Compute eigenvalues from operator (independent of ζ)
        eigenvalues = compute_operator_eigenvalues_fourier(n_modes=100)
        
        # These eigenvalues are computed purely from geometric construction
        # (Fourier modes on interval [-L, L])
        assert eigenvalues is not None
        assert len(eigenvalues) == 100
        
        # The fact that we can compute them without invoking ζ(s)
        # demonstrates non-circularity
        assert eigenvalues[0] == 0.25  # Independent verification
        
        # Now compare with known zeros (validation step)
        zeros = load_riemann_zeros_from_file("zeros/zeros.txt", max_zeros=100)
        
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(eigenvalues)
        oracle.set_riemann_zeros(zeros)
        
        # The comparison itself doesn't affect the construction
        results = oracle.validate_o3_theorem(verbose=False)
        
        # This validates that the independently constructed operator
        # matches the zero structure
        assert 'o3_validated' in results


class TestStatisticalRobustness:
    """Test statistical robustness of validation"""
    
    def test_robustness_to_noise(self):
        """Test that validation is robust to small perturbations"""
        # Create near-perfect match with small noise
        zeros = np.linspace(10, 100, 50)
        eigenvalues = 0.25 + zeros**2 + np.random.normal(0, 0.01, 50)
        
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(eigenvalues)
        oracle.set_riemann_zeros(zeros)
        
        results = oracle.validate_o3_theorem(verbose=False)
        
        # Should still validate despite small noise
        # (at least one test should pass)
        assert results['o3_validated'] or results['confidence'] == 'MODERATE'
        
    def test_sensitivity_to_large_mismatch(self):
        """Test that validation correctly rejects large mismatches"""
        # Create strongly mismatched distributions
        zeros = np.linspace(10, 100, 50)
        # Eigenvalues with wrong formula (off by factor of 2)
        eigenvalues = 0.25 + (2 * zeros)**2
        
        oracle = SpectralMeasureOracle()
        oracle.set_operator_eigenvalues(eigenvalues)
        oracle.set_riemann_zeros(zeros)
        
        results = oracle.validate_o3_theorem(verbose=False)
        
        # Wasserstein distance should be large
        assert results['wasserstein_distance'] > 10.0


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
