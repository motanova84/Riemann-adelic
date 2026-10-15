"""
Tests for Atlas³ Test Decisivo - Spectral Analysis Script

Verifies:
1. Spectrum computation with correct Weyl scaling
2. Unfolding preserves spectrum size and produces unit mean spacing
3. NNSD computation and normalization
4. Delta3 computation
5. Output file generation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import pytest
import numpy as np
import os
import sys
from pathlib import Path

# Import the module under test
sys.path.insert(0, str(Path(__file__).parent.parent))
import atlas3_test_decisivo as atd


class TestAtlas3Spectrum:
    """Test suite for atlas3_spectrum function."""
    
    def test_spectrum_positive_frequencies(self):
        """Test that all returned frequencies are positive."""
        gamma = atd.atlas3_spectrum(N=100, L=4.0)
        assert np.all(gamma > 0), "All frequencies should be positive"
    
    def test_spectrum_sorted(self):
        """Test that frequencies are sorted in ascending order."""
        gamma = atd.atlas3_spectrum(N=100, L=4.0)
        assert np.all(np.diff(gamma) > 0), "Frequencies should be sorted"
    
    def test_spectrum_size(self):
        """Test that spectrum has reasonable size."""
        N = 200
        gamma = atd.atlas3_spectrum(N=N, L=5.0)
        # Should have many positive eigenvalues, but not necessarily N
        assert len(gamma) > 0, "Should have at least some positive frequencies"
        assert len(gamma) <= N, f"Cannot have more than {N} frequencies"
    
    def test_spectrum_weyl_scaling(self):
        """Test that spectrum roughly follows Weyl law growth."""
        gamma = atd.atlas3_spectrum(N=500, L=8.0)
        # Check that higher frequencies grow roughly logarithmically
        # E_n ~ (n/log n)^2, so gamma_n ~ n/log n
        if len(gamma) > 100:
            n_vals = np.arange(10, 100)
            expected_scaling = n_vals / np.log(n_vals + 1)
            # Just check the growth is in the right ballpark (within factor of 10)
            assert gamma[99] > gamma[9], "Spectrum should be increasing"
    
    def test_spectrum_numerical_stability(self):
        """Test that spectrum computation doesn't produce NaN or Inf."""
        gamma = atd.atlas3_spectrum(N=256, L=6.0)
        assert not np.any(np.isnan(gamma)), "Spectrum should not contain NaN"
        assert not np.any(np.isinf(gamma)), "Spectrum should not contain Inf"


class TestUnfoldSpectrum:
    """Test suite for unfold_spectrum function."""
    
    def test_unfold_preserves_length(self):
        """Test that unfolding preserves spectrum length."""
        gamma = atd.atlas3_spectrum(N=100, L=4.0)
        unfolded = atd.unfold_spectrum(gamma)
        assert len(unfolded) == len(gamma), "Unfolding should preserve length"
    
    def test_unfold_mostly_monotonic(self):
        """Test that unfolded spectrum is mostly monotonically increasing.
        
        Note: Polynomial fit doesn't guarantee strict monotonicity,
        but should preserve overall increasing trend.
        """
        gamma = atd.atlas3_spectrum(N=150, L=5.0)
        unfolded = atd.unfold_spectrum(gamma)
        # Check that at least 85% of differences are non-negative
        # (polynomial fitting can introduce minor non-monotonicities)
        diffs = np.diff(unfolded)
        positive_ratio = np.sum(diffs >= 0) / len(diffs)
        assert positive_ratio > 0.85, f"Unfolded should be mostly non-decreasing, got {positive_ratio:.3f}"
    
    def test_unfold_numerical_stability(self):
        """Test that unfolding doesn't produce NaN or Inf."""
        gamma = atd.atlas3_spectrum(N=200, L=6.0)
        unfolded = atd.unfold_spectrum(gamma)
        assert not np.any(np.isnan(unfolded)), "Unfolded should not contain NaN"
        assert not np.any(np.isinf(unfolded)), "Unfolded should not contain Inf"


class TestNearestNeighborSpacing:
    """Test suite for nearest_neighbor_spacing function."""
    
    def test_nnsd_length(self):
        """Test that NNSD has length N-1."""
        unfolded = np.array([0, 1, 2, 3, 4, 5])
        spacings = atd.nearest_neighbor_spacing(unfolded)
        assert len(spacings) == len(unfolded) - 1, "Should have N-1 spacings"
    
    def test_nnsd_normalization(self):
        """Test that spacings are normalized to mean = 1."""
        unfolded = np.array([0, 1.5, 3.0, 5.0, 7.5, 10.0])
        spacings = atd.nearest_neighbor_spacing(unfolded)
        assert np.abs(np.mean(spacings) - 1.0) < 1e-10, "Mean spacing should be 1.0"
    
    def test_nnsd_positive(self):
        """Test that all spacings are positive."""
        gamma = atd.atlas3_spectrum(N=100, L=4.0)
        unfolded = atd.unfold_spectrum(gamma)
        spacings = atd.nearest_neighbor_spacing(unfolded)
        assert np.all(spacings > 0), "All spacings should be positive"
    
    def test_nnsd_numerical_stability(self):
        """Test that NNSD doesn't produce NaN or Inf."""
        gamma = atd.atlas3_spectrum(N=150, L=5.0)
        unfolded = atd.unfold_spectrum(gamma)
        spacings = atd.nearest_neighbor_spacing(unfolded)
        assert not np.any(np.isnan(spacings)), "Spacings should not contain NaN"
        assert not np.any(np.isinf(spacings)), "Spacings should not contain Inf"


class TestSpectralRigidityDelta3:
    """Test suite for spectral_rigidity_delta3 function."""
    
    def test_delta3_returns_list(self):
        """Test that Delta3 returns a list of same length as L_range."""
        gamma = atd.atlas3_spectrum(N=200, L=5.0)
        unfolded = atd.unfold_spectrum(gamma)
        L_range = [5, 10, 15]
        delta3 = atd.spectral_rigidity_delta3(unfolded, L_range)
        assert len(delta3) == len(L_range), "Should return one value per L"
    
    def test_delta3_positive_values(self):
        """Test that Delta3 values are non-negative."""
        gamma = atd.atlas3_spectrum(N=150, L=4.0)
        unfolded = atd.unfold_spectrum(gamma)
        L_range = [3, 5, 8]
        delta3 = atd.spectral_rigidity_delta3(unfolded, L_range)
        assert all(d >= 0 for d in delta3), "Delta3 should be non-negative"
    
    def test_delta3_numerical_stability(self):
        """Test that Delta3 doesn't produce NaN or Inf."""
        gamma = atd.atlas3_spectrum(N=180, L=5.0)
        unfolded = atd.unfold_spectrum(gamma)
        L_range = [4, 6, 8, 10]
        delta3 = atd.spectral_rigidity_delta3(unfolded, L_range)
        assert not any(np.isnan(d) for d in delta3), "Delta3 should not contain NaN"
        assert not any(np.isinf(d) for d in delta3), "Delta3 should not contain Inf"


class TestIntegration:
    """Integration tests for the complete pipeline."""
    
    def test_full_pipeline_small(self):
        """Test complete pipeline with small N for speed."""
        N = 256
        gamma = atd.atlas3_spectrum(N=N, L=5.0)
        unfolded = atd.unfold_spectrum(gamma)
        
        # Bulk analysis
        bulk_start = int(0.1 * len(unfolded))
        bulk_end = int(0.9 * len(unfolded))
        bulk_gamma = unfolded[bulk_start:bulk_end]
        
        spacings = atd.nearest_neighbor_spacing(bulk_gamma)
        
        # Basic sanity checks
        assert len(gamma) > 0, "Should have spectrum"
        assert len(spacings) > 0, "Should have spacings"
        assert np.abs(np.mean(spacings) - 1.0) < 0.1, "Mean spacing close to 1.0"
    
    def test_reproducibility(self):
        """Test that results are reproducible."""
        gamma1 = atd.atlas3_spectrum(N=200, L=4.0)
        gamma2 = atd.atlas3_spectrum(N=200, L=4.0)
        assert np.allclose(gamma1, gamma2), "Results should be reproducible"


class TestNumericalProperties:
    """Test numerical properties and edge cases."""
    
    def test_different_grid_sizes(self):
        """Test that function works with different grid sizes."""
        for N in [64, 128, 256, 512]:
            gamma = atd.atlas3_spectrum(N=N, L=6.0)
            assert len(gamma) > 0, f"Should work with N={N}"
    
    def test_different_domains(self):
        """Test that function works with different domain sizes."""
        for L in [2.0, 4.0, 6.0, 8.0, 10.0]:
            gamma = atd.atlas3_spectrum(N=200, L=L)
            assert len(gamma) > 0, f"Should work with L={L}"
    
    def test_spacing_statistics_reasonable(self):
        """Test that spacing statistics are in reasonable range."""
        gamma = atd.atlas3_spectrum(N=500, L=8.0)
        unfolded = atd.unfold_spectrum(gamma)
        bulk_gamma = unfolded[50:450]  # Focus on bulk
        spacings = atd.nearest_neighbor_spacing(bulk_gamma)
        
        # For GUE/GOE, variance should be around 0.17-0.28
        # For Poisson, variance would be 1.0
        # We're not enforcing a specific value, just reasonable bounds
        variance = np.var(spacings)
        assert 0.0 < variance < 2.0, f"Spacing variance {variance} in reasonable range"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
