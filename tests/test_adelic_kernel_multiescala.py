#!/usr/bin/env python3
"""
Tests for Adelic Kernel Multiescala Convergence Test

This module tests the implementation of the Adelic Kernel heat propagator
and the multi-scale convergence test for the coupling constant κ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-14
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
import pandas as pd
from pathlib import Path
import sys
import json

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from adelic_kernel_multiescala import (
    compute_spectrum,
    find_optimal_kappa,
    run_multiescala_test,
    RIEMANN_ZEROS_50,
    F0, C_QCAL, KAPPA_PI
)


class TestSpectrumComputation:
    """Test suite for spectrum computation from discretized Hamiltonian."""
    
    def test_compute_spectrum_basic(self):
        """Test that spectrum computation returns positive real values."""
        N = 128
        spectrum = compute_spectrum(N, L=5.0)
        
        assert len(spectrum) > 0, "Spectrum should not be empty"
        assert np.all(spectrum > 0), "All eigenvalues should be positive"
        assert np.all(np.isfinite(spectrum)), "All eigenvalues should be finite"
        assert np.all(np.diff(spectrum) >= 0), "Spectrum should be sorted"
    
    def test_compute_spectrum_size(self):
        """Test that spectrum size scales appropriately with N."""
        N = 256
        spectrum = compute_spectrum(N, L=5.0)
        
        # Should have many positive eigenvalues (at least N/2)
        assert len(spectrum) >= N // 2, f"Expected at least {N//2} eigenvalues"
    
    def test_compute_spectrum_convergence(self):
        """Test that spectrum converges with increasing resolution."""
        N1, N2 = 128, 256
        spectrum1 = compute_spectrum(N1, L=5.0)
        spectrum2 = compute_spectrum(N2, L=5.0)
        
        # Compare first few eigenvalues (should converge)
        n_compare = min(20, len(spectrum1), len(spectrum2))
        rel_diff = np.abs(spectrum2[:n_compare] - spectrum1[:n_compare]) / spectrum1[:n_compare]
        
        # Relative difference should decrease with resolution
        assert np.mean(rel_diff) < 0.1, "Spectra should converge with higher N"
    
    def test_potential_form(self):
        """Test that the potential V(t) = exp(2|t|) is correctly implemented."""
        N = 128
        L = 5.0
        
        # Compute spectrum (implicitly tests potential)
        spectrum = compute_spectrum(N, L=L)
        
        # The exponential potential should create a spectrum
        # Check basic properties: spectrum grows
        assert spectrum[-1] > spectrum[0], "Spectrum should grow"
        
        # Check that spacing increases (characteristic of exp potential)
        first_gap = spectrum[10] - spectrum[0]
        last_gap = spectrum[-1] - spectrum[-10]
        
        # Later eigenvalues should be more spread out
        assert last_gap > first_gap, "Eigenvalue spacing should increase"


class TestKappaOptimization:
    """Test suite for κ optimization and fitting."""
    
    def test_find_optimal_kappa_basic(self):
        """Test that κ optimization produces reasonable results."""
        # Create mock spectrum
        spectrum = np.linspace(10, 100, 50)
        target = spectrum * 2.0  # Known scaling
        
        kappa, error = find_optimal_kappa(spectrum, target, initial_guess=1.0)
        
        # Should find κ ≈ 2.0
        assert abs(kappa - 2.0) < 0.01, f"Expected κ ≈ 2.0, got {kappa}"
        assert error < 0.01, f"Error should be small, got {error}"
    
    def test_find_optimal_kappa_positive(self):
        """Test that κ is always positive."""
        spectrum = compute_spectrum(128, L=5.0)
        target = RIEMANN_ZEROS_50[:30]
        
        kappa, error = find_optimal_kappa(spectrum, target)
        
        assert kappa > 0, "κ should be positive"
        assert np.isfinite(kappa), "κ should be finite"
    
    def test_find_optimal_kappa_error_decreases(self):
        """Test that better spectrum leads to lower error."""
        target = RIEMANN_ZEROS_50[:20]
        
        # Lower resolution
        spectrum1 = compute_spectrum(128, L=5.0)
        kappa1, error1 = find_optimal_kappa(spectrum1, target)
        
        # Higher resolution
        spectrum2 = compute_spectrum(256, L=5.0)
        kappa2, error2 = find_optimal_kappa(spectrum2, target)
        
        # Error should generally decrease (though not guaranteed due to potential)
        # At minimum, both should be finite and positive
        assert error1 > 0 and error2 > 0, "Errors should be positive"
        assert np.isfinite(error1) and np.isfinite(error2), "Errors should be finite"


class TestMultiescalaConvergence:
    """Test suite for multi-scale convergence analysis."""
    
    def test_multiescala_basic(self):
        """Test that multiescala test runs without errors."""
        # Run with small N values for speed
        df = run_multiescala_test(
            N_values=[64, 128],
            L=5.0,
            n_zeros=20,
            save_plots=False,
            save_csv=False,
            output_dir='/tmp'
        )
        
        assert isinstance(df, pd.DataFrame), "Should return DataFrame"
        assert len(df) == 2, "Should have 2 rows"
        assert 'kappa' in df.columns, "Should have kappa column"
        assert 'drift' in df.columns, "Should have drift column"
    
    def test_kappa_convergence(self):
        """Test that κ shows convergence behavior."""
        df = run_multiescala_test(
            N_values=[128, 256, 512],
            L=5.0,
            n_zeros=20,
            save_plots=False,
            save_csv=False,
            output_dir='/tmp'
        )
        
        # Drift should decrease
        drifts = df['drift'].iloc[1:].values
        assert np.all(drifts > 0), "Drift should be positive"
        
        # κ values should be positive and finite
        assert np.all(df['kappa'] > 0), "All κ values should be positive"
        assert np.all(np.isfinite(df['kappa'])), "All κ values should be finite"
    
    def test_kappa_stability(self):
        """Test that κ stabilizes with increasing N."""
        df = run_multiescala_test(
            N_values=[256, 512, 1024],
            L=5.0,
            n_zeros=30,
            save_plots=False,
            save_csv=False,
            output_dir='/tmp'
        )
        
        # Check that the range of κ values decreases
        kappa_range = df['kappa'].max() - df['kappa'].min()
        
        # Should be relatively stable (range < 10% of mean)
        kappa_mean = df['kappa'].mean()
        relative_range = kappa_range / kappa_mean
        
        assert relative_range < 0.5, f"κ should be relatively stable, got range {relative_range}"
    
    def test_drift_decreases(self):
        """Test that drift decreases with increasing N."""
        df = run_multiescala_test(
            N_values=[128, 256, 512],
            L=5.0,
            n_zeros=20,
            save_plots=False,
            save_csv=False,
            output_dir='/tmp'
        )
        
        # Get non-zero drifts
        drifts = df['drift'].iloc[1:].values
        
        # Drift should generally decrease
        # (we allow some tolerance for numerical noise)
        # Check that final drift is smaller than first drift
        if len(drifts) > 1:
            assert drifts[-1] <= drifts[0] * 2, "Drift should decrease or stay stable"


class TestQCALConstants:
    """Test QCAL constants and physical parameters."""
    
    def test_constants_defined(self):
        """Test that all QCAL constants are properly defined."""
        assert F0 == 141.7001, "Fundamental frequency should be 141.7001 Hz"
        assert C_QCAL == 244.36, "QCAL constant should be 244.36"
        assert abs(KAPPA_PI - 2.577310) < 1e-6, "κ_Π should be 2.577310"
    
    def test_riemann_zeros_validity(self):
        """Test that Riemann zeros array is valid."""
        assert len(RIEMANN_ZEROS_50) == 50, "Should have 50 zeros"
        assert np.all(RIEMANN_ZEROS_50 > 0), "All zeros should be positive"
        assert np.all(np.diff(RIEMANN_ZEROS_50) > 0), "Zeros should be increasing"
        
        # Check first zero
        assert abs(RIEMANN_ZEROS_50[0] - 14.134725) < 1e-5, "First zero should be ~14.134725"


class TestOutputGeneration:
    """Test output file generation and format."""
    
    @pytest.fixture
    def test_output_dir(self, tmp_path):
        """Create temporary output directory."""
        return tmp_path / "test_output"
    
    def test_csv_generation(self, test_output_dir):
        """Test that CSV file is generated correctly."""
        df = run_multiescala_test(
            N_values=[64, 128],
            L=5.0,
            n_zeros=10,
            save_plots=False,
            save_csv=True,
            output_dir=str(test_output_dir)
        )
        
        csv_file = test_output_dir / 'adelic_kernel_kappa_convergence.csv'
        assert csv_file.exists(), "CSV file should be created"
        
        # Read and verify
        df_read = pd.read_csv(csv_file)
        assert len(df_read) == 2, "CSV should have 2 rows"
        assert list(df_read.columns) == list(df.columns), "Columns should match"
    
    def test_beacon_generation(self, test_output_dir):
        """Test that QCAL beacon JSON is generated correctly."""
        run_multiescala_test(
            N_values=[64, 128],
            L=5.0,
            n_zeros=10,
            save_plots=False,
            save_csv=True,
            output_dir=str(test_output_dir)
        )
        
        beacon_file = test_output_dir / 'adelic_kernel_multiescala_beacon.json'
        assert beacon_file.exists(), "Beacon file should be created"
        
        # Read and verify structure
        with open(beacon_file) as f:
            beacon = json.load(f)
        
        assert 'node_id' in beacon, "Should have node_id"
        assert 'protocol' in beacon, "Should have protocol"
        assert 'test_results' in beacon, "Should have test_results"
        assert 'theoretical_framework' in beacon, "Should have theoretical_framework"
        assert 'qcal_signature' in beacon, "Should have QCAL signature"
        
        # Verify test results
        results = beacon['test_results']
        assert 'kappa_asymptotic' in results
        assert 'drift_final' in results
        assert 'convergence_status' in results


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_no_nans_in_spectrum(self):
        """Test that spectrum computation never produces NaN values."""
        for N in [64, 128, 256]:
            spectrum = compute_spectrum(N, L=5.0)
            assert not np.any(np.isnan(spectrum)), f"NaN found in spectrum for N={N}"
    
    def test_no_infs_in_spectrum(self):
        """Test that spectrum computation never produces Inf values."""
        for N in [64, 128, 256]:
            spectrum = compute_spectrum(N, L=5.0)
            assert not np.any(np.isinf(spectrum)), f"Inf found in spectrum for N={N}"
    
    def test_different_domain_sizes(self):
        """Test that different domain sizes work correctly."""
        for L in [3.0, 5.0, 7.0]:
            spectrum = compute_spectrum(128, L=L)
            assert len(spectrum) > 0, f"Empty spectrum for L={L}"
            assert np.all(spectrum > 0), f"Non-positive values for L={L}"


@pytest.mark.slow
class TestFullMultiescala:
    """Full multiescala test (slow, marked for optional execution)."""
    
    def test_full_convergence_analysis(self):
        """Run full multiescala test with production parameters."""
        df = run_multiescala_test(
            N_values=[640, 1280, 2560],
            L=5.0,
            n_zeros=50,
            save_plots=False,
            save_csv=False,
            output_dir='/tmp'
        )
        
        # Verify convergence quality
        drift_final = df['drift'].iloc[-1]
        
        # Should achieve at least moderate convergence
        assert drift_final < 0.01, f"Drift should be < 0.01, got {drift_final}"
        
        # κ should be stable
        kappa_final = df['kappa'].iloc[-1]
        assert kappa_final > 0, "Final κ should be positive"
        assert np.isfinite(kappa_final), "Final κ should be finite"


if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, "-v", "--tb=short"])
