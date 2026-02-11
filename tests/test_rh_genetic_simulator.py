"""
Tests for RH Genetic Simulator Module
======================================

Tests the biological-spectral genetic operator and codon simulation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-02-11
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from biological.rh_genetic_simulator import (
    simulate_codon_waveform,
    compute_coherence,
    get_codon_frequencies,
    compare_biological_rhythms,
    plot_codon_waveform,
    plot_spectral_comparison,
    load_extended_riemann_zeros,
    RIEMANN_ZEROS,
    CODON_DATABASE,
    F0_HZ,
    DELTA_ZETA_HZ,
    EEG_ALPHA_HZ,
)


class TestCodonDatabase:
    """Test codon database integrity."""
    
    def test_codon_count(self):
        """Verify we have standard 64 codons."""
        # Standard genetic code has 64 codons (4³)
        assert len(CODON_DATABASE) == 64, \
            f"Expected 64 codons, got {len(CODON_DATABASE)}"
    
    def test_start_codon_exists(self):
        """Verify start codon AUG exists."""
        assert "AUG" in CODON_DATABASE, "Start codon AUG not found"
    
    def test_stop_codons_exist(self):
        """Verify stop codons exist."""
        stop_codons = ["UAA", "UAG", "UGA"]
        for codon in stop_codons:
            assert codon in CODON_DATABASE, f"Stop codon {codon} not found"
    
    def test_codon_indices_valid(self):
        """Verify all codon indices are within valid range."""
        n_zeros = len(RIEMANN_ZEROS)
        for codon, (idx1, idx2, idx3) in CODON_DATABASE.items():
            assert 0 <= idx1 < n_zeros, \
                f"Codon {codon} has invalid index1: {idx1}"
            assert 0 <= idx2 < n_zeros, \
                f"Codon {codon} has invalid index2: {idx2}"
            assert 0 <= idx3 < n_zeros, \
                f"Codon {codon} has invalid index3: {idx3}"


class TestRiemannZeros:
    """Test Riemann zeros data."""
    
    def test_riemann_zeros_shape(self):
        """Verify Riemann zeros array has correct shape."""
        assert RIEMANN_ZEROS.shape == (30,), \
            f"Expected 30 zeros, got {RIEMANN_ZEROS.shape}"
    
    def test_riemann_zeros_sorted(self):
        """Verify zeros are in ascending order."""
        assert np.all(RIEMANN_ZEROS[:-1] <= RIEMANN_ZEROS[1:]), \
            "Riemann zeros are not sorted"
    
    def test_riemann_zeros_positive(self):
        """Verify all zeros are positive."""
        assert np.all(RIEMANN_ZEROS > 0), \
            "Some Riemann zeros are not positive"
    
    def test_first_zero_value(self):
        """Verify first zero is approximately 14.134725."""
        expected_gamma1 = 14.1347251417
        assert abs(RIEMANN_ZEROS[0] - expected_gamma1) < 1e-6, \
            f"First zero mismatch: {RIEMANN_ZEROS[0]} vs {expected_gamma1}"
    
    def test_load_extended_zeros(self):
        """Test loading extended zeros from file."""
        try:
            zeros = load_extended_riemann_zeros(n_zeros=50)
            assert len(zeros) >= 30, "Should load at least 30 zeros"
            assert np.all(zeros[:-1] <= zeros[1:]), "Loaded zeros not sorted"
        except FileNotFoundError:
            # OK if file not found, will use hardcoded
            pytest.skip("Zeros file not found, using hardcoded values")


class TestCodonWaveform:
    """Test codon waveform simulation."""
    
    def test_simulate_aug_waveform(self):
        """Test AUG (start codon) waveform simulation."""
        t = np.linspace(0, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        assert waveform.shape == t.shape, "Waveform shape mismatch"
        assert np.iscomplexobj(waveform), "Waveform should be complex"
        assert np.all(np.isfinite(waveform)), "Waveform has non-finite values"
    
    def test_simulate_all_codons(self):
        """Test that all codons can be simulated."""
        t = np.linspace(0, 0.05, 50)
        
        for codon in CODON_DATABASE.keys():
            waveform = simulate_codon_waveform(codon, t)
            assert waveform.shape == t.shape, \
                f"Shape mismatch for codon {codon}"
            assert np.iscomplexobj(waveform), \
                f"Waveform not complex for codon {codon}"
    
    def test_invalid_codon_raises_error(self):
        """Test that invalid codon raises ValueError."""
        t = np.linspace(0, 0.1, 100)
        
        with pytest.raises(ValueError, match="no reconocido"):
            simulate_codon_waveform("XYZ", t)
    
    def test_custom_amplitudes(self):
        """Test waveform with custom amplitudes."""
        t = np.linspace(0, 0.1, 100)
        custom_amps = np.array([2.0, 1.5, 1.0])
        
        waveform = simulate_codon_waveform("AUG", t, amplitudes=custom_amps)
        
        assert waveform.shape == t.shape
        assert np.iscomplexobj(waveform)
    
    def test_waveform_periodicity(self):
        """Test that waveform has expected periodicity."""
        # Create long enough time series to see periodicity
        t = np.linspace(0, 1.0, 1000)
        waveform = simulate_codon_waveform("AUG", t)
        
        # Magnitude should oscillate
        magnitude = np.abs(waveform)
        assert magnitude.max() > magnitude.min(), \
            "Waveform magnitude should vary"


class TestCoherenceMeasure:
    """Test coherence computation."""
    
    def test_coherence_positive(self):
        """Test that coherence is always positive."""
        t = np.linspace(0, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        coherence = compute_coherence(waveform)
        assert coherence >= 0, "Coherence should be non-negative"
    
    def test_coherence_finite(self):
        """Test that coherence is finite."""
        t = np.linspace(0, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        coherence = compute_coherence(waveform)
        assert np.isfinite(coherence), "Coherence should be finite"
    
    def test_coherence_with_reference(self):
        """Test cross-coherence with reference waveform."""
        t = np.linspace(0, 0.1, 100)
        waveform1 = simulate_codon_waveform("AUG", t)
        waveform2 = simulate_codon_waveform("UUU", t)
        
        coherence = compute_coherence(waveform1, waveform2)
        assert 0 <= coherence <= 1.5, "Cross-coherence out of expected range"
    
    def test_self_coherence(self):
        """Test that self-coherence is maximal."""
        t = np.linspace(0, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        # Self-coherence should be high
        self_coh = compute_coherence(waveform, waveform)
        auto_coh = compute_coherence(waveform)
        
        # Both should be positive
        assert self_coh > 0
        assert auto_coh > 0


class TestFrequencyMapping:
    """Test frequency mapping functions."""
    
    def test_get_codon_frequencies_aug(self):
        """Test getting frequencies for AUG."""
        freqs = get_codon_frequencies("AUG")
        
        assert len(freqs) == 3, "Should return 3 frequencies"
        assert all(f > 0 for f in freqs), "All frequencies should be positive"
        assert all(np.isfinite(f) for f in freqs), "All frequencies should be finite"
    
    def test_get_codon_frequencies_invalid(self):
        """Test that invalid codon raises error."""
        with pytest.raises(ValueError, match="no reconocido"):
            get_codon_frequencies("XYZ")
    
    def test_frequencies_match_zeros(self):
        """Test that returned frequencies match Riemann zeros."""
        freqs = get_codon_frequencies("AUG")
        
        # Each frequency should be one of the Riemann zeros
        for freq in freqs:
            assert freq in RIEMANN_ZEROS, \
                f"Frequency {freq} not in Riemann zeros"


class TestBiologicalRhythms:
    """Test biological rhythm comparisons."""
    
    def test_compare_biological_rhythms(self):
        """Test biological rhythm comparison function."""
        rhythms = compare_biological_rhythms()
        
        assert 'f0_base_hz' in rhythms
        assert 'eeg_alpha_hz' in rhythms
        assert 'respiration_hz' in rhythms
        assert 'delta_zeta_hz' in rhythms
    
    def test_eeg_alpha_ratio(self):
        """Test EEG alpha frequency ratio."""
        rhythms = compare_biological_rhythms()
        
        # EEG alpha should be approximately f₀/14
        theoretical = rhythms['eeg_alpha_theoretical']
        observed = rhythms['eeg_alpha_hz']
        
        # Should be within 10% of theoretical
        ratio = observed / theoretical
        assert 0.9 <= ratio <= 1.1, \
            f"EEG alpha ratio {ratio} out of expected range"
    
    def test_delta_zeta_value(self):
        """Test delta zeta quantum phase shift value."""
        rhythms = compare_biological_rhythms()
        
        # δζ ≈ 0.2787437627 Hz
        assert abs(rhythms['delta_zeta_hz'] - 0.2787437627) < 1e-6, \
            "Delta zeta value mismatch"
    
    def test_f0_value(self):
        """Test fundamental frequency value."""
        rhythms = compare_biological_rhythms()
        
        # f₀ = 141.7001 Hz
        assert abs(rhythms['f0_base_hz'] - 141.7001) < 1e-4, \
            "Fundamental frequency mismatch"


class TestVisualization:
    """Test visualization functions."""
    
    def test_plot_codon_waveform(self, tmp_path):
        """Test single codon waveform plotting."""
        t = np.linspace(0, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        output_file = tmp_path / "test_aug.png"
        plot_codon_waveform(t, waveform, "AUG", save_path=str(output_file))
        
        assert output_file.exists(), "Plot file was not created"
        assert output_file.stat().st_size > 0, "Plot file is empty"
    
    def test_plot_spectral_comparison(self, tmp_path):
        """Test multi-codon spectral comparison plotting."""
        t = np.linspace(0, 0.1, 100)
        codons = ["AUG", "UUU", "UAA"]
        
        output_file = tmp_path / "test_comparison.png"
        plot_spectral_comparison(codons, t, save_path=str(output_file))
        
        assert output_file.exists(), "Comparison plot was not created"
        assert output_file.stat().st_size > 0, "Comparison plot is empty"


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are defined."""
        assert F0_HZ == 141.7001, "F0 constant mismatch"
        assert abs(DELTA_ZETA_HZ - 0.2787437627) < 1e-6, \
            "Delta zeta constant mismatch"
    
    def test_coherence_c_integration(self):
        """Test coherence constant integration."""
        from biological.rh_genetic_simulator import COHERENCE_C
        
        # C = 244.36 (QCAL coherence)
        assert abs(COHERENCE_C - 244.36) < 1e-2, \
            "Coherence constant mismatch"
    
    def test_gamma_1_relationship(self):
        """Test relationship between γ₁ and f₀."""
        rhythms = compare_biological_rhythms()
        
        # γ₁ / f₀ ≈ 0.0998
        ratio = rhythms['gamma_1_vs_f0']
        assert 0.095 <= ratio <= 0.105, \
            f"γ₁/f₀ ratio {ratio} out of expected range"


class TestEdgeCases:
    """Test edge cases and error handling."""
    
    def test_zero_time_array(self):
        """Test with single time point."""
        t = np.array([0.0])
        waveform = simulate_codon_waveform("AUG", t)
        
        assert waveform.shape == (1,)
        assert np.isfinite(waveform[0])
    
    def test_large_time_array(self):
        """Test with large time array."""
        t = np.linspace(0, 10.0, 10000)
        waveform = simulate_codon_waveform("AUG", t)
        
        assert waveform.shape == (10000,)
        assert np.all(np.isfinite(waveform))
    
    def test_negative_time(self):
        """Test with negative time values."""
        t = np.linspace(-0.1, 0.1, 100)
        waveform = simulate_codon_waveform("AUG", t)
        
        # Should still work (complex exponentials defined for all t)
        assert waveform.shape == t.shape
        assert np.all(np.isfinite(waveform))


@pytest.mark.slow
class TestPerformance:
    """Performance tests (marked as slow)."""
    
    def test_simulate_all_codons_performance(self):
        """Test that simulating all codons completes in reasonable time."""
        import time
        
        t = np.linspace(0, 0.1, 1000)
        
        start_time = time.time()
        for codon in CODON_DATABASE.keys():
            simulate_codon_waveform(codon, t)
        elapsed = time.time() - start_time
        
        # Should complete in less than 5 seconds
        assert elapsed < 5.0, \
            f"Simulating all codons took {elapsed:.2f}s (expected < 5s)"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
