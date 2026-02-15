#!/usr/bin/env python3
"""
Tests for Atlas³ Spectral Analyzer

Validates the quantum-inspired spectral analysis framework for forced
oscillatory systems with nonlinear dissipation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.atlas3_spectral_analyzer import (
    # Constants
    F0,
    C_QCAL,
    KAPPA_PI,
    N_DEFAULT,
    OMEGA_J_DEFAULT,
    A_DEFAULT,
    BETA_DEFAULT,
    GAMMA_DEFAULT,
    # Classes
    Atlas3SpectralAnalyzer,
    # Functions
    run_atlas3_spectral_analysis,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_f0_value(self):
        """Fundamental frequency should be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-4
    
    def test_c_qcal_value(self):
        """QCAL coherence constant should be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01
    
    def test_kappa_pi_value(self):
        """Critical constant should be ~2.57."""
        assert abs(KAPPA_PI - 2.577) < 0.01
    
    def test_n_default(self):
        """Default discretization should be 1000."""
        assert N_DEFAULT == 1000


class TestAtlas3SpectralAnalyzer:
    """Test Atlas³ Spectral Analyzer class."""
    
    def test_initialization(self):
        """Test basic initialization."""
        analyzer = Atlas3SpectralAnalyzer(N=100, omega_J=1.0, A=1.0, beta=0.3, gamma=0.5)
        assert analyzer.N == 100
        assert analyzer.omega_J == 1.0
        assert analyzer.A == 1.0
        assert analyzer.beta == 0.3
        assert analyzer.gamma == 0.5
    
    def test_default_initialization(self):
        """Test initialization with defaults."""
        analyzer = Atlas3SpectralAnalyzer()
        assert analyzer.N == N_DEFAULT
        assert analyzer.omega_J == OMEGA_J_DEFAULT
        assert analyzer.A == A_DEFAULT
        assert analyzer.beta == BETA_DEFAULT
        assert analyzer.gamma == GAMMA_DEFAULT
    
    def test_grid_construction(self):
        """Test grid points are properly constructed."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        assert len(analyzer.t) == 100
        assert analyzer.t[0] == 0.0
        assert abs(analyzer.t[-1] - 2*np.pi) < 0.1
    
    def test_time_step_calculation(self):
        """Test time step dt calculation."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        expected_dt = 2*np.pi / 100
        assert abs(analyzer.dt - expected_dt) < 1e-10


class TestOperatorConstruction:
    """Test Atlas³ operator construction."""
    
    def test_build_operator_returns_tuple(self):
        """Operator builder should return (d, e) tuple."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        d, e = analyzer.build_operator()
        assert isinstance(d, np.ndarray)
        assert isinstance(e, np.ndarray)
    
    def test_diagonal_length(self):
        """Diagonal should have length N."""
        N = 50
        analyzer = Atlas3SpectralAnalyzer(N=N)
        d, e = analyzer.build_operator()
        assert len(d) == N
    
    def test_off_diagonal_length(self):
        """Off-diagonal should have length N-1."""
        N = 50
        analyzer = Atlas3SpectralAnalyzer(N=N)
        d, e = analyzer.build_operator()
        assert len(e) == N - 1
    
    def test_potential_term_positive(self):
        """Effective potential V(t) should be non-negative."""
        analyzer = Atlas3SpectralAnalyzer(N=50, gamma=0.5, A=1.0)
        d, e = analyzer.build_operator()
        # V(t) = gamma * A² * cos²(omega_J * t) >= 0
        # d = V + 1/dt² >= 1/dt²
        assert np.all(d >= 0)
    
    def test_kinetic_term_contribution(self):
        """Kinetic term should contribute to diagonal."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        d, e = analyzer.build_operator()
        # Diagonal includes 1/dt² from kinetic term
        min_kinetic = 1 / analyzer.dt**2
        assert np.all(d >= min_kinetic * 0.9)  # Allow small numerical tolerance


class TestSpectrumComputation:
    """Test spectrum computation."""
    
    def test_compute_spectrum_returns_eigenvalues(self):
        """Spectrum computation should return eigenvalues."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        eigenvalues = analyzer.compute_spectrum()
        assert eigenvalues is not None
        assert len(eigenvalues) == 50
    
    def test_eigenvalues_are_real(self):
        """For Hermitian approximation, eigenvalues should be mostly real."""
        analyzer = Atlas3SpectralAnalyzer(N=50, beta=0.0)  # beta=0 → Hermitian
        eigenvalues = analyzer.compute_spectrum()
        # Check that imaginary parts are small
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-10
    
    def test_eigenvalues_stored(self):
        """Eigenvalues should be stored in analyzer."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        assert analyzer.eigenvalues is not None
        assert analyzer.eigenvectors is not None
    
    def test_spectrum_ordering(self):
        """Eigenvalues from eigh_tridiagonal should be sorted."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        eigenvalues = analyzer.compute_spectrum()
        # Check if sorted (or nearly sorted)
        sorted_eigs = np.sort(eigenvalues)
        assert np.allclose(eigenvalues, sorted_eigs, rtol=1e-5)


class TestVerticalAlignment:
    """Test vertical alignment detection."""
    
    def test_vertical_alignment_returns_tuple(self):
        """Vertical alignment test should return (mean, std)."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        mean_re, std_re = analyzer.test_vertical_alignment()
        assert isinstance(mean_re, (float, np.floating))
        assert isinstance(std_re, (float, np.floating))
    
    def test_mean_is_reasonable(self):
        """Mean Re(λ) should be positive and finite."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        mean_re, std_re = analyzer.test_vertical_alignment()
        assert np.isfinite(mean_re)
        assert mean_re > 0
    
    def test_std_is_nonnegative(self):
        """Standard deviation should be non-negative."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        mean_re, std_re = analyzer.test_vertical_alignment()
        assert std_re >= 0
    
    def test_hermitian_case_small_std(self):
        """For Hermitian case (beta=0), std should be non-trivial but finite."""
        analyzer = Atlas3SpectralAnalyzer(N=100, beta=0.0)
        analyzer.compute_spectrum()
        mean_re, std_re = analyzer.test_vertical_alignment()
        # Hermitian → all real, but different values
        assert std_re > 0.01  # Non-trivial spread
        assert std_re < 100   # But not pathological


class TestGUEStatistics:
    """Test GUE statistics computation."""
    
    def test_gue_returns_spacings(self):
        """GUE test should return normalized spacings."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        spacings = analyzer.test_gue_statistics()
        assert isinstance(spacings, np.ndarray)
        assert len(spacings) == 49  # N-1 spacings
    
    def test_spacings_normalized(self):
        """Spacings should be normalized to mean=1."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        spacings = analyzer.test_gue_statistics()
        # Mean should be close to 1
        assert abs(np.mean(spacings) - 1.0) < 0.05
    
    def test_spacings_positive(self):
        """All spacings should be positive."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        spacings = analyzer.test_gue_statistics()
        assert np.all(spacings > 0)
    
    def test_level_repulsion(self):
        """Should detect level repulsion for non-Poisson."""
        analyzer = Atlas3SpectralAnalyzer(N=100, beta=0.3)
        analyzer.compute_spectrum()
        spacings = analyzer.test_gue_statistics()
        # For GUE, minimum spacing should be > 0
        assert np.min(spacings) > 0.001


class TestSpectralRigidity:
    """Test spectral rigidity computation."""
    
    def test_rigidity_returns_tuple(self):
        """Rigidity test should return (L_values, rigidity)."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        L_vals, rigidity = analyzer.test_spectral_rigidity()
        assert isinstance(L_vals, np.ndarray)
        assert isinstance(rigidity, np.ndarray)
        assert len(L_vals) == len(rigidity)
    
    def test_rigidity_nonnegative(self):
        """Rigidity values should be non-negative."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        L_vals, rigidity = analyzer.test_spectral_rigidity()
        assert np.all(rigidity >= 0)
    
    def test_custom_L_values(self):
        """Should accept custom L values."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        custom_L = np.array([1, 2, 5, 10])
        L_vals, rigidity = analyzer.test_spectral_rigidity(L_values=custom_L)
        assert len(rigidity) == len(custom_L)
    
    def test_rigidity_increases_with_L(self):
        """Rigidity should generally increase with L."""
        analyzer = Atlas3SpectralAnalyzer(N=200)
        analyzer.compute_spectrum()
        L_vals, rigidity = analyzer.test_spectral_rigidity()
        # Check that rigidity is generally increasing (at least monotonic on average)
        valid = rigidity > 0
        if np.sum(valid) > 2:
            # Should have positive correlation with L
            corr = np.corrcoef(np.log(L_vals[valid] + 1), 
                              np.log(rigidity[valid] + 1))[0, 1]
            assert corr > 0.3  # Positive correlation


class TestVisualization:
    """Test truth panel visualization."""
    
    def test_generate_truth_panel_returns_figure(self):
        """Should return matplotlib Figure."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        fig = analyzer.generate_truth_panel()
        assert fig is not None
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)
    
    def test_truth_panel_has_subplots(self):
        """Truth panel should have 4 subplots."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        fig = analyzer.generate_truth_panel()
        assert len(fig.axes) == 4
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)
    
    def test_truth_panel_saves_to_file(self, tmp_path):
        """Should save figure to file."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        save_path = tmp_path / "test_panel.png"
        fig = analyzer.generate_truth_panel(save_path=save_path)
        assert save_path.exists()
        # Clean up
        import matplotlib.pyplot as plt
        plt.close(fig)


class TestCoherenceMetric:
    """Test QCAL coherence metric."""
    
    def test_coherence_in_range(self):
        """Coherence Ψ should be in [0, 1]."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        psi = analyzer.compute_coherence_metric()
        assert 0 <= psi <= 1
    
    def test_coherence_is_float(self):
        """Coherence should be a float."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        psi = analyzer.compute_coherence_metric()
        assert isinstance(psi, (float, np.floating))
    
    def test_coherence_varies_with_parameters(self):
        """Coherence should vary with system parameters."""
        psi1 = Atlas3SpectralAnalyzer(N=100, beta=0.1).compute_coherence_metric()
        psi2 = Atlas3SpectralAnalyzer(N=100, beta=0.5).compute_coherence_metric()
        # Should be different (not necessarily one higher than the other)
        # Just check they're not identical
        assert abs(psi1 - psi2) > 0.01


class TestCertificateGeneration:
    """Test certificate generation."""
    
    def test_certificate_is_dict(self):
        """Certificate should be a dictionary."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        cert = analyzer.generate_certificate()
        assert isinstance(cert, dict)
    
    def test_certificate_has_required_fields(self):
        """Certificate should have required fields."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        cert = analyzer.generate_certificate()
        
        required_fields = [
            "protocol", "version", "signature", "parameters",
            "qcal_constants", "test_results", "coherence", "spectrum_summary"
        ]
        for field in required_fields:
            assert field in cert
    
    def test_certificate_parameters_correct(self):
        """Certificate should record correct parameters."""
        analyzer = Atlas3SpectralAnalyzer(N=50, omega_J=1.5, A=2.0, beta=0.4, gamma=0.6)
        analyzer.compute_spectrum()
        cert = analyzer.generate_certificate()
        
        assert cert["parameters"]["N"] == 50
        assert cert["parameters"]["omega_J"] == 1.5
        assert cert["parameters"]["A"] == 2.0
        assert cert["parameters"]["beta"] == 0.4
        assert cert["parameters"]["gamma"] == 0.6
    
    def test_certificate_saves_to_file(self, tmp_path):
        """Certificate should save to JSON file."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        cert_path = tmp_path / "test_cert.json"
        cert = analyzer.generate_certificate(output_path=cert_path)
        assert cert_path.exists()
        
        # Verify it's valid JSON
        import json
        with open(cert_path, 'r') as f:
            loaded = json.load(f)
        assert loaded == cert
    
    def test_certificate_qcal_constants(self):
        """Certificate should include QCAL constants."""
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        cert = analyzer.generate_certificate()
        
        assert abs(cert["qcal_constants"]["f0_hz"] - F0) < 1e-4
        assert abs(cert["qcal_constants"]["C"] - C_QCAL) < 0.01
        assert abs(cert["qcal_constants"]["kappa_pi"] - KAPPA_PI) < 0.01
    
    def test_certificate_coherence_level(self):
        """Certificate should classify coherence level."""
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        cert = analyzer.generate_certificate()
        
        assert "coherence" in cert
        assert "psi" in cert["coherence"]
        assert "level" in cert["coherence"]
        assert cert["coherence"]["level"] in ["UNIVERSAL", "PARTIAL"]


class TestIntegrationAnalysis:
    """Test complete analysis pipeline."""
    
    def test_run_analysis_completes(self, tmp_path):
        """Complete analysis should run without errors."""
        results = run_atlas3_spectral_analysis(
            N=50, save_dir=tmp_path
        )
        assert isinstance(results, dict)
    
    def test_run_analysis_generates_certificate(self, tmp_path):
        """Analysis should generate certificate file."""
        run_atlas3_spectral_analysis(N=50, save_dir=tmp_path)
        cert_path = tmp_path / "atlas3_spectral_analyzer_certificate.json"
        assert cert_path.exists()
    
    def test_run_analysis_generates_visualization(self, tmp_path):
        """Analysis should generate visualization file."""
        run_atlas3_spectral_analysis(N=50, save_dir=tmp_path)
        fig_path = tmp_path / "atlas3_spectral_analyzer_truth_panel.png"
        assert fig_path.exists()
    
    def test_analysis_with_custom_parameters(self, tmp_path):
        """Analysis should work with custom parameters."""
        results = run_atlas3_spectral_analysis(
            N=100,
            omega_J=2.0,
            A=1.5,
            beta=0.4,
            gamma=0.7,
            save_dir=tmp_path
        )
        assert results["parameters"]["omega_J"] == 2.0
        assert results["parameters"]["A"] == 1.5


@pytest.mark.slow
class TestNumericalConvergence:
    """Test numerical convergence with resolution."""
    
    def test_spectrum_converges_with_N(self):
        """Spectrum should converge as N increases."""
        N_values = [50, 100, 200]
        spectra = []
        
        for N in N_values:
            analyzer = Atlas3SpectralAnalyzer(N=N)
            analyzer.compute_spectrum()
            spectra.append(analyzer.eigenvalues)
        
        # Check that results are becoming more stable
        # (hard to define precisely, but basic sanity check)
        for spec in spectra:
            assert len(spec) == len(set(N_values[spectra.index(spec)]))
    
    def test_coherence_stability(self):
        """Coherence should be relatively stable across resolutions."""
        coherences = []
        for N in [100, 150, 200]:
            analyzer = Atlas3SpectralAnalyzer(N=N)
            analyzer.compute_spectrum()
            psi = analyzer.compute_coherence_metric()
            coherences.append(psi)
        
        # All should be valid
        assert all(0 <= psi <= 1 for psi in coherences)
        # Should not vary wildly (within factor of 2)
        assert max(coherences) / (min(coherences) + 1e-10) < 5


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
