#!/usr/bin/env python3
"""
Test Suite for Atlas³ Operator

Tests the Atlas³ non-Hermitian operator with PT symmetry,
spectral analysis, and connection to Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from atlas3_operator import (
    Atlas3Operator,
    time_dependent_alpha,
    time_dependent_beta,
    quasiperiodic_potential,
    analyze_gue_statistics,
    weyl_law_analysis,
    gue_wigner_surmise,
    KAPPA_PI,
    F0,
    GOLDEN_RATIO
)


class TestTimeDependentCoefficients:
    """Test time-dependent coefficient functions."""
    
    def test_alpha_constant(self):
        """Test constant alpha(t)."""
        t = np.linspace(0, 10, 100)
        alpha = time_dependent_alpha(t, 'constant')
        
        assert alpha.shape == t.shape
        assert np.allclose(alpha, 1.0)
    
    def test_alpha_sinusoidal(self):
        """Test sinusoidal alpha(t)."""
        t = np.linspace(0, 10, 100)
        alpha = time_dependent_alpha(t, 'sinusoidal')
        
        assert alpha.shape == t.shape
        assert np.all(alpha > 0)  # Should be positive
        assert np.min(alpha) < 1.0 < np.max(alpha)  # Should oscillate around 1
    
    def test_alpha_quasiperiodic(self):
        """Test quasiperiodic alpha(t)."""
        t = np.linspace(0, 10, 100)
        alpha = time_dependent_alpha(t, 'quasiperiodic')
        
        assert alpha.shape == t.shape
        assert np.all(alpha > 0)
    
    def test_beta_constant(self):
        """Test constant beta(t)."""
        t = np.linspace(0, 10, 100)
        beta = time_dependent_beta(t, coupling_strength=1.0, modulation='constant')
        
        assert beta.shape == t.shape
        assert np.allclose(beta, 1.0)
    
    def test_beta_critical(self):
        """Test critical beta(t) at κ_Π."""
        t = np.linspace(0, 10, 100)
        beta = time_dependent_beta(t, coupling_strength=1.0, modulation='critical')
        
        assert beta.shape == t.shape
        assert np.mean(beta) == pytest.approx(KAPPA_PI, rel=0.1)
    
    def test_quasiperiodic_potential(self):
        """Test quasiperiodic potential V(t)."""
        t = np.linspace(0, 10, 100)
        V = quasiperiodic_potential(t, amplitude=1.0, n_frequencies=3)
        
        assert V.shape == t.shape
        # Should be bounded
        assert np.abs(V).max() < 5.0


class TestAtlas3Operator:
    """Test Atlas³ operator construction and diagonalization."""
    
    def test_operator_initialization(self):
        """Test operator initialization."""
        atlas = Atlas3Operator(n_points=64, t_max=5.0)
        
        assert atlas.n_points == 64
        assert atlas.t_max == 5.0
        assert atlas.t.shape == (64,)
        assert atlas.operator.shape == (64, 64)
        assert atlas.operator.dtype == complex
    
    def test_operator_is_complex(self):
        """Test that operator is complex (non-Hermitian)."""
        atlas = Atlas3Operator(n_points=64, beta_coupling=1.0)
        
        # Operator should be complex due to i*beta term
        assert np.any(np.abs(atlas.operator.imag) > 1e-10)
    
    def test_operator_tridiagonal_structure(self):
        """Test tridiagonal structure of operator matrix."""
        atlas = Atlas3Operator(n_points=64)
        
        # Check that only diagonal and off-diagonal elements are non-zero
        for i in range(64):
            for j in range(64):
                if abs(i - j) > 1:
                    assert np.abs(atlas.operator[i, j]) < 1e-10
    
    def test_diagonalization(self):
        """Test operator diagonalization."""
        atlas = Atlas3Operator(n_points=64)
        
        eigenvalues, eigenvectors = atlas.diagonalize()
        
        assert eigenvalues.shape == (64,)
        assert eigenvectors.shape == (64, 64)
        assert atlas._eigenvalues is not None
        assert atlas._eigenvectors is not None
    
    def test_diagonalization_without_eigenvectors(self):
        """Test diagonalization without eigenvectors."""
        atlas = Atlas3Operator(n_points=64)
        
        eigenvalues, eigenvectors = atlas.diagonalize(compute_eigenvectors=False)
        
        assert eigenvalues.shape == (64,)
        assert eigenvectors is None
        assert atlas._eigenvalues is not None


class TestSpectralAnalysis:
    """Test spectral analysis functions."""
    
    def test_analyze_spectrum_basic(self):
        """Test basic spectral analysis."""
        atlas = Atlas3Operator(n_points=64, beta_coupling=0.5)
        atlas.diagonalize(compute_eigenvectors=False)
        
        analysis = atlas.analyze_spectrum()
        
        assert 'eigenvalues' in analysis
        assert 'real_parts' in analysis
        assert 'imag_parts' in analysis
        assert 'is_pt_symmetric' in analysis
        assert 'mean_real_part' in analysis
        assert 'critical_line_deviation' in analysis
    
    def test_pt_symmetry_weak_coupling(self):
        """Test PT symmetry with weak coupling (should be symmetric)."""
        atlas = Atlas3Operator(n_points=64, beta_coupling=0.5)
        atlas.diagonalize(compute_eigenvectors=False)
        
        analysis = atlas.analyze_spectrum()
        
        # Weak coupling should preserve PT symmetry
        assert analysis['max_imaginary_part'] < 1.0
    
    def test_spectral_gaps(self):
        """Test detection of spectral gaps."""
        atlas = Atlas3Operator(
            n_points=64,
            beta_coupling=KAPPA_PI,
            v_amplitude=2.0,
            n_v_frequencies=5
        )
        atlas.diagonalize(compute_eigenvectors=False)
        
        analysis = atlas.analyze_spectrum()
        
        assert 'spectral_gaps' in analysis
        assert 'num_gaps' in analysis
        assert analysis['num_gaps'] >= 0
    
    def test_participation_ratio(self):
        """Test participation ratio computation."""
        atlas = Atlas3Operator(n_points=64)
        atlas.diagonalize(compute_eigenvectors=True)
        
        analysis = atlas.analyze_spectrum()
        
        assert 'participation_ratios' in analysis
        assert 'mean_participation_ratio' in analysis
        
        if len(analysis['participation_ratios']) > 0:
            # PR should be between 1 and N
            prs = np.array(analysis['participation_ratios'])
            assert np.all(prs >= 1.0)
            assert np.all(prs <= atlas.n_points)


class TestAndersonLocalization:
    """Test Anderson localization transition."""
    
    def test_localization_scan(self):
        """Test localization scan over coupling values."""
        atlas = Atlas3Operator(n_points=64)
        
        coupling_values = [0.5, 1.0, 2.0, 3.0]
        results = atlas.check_anderson_localization(coupling_values)
        
        assert 'coupling_values' in results
        assert 'mean_pr' in results
        assert 'localization_length' in results
        assert len(results['mean_pr']) == len(coupling_values)
    
    def test_transition_detection(self):
        """Test detection of localization transition."""
        atlas = Atlas3Operator(n_points=64)
        
        coupling_values = np.linspace(0.5, 5.0, 10)
        results = atlas.check_anderson_localization(coupling_values)
        
        assert 'transition_coupling' in results
        # Transition should be detected
        assert results['transition_coupling'] is not None


class TestGUEStatistics:
    """Test GUE random matrix statistics analysis."""
    
    def test_gue_wigner_surmise(self):
        """Test GUE Wigner surmise function."""
        s = np.linspace(0, 3, 100)
        P = gue_wigner_surmise(s)
        
        assert P.shape == s.shape
        assert np.all(P >= 0)
        # Should peak around s ~ 1
        assert s[np.argmax(P)] > 0.5
        assert s[np.argmax(P)] < 1.5
    
    def test_gue_analysis_basic(self):
        """Test basic GUE statistics analysis."""
        # Generate some random spacings
        np.random.seed(42)
        spacings = np.random.exponential(1.0, 100)
        
        results = analyze_gue_statistics(spacings)
        
        assert 'gue_compatible' in results
        assert 'ks_statistic' in results
        assert 'ks_pvalue' in results
        assert 'mean_spacing' in results
    
    def test_gue_analysis_empty(self):
        """Test GUE analysis with empty array."""
        spacings = np.array([])
        
        results = analyze_gue_statistics(spacings)
        
        assert results['gue_compatible'] is False
        assert results['ks_statistic'] is None


class TestWeylLaw:
    """Test Weyl law analysis."""
    
    def test_weyl_law_basic(self):
        """Test basic Weyl law analysis."""
        # Generate some eigenvalues
        np.random.seed(42)
        real_parts = np.sort(np.random.uniform(0, 10, 100))
        
        results = weyl_law_analysis(real_parts)
        
        assert 'energies' in results
        assert 'N_E' in results
        assert 'weyl_slope' in results
        assert 'oscillatory_part' in results
    
    def test_weyl_law_linear_growth(self):
        """Test Weyl law for linearly growing eigenvalues."""
        # Perfect linear growth
        real_parts = np.linspace(0, 10, 100)
        
        results = weyl_law_analysis(real_parts)
        
        # Should have high R² for linear fit
        assert results['weyl_r_squared'] > 0.99


class TestConstants:
    """Test QCAL constants."""
    
    def test_kappa_pi_value(self):
        """Test κ_Π value."""
        assert KAPPA_PI == pytest.approx(2.5773, rel=1e-4)
    
    def test_f0_value(self):
        """Test fundamental frequency."""
        assert F0 == pytest.approx(141.7001, rel=1e-6)
    
    def test_golden_ratio(self):
        """Test golden ratio value."""
        expected = (1 + np.sqrt(5)) / 2
        assert GOLDEN_RATIO == pytest.approx(expected, rel=1e-10)


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_workflow(self):
        """Test complete Atlas³ analysis workflow."""
        # Create operator
        atlas = Atlas3Operator(
            n_points=128,
            t_max=10.0,
            beta_coupling=1.0
        )
        
        # Diagonalize
        eigenvalues, eigenvectors = atlas.diagonalize()
        
        # Analyze spectrum
        analysis = atlas.analyze_spectrum()
        
        # Check basic properties
        assert len(eigenvalues) == 128
        assert analysis['mean_real_part'] is not None
        assert analysis['is_pt_symmetric'] in [True, False]
        
        # GUE analysis
        if len(analysis['normalized_spacings']) > 0:
            gue_results = analyze_gue_statistics(analysis['normalized_spacings'])
            assert gue_results['mean_spacing'] is not None
        
        # Weyl law
        weyl_results = weyl_law_analysis(analysis['real_parts'])
        assert weyl_results['weyl_slope'] is not None
    
    def test_reproducibility(self):
        """Test reproducibility of results."""
        # Same parameters should give same results
        atlas1 = Atlas3Operator(n_points=64, t_max=5.0, beta_coupling=1.0)
        atlas2 = Atlas3Operator(n_points=64, t_max=5.0, beta_coupling=1.0)
        
        evals1, _ = atlas1.diagonalize(compute_eigenvectors=False)
        evals2, _ = atlas2.diagonalize(compute_eigenvectors=False)
        
        # Sort eigenvalues
        evals1_sorted = np.sort(evals1.real)
        evals2_sorted = np.sort(evals2.real)
        
        # Should be identical
        assert np.allclose(evals1_sorted, evals2_sorted, rtol=1e-10)


if __name__ == '__main__':
    # Run tests
    pytest.main([__file__, '-v'])
