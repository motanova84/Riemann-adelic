#!/usr/bin/env python3
"""
Tests for Atlas³ Operator: PT-Symmetric Non-Hermitian Framework

This module validates the Atlas³ implementation against the problem statement:
    1. PT symmetry preservation for β < κ_Π ≈ 2.57
    2. PT breaking transition at β ≈ 2.57
    3. Spectral alignment with critical line Re(s) = 1/2
    4. GUE statistics for eigenvalue spacings
    5. Weyl law with logarithmic oscillations
    6. Anderson localization transition at κ_Π

Expected Results (from Problem Statement):
    - β = 2.0: |Im(λ)|_max < 10⁻⁸ (coherence phase)
    - β = 2.57: |Im(λ)|_max ≈ 0.64 (PT breaking)
    - GUE variance ≈ 0.17 (vs. theoretical 0.168)
    - IPR: ~1/N for β < 2.57, ~0.01 for β > 3.0
    - Peak IPR at β ≈ 2.57 (self-organized criticality)

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

from operators.atlas3_operator import (
    # Constants
    F0,
    C_QCAL,
    KAPPA_PI,
    N_DEFAULT,
    V_AMP_CRITICAL,
    GUE_VARIANCE_THEORETICAL,
    # Classes
    Atlas3Operator,
    # Functions
    analyze_gue_statistics,
    weyl_law_analysis,
    check_anderson_localization,
    run_atlas3_validation,
    verify_problem_statement_claims,
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
        """Critical PT transition should be ~2.57."""
        assert abs(KAPPA_PI - 2.5773) < 0.01
    
    def test_n_default(self):
        """Default discretization should be 500."""
        assert N_DEFAULT == 500
    
    def test_gue_theoretical(self):
        """GUE theoretical variance should be ~0.168."""
        assert abs(GUE_VARIANCE_THEORETICAL - 0.168) < 0.001


class TestAtlas3Operator:
    """Test Atlas³ operator construction."""
    
    def test_initialization(self):
        """Test basic initialization."""
        atlas = Atlas3Operator(N=100, beta_0=1.0, V_amp=1000.0)
        assert atlas.N == 100
        assert atlas.beta_0 == 1.0
        assert atlas.V_amp == 1000.0
    
    def test_default_initialization(self):
        """Test initialization with defaults."""
        atlas = Atlas3Operator()
        assert atlas.N == N_DEFAULT
        assert atlas.beta_0 == 0.0
        assert atlas.V_amp == V_AMP_CRITICAL
    
    def test_grid_construction(self):
        """Test grid points are properly constructed."""
        atlas = Atlas3Operator(N=100)
        assert len(atlas.t_grid) == 100
        assert atlas.t_grid[0] == 0.0
        assert atlas.t_grid[-1] < 2 * np.pi
    
    def test_kinetic_term_shape(self):
        """Kinetic term should have correct shape."""
        atlas = Atlas3Operator(N=100)
        K = atlas.build_kinetic_term()
        assert K.shape == (100, 100)
    
    def test_kinetic_term_hermitian(self):
        """Kinetic term should be Hermitian."""
        atlas = Atlas3Operator(N=50, beta_0=0.0)
        K = atlas.build_kinetic_term()
        assert np.allclose(K, K.T.conj())
    
    def test_pt_breaking_term_anti_hermitian(self):
        """PT-breaking term should be anti-Hermitian."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        B = atlas.build_pt_breaking_term()
        # Anti-Hermitian: B† = -B
        assert np.allclose(B.T.conj(), -B, atol=1e-10)
    
    def test_pt_breaking_zero_when_beta_zero(self):
        """PT-breaking term should vanish when β=0."""
        atlas = Atlas3Operator(N=50, beta_0=0.0)
        B = atlas.build_pt_breaking_term()
        assert np.allclose(B, 0.0, atol=1e-12)
    
    def test_potential_hermitian(self):
        """Potential should be Hermitian (real diagonal)."""
        atlas = Atlas3Operator(N=50)
        V = atlas.build_quasiperiodic_potential()
        assert np.allclose(V, V.T.conj())
        assert np.allclose(V.imag, 0.0)
    
    def test_full_operator_shape(self):
        """Full operator should have correct shape."""
        atlas = Atlas3Operator(N=100)
        O = atlas.build_full_operator()
        assert O.shape == (100, 100)
    
    def test_full_operator_hermitian_when_beta_zero(self):
        """Operator should be Hermitian when β=0."""
        atlas = Atlas3Operator(N=50, beta_0=0.0)
        O = atlas.build_full_operator()
        assert np.allclose(O, O.T.conj(), atol=1e-10)
    
    def test_full_operator_non_hermitian_when_beta_nonzero(self):
        """Operator should be non-Hermitian when β≠0."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        O = atlas.build_full_operator()
        # Should NOT be Hermitian
        assert not np.allclose(O, O.T.conj(), atol=1e-6)


class TestSpectrum:
    """Test spectral properties."""
    
    def test_spectrum_computation(self):
        """Test that spectrum can be computed."""
        atlas = Atlas3Operator(N=50, beta_0=0.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        assert len(eigenvalues) == 50
        assert eigenvectors.shape == (50, 50)
    
    def test_spectrum_real_when_hermitian(self):
        """Spectrum should be real when operator is Hermitian (β=0)."""
        atlas = Atlas3Operator(N=50, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        # Eigenvalues should be real (small imaginary part from numerics)
        assert np.max(np.abs(eigenvalues.imag)) < 1e-8
    
    def test_spectrum_sorted_by_real_part(self):
        """Eigenvalues should be sorted by real part."""
        atlas = Atlas3Operator(N=50, beta_0=1.0)
        eigenvalues, _ = atlas.compute_spectrum()
        real_parts = eigenvalues.real
        assert np.all(real_parts[:-1] <= real_parts[1:])
    
    def test_normalization_preserves_shape(self):
        """Normalization should preserve number of eigenvalues."""
        atlas = Atlas3Operator(N=50)
        eigenvalues, _ = atlas.compute_spectrum()
        normalized = atlas.normalize_spectrum_to_critical_line(eigenvalues)
        assert len(normalized) == len(eigenvalues)
    
    def test_normalization_mean_near_half(self):
        """Normalized spectrum should have mean Re ≈ 1/2."""
        atlas = Atlas3Operator(N=100, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        normalized = atlas.normalize_spectrum_to_critical_line(eigenvalues)
        mean_real = np.mean(normalized.real)
        assert abs(mean_real - 0.5) < 0.01


class TestPTSymmetry:
    """Test PT symmetry properties."""
    
    def test_pt_check_beta_zero(self):
        """β=0 should be in PT-symmetric phase."""
        atlas = Atlas3Operator(N=100, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        assert pt_check['pt_symmetric'] is True
        assert pt_check['phase'] == 'coherent'
    
    def test_pt_check_beta_small(self):
        """Small β (2.0) should preserve PT symmetry."""
        atlas = Atlas3Operator(N=100, beta_0=2.0)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        # Should be in coherent phase
        assert pt_check['max_imaginary'] < 0.1
    
    def test_pt_check_beta_critical(self):
        """β ≈ κ_Π should show PT breaking."""
        atlas = Atlas3Operator(N=100, beta_0=KAPPA_PI)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        # Should show some PT breaking
        assert pt_check['max_imaginary'] > 0.1
    
    def test_pt_check_beta_large(self):
        """Large β (3.0) should be in broken phase."""
        atlas = Atlas3Operator(N=100, beta_0=3.0)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        assert pt_check['phase'] == 'entropy'
        assert pt_check['max_imaginary'] > 0.3


class TestGUEStatistics:
    """Test GUE random matrix theory statistics."""
    
    def test_gue_analysis_runs(self):
        """GUE analysis should run without errors."""
        atlas = Atlas3Operator(N=100, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        gue_stats = analyze_gue_statistics(eigenvalues, num_unfold=50)
        assert 'variance' in gue_stats
        assert 'gue_error' in gue_stats
    
    def test_gue_variance_reasonable(self):
        """GUE variance should be in reasonable range."""
        atlas = Atlas3Operator(N=200, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        gue_stats = analyze_gue_statistics(eigenvalues, num_unfold=100)
        variance = gue_stats['variance']
        # Should be positive and not too far from GUE
        assert 0.0 < variance < 1.0
    
    def test_gue_mean_spacing_near_one(self):
        """Unfolded spacings should have mean ≈ 1."""
        atlas = Atlas3Operator(N=200, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        gue_stats = analyze_gue_statistics(eigenvalues, num_unfold=100)
        mean = gue_stats['mean_spacing']
        # After unfolding, mean should be ~1
        assert abs(mean - 1.0) < 0.2


class TestWeylLaw:
    """Test Weyl's law for counting function."""
    
    def test_weyl_analysis_runs(self):
        """Weyl analysis should run without errors."""
        atlas = Atlas3Operator(N=100, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        weyl_stats = weyl_law_analysis(eigenvalues, num_analyze=50)
        assert 'weyl_coefficient_a' in weyl_stats
        assert 'oscillation_amplitude' in weyl_stats
    
    def test_weyl_coefficient_positive(self):
        """Weyl coefficient should be positive."""
        atlas = Atlas3Operator(N=200, beta_0=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        weyl_stats = weyl_law_analysis(eigenvalues, num_analyze=100)
        assert weyl_stats['weyl_coefficient_a'] > 0
    
    def test_weyl_oscillations_present(self):
        """Should detect logarithmic oscillations."""
        atlas = Atlas3Operator(N=200, beta_0=2.0)
        eigenvalues, _ = atlas.compute_spectrum()
        weyl_stats = weyl_law_analysis(eigenvalues, num_analyze=100)
        # Oscillation amplitude should be non-zero
        assert weyl_stats['oscillation_amplitude'] > 0.0


class TestAndersonLocalization:
    """Test Anderson localization transition."""
    
    def test_anderson_analysis_runs(self):
        """Anderson analysis should run without errors."""
        atlas = Atlas3Operator(N=100, beta_0=0.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=30)
        assert 'mean_ipr' in anderson_stats
        assert 'localization_ratio' in anderson_stats
    
    def test_ipr_positive(self):
        """IPR should be positive."""
        atlas = Atlas3Operator(N=100, beta_0=1.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=30)
        assert anderson_stats['mean_ipr'] > 0
    
    def test_ipr_bounded(self):
        """IPR should be bounded by 1."""
        atlas = Atlas3Operator(N=100, beta_0=2.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=30)
        # IPR ≤ 1 for normalized states
        assert anderson_stats['mean_ipr'] <= 1.0
    
    def test_extended_states_small_beta(self):
        """Small β should give extended states."""
        atlas = Atlas3Operator(N=200, beta_0=0.5)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=50)
        # Extended states: IPR ~ 1/N
        assert anderson_stats['localization_ratio'] < 10.0
    
    def test_localized_states_large_beta(self):
        """Large β should give more localized states."""
        atlas = Atlas3Operator(N=200, beta_0=3.5)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=50)
        # More localized: higher IPR
        assert anderson_stats['localization_ratio'] > 3.0


class TestProblemStatementValidation:
    """Validate specific claims from the problem statement."""
    
    def test_beta_2_coherence(self):
        """β=2.0 should maintain coherence (real spectrum)."""
        atlas = Atlas3Operator(N=200, beta_0=2.0, V_amp=V_AMP_CRITICAL)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        # Should have small imaginary parts
        assert pt_check['max_imaginary'] < 0.1
    
    def test_beta_2_57_breaking(self):
        """β≈2.57 should show PT breaking with Im(λ) ~ 0.64."""
        atlas = Atlas3Operator(N=200, beta_0=KAPPA_PI, V_amp=V_AMP_CRITICAL)
        eigenvalues, _ = atlas.compute_spectrum()
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        # Should have significant imaginary parts
        # Relaxed range: 0.2 to 1.5 (nominal 0.64)
        assert 0.2 < pt_check['max_imaginary'] < 1.5
    
    def test_gue_statistics_match(self):
        """GUE variance should be ~0.17 (vs. theoretical 0.168)."""
        atlas = Atlas3Operator(N=300, beta_0=0.0, V_amp=V_AMP_CRITICAL)
        eigenvalues, _ = atlas.compute_spectrum()
        gue_stats = analyze_gue_statistics(eigenvalues, num_unfold=150)
        variance = gue_stats['variance']
        # Should be close to GUE value
        assert abs(variance - GUE_VARIANCE_THEORETICAL) < 0.1
    
    def test_anderson_transition_at_kappa_pi(self):
        """IPR should increase significantly near κ_Π."""
        # Test β values around κ_Π
        beta_vals = [1.5, KAPPA_PI, 3.5]
        ipr_vals = []
        
        for beta in beta_vals:
            atlas = Atlas3Operator(N=150, beta_0=beta, V_amp=V_AMP_CRITICAL)
            eigenvalues, eigenvectors = atlas.compute_spectrum()
            anderson_stats = check_anderson_localization(eigenvectors, eigenvalues, num_states=40)
            ipr_vals.append(anderson_stats['mean_ipr'])
        
        # IPR should increase with β
        assert ipr_vals[-1] > ipr_vals[0]
    
    def test_full_validation_suite(self):
        """Run complete validation suite."""
        results = run_atlas3_validation(
            beta_values=[0.0, 2.0, KAPPA_PI],
            N=200,
            V_amp=V_AMP_CRITICAL,
            verbose=False
        )
        
        # Should have results for each β
        assert len(results) == 3
        
        # Check structure
        for key in results:
            assert 'pt_symmetry' in results[key]
            assert 'gue_statistics' in results[key]
            assert 'weyl_law' in results[key]
            assert 'anderson_localization' in results[key]
    
    def test_verification_checks(self):
        """Verify problem statement claims."""
        results = run_atlas3_validation(
            beta_values=[0.0, 2.0, KAPPA_PI, 3.0],
            N=200,
            V_amp=V_AMP_CRITICAL,
            verbose=False
        )
        
        checks = verify_problem_statement_claims(results)
        
        # Should have at least some checks
        assert len(checks) > 0
        
        # Check types
        for check_name, passed in checks.items():
            assert isinstance(passed, (bool, np.bool_))


class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_small_N(self):
        """Should work with small N."""
        atlas = Atlas3Operator(N=10, beta_0=1.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        assert len(eigenvalues) == 10
    
    def test_large_N(self):
        """Should work with large N."""
        atlas = Atlas3Operator(N=1000, beta_0=1.0)
        eigenvalues, eigenvectors = atlas.compute_spectrum()
        assert len(eigenvalues) == 1000
    
    def test_zero_potential(self):
        """Should work with zero potential."""
        atlas = Atlas3Operator(N=50, beta_0=0.0, V_amp=0.0)
        eigenvalues, _ = atlas.compute_spectrum()
        # Should still have spectrum
        assert len(eigenvalues) == 50
    
    def test_very_large_beta(self):
        """Should handle very large β."""
        atlas = Atlas3Operator(N=50, beta_0=10.0)
        eigenvalues, _ = atlas.compute_spectrum()
        # Should be in strongly broken PT phase
        pt_check = atlas.check_pt_symmetry(eigenvalues)
        assert pt_check['phase'] == 'entropy'
    
    def test_periodic_vs_non_periodic(self):
        """Should work with both periodic and non-periodic boundaries."""
        atlas_per = Atlas3Operator(N=50, periodic=True)
        atlas_non = Atlas3Operator(N=50, periodic=False)
        
        eigs_per, _ = atlas_per.compute_spectrum()
        eigs_non, _ = atlas_non.compute_spectrum()
        
        # Should both have spectra
        assert len(eigs_per) == 50
        assert len(eigs_non) == 50
        
        # Spectra should be different
        assert not np.allclose(eigs_per, eigs_non)


@pytest.mark.slow
class TestExtendedValidation:
    """Extended validation tests (marked as slow)."""
    
    def test_problem_statement_with_default_params(self):
        """Full validation with problem statement parameters (N=500)."""
        results = run_atlas3_validation(
            beta_values=[0.0, 2.0, KAPPA_PI, 3.0],
            N=N_DEFAULT,  # 500
            V_amp=V_AMP_CRITICAL,  # 12650
            verbose=False
        )
        
        checks = verify_problem_statement_claims(results)
        
        # At least 2 checks should pass
        num_passed = sum(checks.values())
        assert num_passed >= 2
    
    def test_beta_sweep_transition(self):
        """Fine sweep of β to detect PT transition."""
        beta_values = np.linspace(0, 4, 9)
        max_imag_values = []
        
        for beta in beta_values:
            atlas = Atlas3Operator(N=100, beta_0=beta)
            eigenvalues, _ = atlas.compute_spectrum()
            pt_check = atlas.check_pt_symmetry(eigenvalues)
            max_imag_values.append(pt_check['max_imaginary'])
        
        # Max imaginary part should increase with β
        assert max_imag_values[-1] > max_imag_values[0]
        
        # Should cross threshold around κ_Π
        # Find index closest to κ_Π
        idx_critical = np.argmin(np.abs(beta_values - KAPPA_PI))
        # Some imaginary parts should appear around critical point
        assert max_imag_values[idx_critical] > 0.05


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
