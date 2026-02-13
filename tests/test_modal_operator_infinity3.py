#!/usr/bin/env python3
"""
Tests for Modal Operator ∞³ - Vibrational Graph Analysis

Validates:
1. FASE 1: State space construction and operator building
2. FASE 2: Vibrational graph construction and spectral analysis
3. FASE 3: κ_Π extraction and validation
4. Stability under parameter variations
5. QCAL coherence integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.modal_operator_infinity3 import (
    ModalOperatorInfinity3,
    build_orthonormal_basis,
    compute_free_frequencies,
    compute_coupling_matrix,
    build_atlas3_operator,
    build_adjacency_matrix,
    compute_kappa_curve,
    theoretical_kappa_model,
    fit_kappa_pi,
    validate_kappa_pi,
    F0,
    OMEGA_0,
    C_QCAL,
    KAPPA_PI_THEORETICAL,
)


# =============================================================================
# TEST FIXTURES
# =============================================================================

@pytest.fixture
def default_params():
    """Default parameters for testing."""
    return {
        'T': 10.0,
        'n_modes': 30,
        'n_grid': 500,
        'basis_type': 'fourier',
        'forcing_type': 'harmonic'
    }


@pytest.fixture
def modal_analyzer(default_params):
    """Create a Modal Operator ∞³ analyzer instance."""
    return ModalOperatorInfinity3(**default_params)


# =============================================================================
# FASE 1 TESTS: STATE SPACE AND OPERATOR CONSTRUCTION
# =============================================================================

class TestFase1StateSpace:
    """Test suite for FASE 1: State space and operator construction."""
    
    def test_fourier_basis_orthonormality(self):
        """Test that Fourier basis is orthonormal."""
        T = 10.0
        n_modes = 10
        n_grid = 1000
        
        phi = build_orthonormal_basis(T, n_modes, "fourier")
        t_grid = np.linspace(0, T, n_grid)
        dt = T / (n_grid - 1)
        
        # Check orthonormality: ∫ φ_n(t)·φ_m(t) dt = δ_nm
        for n in range(n_modes):
            phi_n = phi(t_grid, n)
            for m in range(n_modes):
                phi_m = phi(t_grid, m)
                inner_product = np.trapezoid(phi_n * phi_m, dx=dt)
                
                if n == m:
                    assert abs(inner_product - 1.0) < 1e-8, \
                        f"<φ_{n}|φ_{n}> = {inner_product}, expected 1"
                else:
                    assert abs(inner_product) < 1e-8, \
                        f"<φ_{n}|φ_{m}> = {inner_product}, expected 0"
    
    def test_free_frequencies_positive(self):
        """Test that free frequencies are positive."""
        n_modes = 50
        T = 10.0
        
        omega_n = compute_free_frequencies(n_modes, T)
        
        assert len(omega_n) == n_modes
        assert np.all(omega_n > 0), "All frequencies must be positive"
        assert omega_n[0] == OMEGA_0, "First frequency should be OMEGA_0"
    
    def test_coupling_matrix_symmetric(self):
        """Test that coupling matrix is symmetric."""
        T = 10.0
        n_modes = 10
        n_grid = 500
        
        phi = build_orthonormal_basis(T, n_modes, "fourier")
        forcing = lambda t: np.cos(OMEGA_0 * t)
        
        K = compute_coupling_matrix(phi, forcing, T, n_modes, n_grid)
        
        assert K.shape == (n_modes, n_modes)
        assert np.allclose(K, K.T, atol=1e-10), "Coupling matrix must be symmetric"
    
    def test_operator_construction(self):
        """Test O_Atlas³ = D + K construction."""
        n_modes = 20
        T = 10.0
        
        omega_n = compute_free_frequencies(n_modes, T)
        K = np.random.randn(n_modes, n_modes)
        K = (K + K.T) / 2  # Make symmetric
        
        O = build_atlas3_operator(omega_n, K)
        
        assert O.shape == (n_modes, n_modes)
        
        # Check diagonal elements are ω_n²
        for n in range(n_modes):
            assert abs(O[n, n] - omega_n[n]**2 - K[n, n]) < 1e-10


class TestFase1Integration:
    """Test FASE 1 integration pipeline."""
    
    def test_run_fase1(self, modal_analyzer):
        """Test complete FASE 1 execution."""
        O = modal_analyzer.run_fase1(verbose=False)
        
        assert O is not None
        assert O.shape == (modal_analyzer.n_modes, modal_analyzer.n_modes)
        assert modal_analyzer.K is not None
        assert modal_analyzer.O is not None
        
        # Check operator is symmetric
        assert np.allclose(O, O.T, atol=1e-10)
    
    def test_different_basis_types(self, default_params):
        """Test different orthonormal basis types."""
        basis_types = ["fourier", "hermite", "legendre"]
        
        for basis_type in basis_types:
            params = default_params.copy()
            params['basis_type'] = basis_type
            analyzer = ModalOperatorInfinity3(**params)
            
            O = analyzer.run_fase1(verbose=False)
            assert O is not None
            assert O.shape == (params['n_modes'], params['n_modes'])


# =============================================================================
# FASE 2 TESTS: VIBRATIONAL GRAPH
# =============================================================================

class TestFase2VibrationalGraph:
    """Test suite for FASE 2: Vibrational graph construction."""
    
    def test_adjacency_matrix_properties(self):
        """Test adjacency matrix properties (weighted or binary)."""
        K = np.random.randn(20, 20)
        K = (K + K.T) / 2
        
        # Test weighted adjacency (default)
        A = build_adjacency_matrix(K, use_weighted=True)
        
        assert A.shape == K.shape
        assert np.all(A >= 0), "A must be non-negative"
        assert np.all(A <= 1), "A must be normalized (≤ 1)"
        assert np.allclose(A, A.T), "A must be symmetric"
        assert np.all(np.diag(A) == 0), "A diagonal must be zero"
        
        # Test binary adjacency
        A_binary = build_adjacency_matrix(K, use_weighted=False, threshold_percentile=75.0)
        assert np.all((A_binary == 0) | (A_binary == 1)), "Binary A must be 0 or 1"
    
    def test_kappa_curve_properties(self):
        """Test that κ(n) has expected properties."""
        eigenvalues = np.random.randn(50)
        kappa = compute_kappa_curve(eigenvalues)
        
        assert len(kappa) == len(eigenvalues)
        assert np.all(np.isfinite(kappa)), "κ(n) must be finite"
        
        # κ(n) should generally decrease for large n (1/(n·log n) behavior)
        # Check last half is mostly decreasing
        if len(kappa) > 20:
            second_half = kappa[len(kappa)//2:]
            decreasing_fraction = np.sum(np.diff(second_half) < 0) / len(np.diff(second_half))
            assert decreasing_fraction > 0.5, "κ(n) should be mostly decreasing for large n"
    
    def test_run_fase2(self, modal_analyzer):
        """Test complete FASE 2 execution."""
        modal_analyzer.run_fase1(verbose=False)
        kappa_curve = modal_analyzer.run_fase2(verbose=False)
        
        assert kappa_curve is not None
        assert len(kappa_curve) == modal_analyzer.n_modes
        assert modal_analyzer.A is not None
        assert modal_analyzer.eigenvalues is not None
        
        # Check graph properties (weighted adjacency is default)
        assert np.all(modal_analyzer.A >= 0), "Adjacency must be non-negative"
        assert np.allclose(modal_analyzer.A, modal_analyzer.A.T), "Adjacency must be symmetric"


# =============================================================================
# FASE 3 TESTS: κ_Π EXTRACTION
# =============================================================================

class TestFase3KappaPiExtraction:
    """Test suite for FASE 3: κ_Π extraction and validation."""
    
    def test_theoretical_model(self):
        """Test theoretical model κ(n) = C/(n·log n)."""
        n = np.arange(2, 100)
        C = KAPPA_PI_THEORETICAL
        
        kappa = theoretical_kappa_model(n, C)
        
        assert len(kappa) == len(n)
        assert np.all(kappa > 0), "κ(n) must be positive"
        assert np.all(np.diff(kappa) < 0), "κ(n) should be decreasing"
    
    def test_fit_kappa_pi_synthetic(self):
        """Test fitting with synthetic data."""
        # Generate synthetic data
        n = np.arange(1, 100)
        C_true = KAPPA_PI_THEORETICAL
        kappa_true = theoretical_kappa_model(n, C_true)
        
        # Add small noise
        np.random.seed(42)
        noise = 0.01 * np.random.randn(len(n))
        kappa_obs = kappa_true + noise
        
        # Fit
        C_fit, C_error, fit_info = fit_kappa_pi(n, kappa_obs, n_min=5)
        
        assert fit_info['success']
        assert abs(C_fit - C_true) / C_true < 0.05, \
            f"Fitted C = {C_fit}, expected ≈ {C_true}"
    
    def test_validate_kappa_pi(self):
        """Test κ_Π validation."""
        # Test valid case (in range)
        C_fit = 50.0  # Reasonable value
        validation = validate_kappa_pi(C_fit, tolerance=0.20)
        
        assert validation['is_valid']
        assert validation['in_range']
        
        # Test out of range case
        C_fit = 200.0  # Too large
        validation = validate_kappa_pi(C_fit, tolerance=0.20)
        
        assert not validation['is_valid']
    
    def test_run_fase3(self, modal_analyzer):
        """Test complete FASE 3 execution."""
        modal_analyzer.run_fase1(verbose=False)
        modal_analyzer.run_fase2(verbose=False)
        results = modal_analyzer.run_fase3(verbose=False)
        
        assert results is not None
        assert 'fit_info' in results
        assert 'validation' in results
        
        # Check that fitting was attempted
        assert 'success' in results['fit_info']


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

class TestCompleteAnalysis:
    """Test complete analysis pipeline."""
    
    def test_run_complete_analysis(self, modal_analyzer):
        """Test complete FASE 1-3 analysis."""
        results = modal_analyzer.run_complete_analysis(verbose=False)
        
        assert results is not None
        assert modal_analyzer.O is not None
        assert modal_analyzer.A is not None
        assert modal_analyzer.kappa_curve is not None
        assert 'fit_info' in results
    
    def test_different_forcing_types(self, default_params):
        """Test analysis with different forcing types."""
        forcing_types = [
            ('harmonic', {'n_harmonics': 5}),
            ('gaussian_pulse', {'A': 10.0}),
            ('constant', {'A0': 1.0})
        ]
        
        for forcing_type, params in forcing_types:
            test_params = default_params.copy()
            test_params['forcing_type'] = forcing_type
            test_params['forcing_params'] = params
            
            analyzer = ModalOperatorInfinity3(**test_params)
            results = analyzer.run_complete_analysis(verbose=False)
            
            assert results is not None
            assert 'fit_info' in results
    
    def test_stability_analysis(self, modal_analyzer):
        """Test stability under parameter variations."""
        # Use smaller variations for faster testing
        variations = {
            'n_grid': [300, 500],
            'n_modes': [20, 30],
        }
        
        stability = modal_analyzer.test_stability(
            variations=variations,
            verbose=False
        )
        
        assert stability is not None
        assert 'C_fits' in stability
        assert 'mean' in stability
        assert 'std' in stability
        assert len(stability['C_fits']) > 0


# =============================================================================
# QCAL COHERENCE TESTS
# =============================================================================

class TestQCALIntegration:
    """Test QCAL coherence integration."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are defined."""
        assert F0 == 141.7001
        assert OMEGA_0 == 2 * np.pi * F0
        assert C_QCAL == 244.36
        assert KAPPA_PI_THEORETICAL == 2.5773
    
    def test_frequency_integration(self):
        """Test that QCAL fundamental frequency is used."""
        n_modes = 20
        T = 10.0
        
        omega_n = compute_free_frequencies(n_modes, T)
        
        # First frequency should be OMEGA_0
        assert omega_n[0] == OMEGA_0
    
    def test_kappa_pi_target(self, modal_analyzer):
        """Test that κ_Π extraction produces reasonable values."""
        modal_analyzer.run_complete_analysis(verbose=False)
        
        if modal_analyzer.fit_results['fit_info']['success']:
            C_fit = modal_analyzer.fit_results['fit_info']['C_fit']
            
            # Should be in reasonable range (not exact match expected)
            assert 0.1 < C_fit < 100, \
                f"C_fit = {C_fit}, should be in reasonable range"
            
            # Check that fit quality is good
            rms_error = modal_analyzer.fit_results['fit_info']['rms_error']
            assert rms_error < 1.0, "RMS error should be reasonable"


# =============================================================================
# EDGE CASES AND ROBUSTNESS
# =============================================================================

class TestEdgeCases:
    """Test edge cases and robustness."""
    
    def test_small_n_modes(self):
        """Test with small number of modes."""
        analyzer = ModalOperatorInfinity3(n_modes=10, n_grid=200)
        
        # Should run without errors
        results = analyzer.run_complete_analysis(verbose=False)
        assert results is not None
    
    def test_large_n_modes(self):
        """Test with larger number of modes."""
        analyzer = ModalOperatorInfinity3(n_modes=100, n_grid=500)
        
        # Should run without errors
        O = analyzer.run_fase1(verbose=False)
        assert O.shape == (100, 100)
    
    def test_different_time_intervals(self):
        """Test with different time intervals."""
        for T in [5.0, 10.0, 20.0]:
            analyzer = ModalOperatorInfinity3(T=T, n_modes=20, n_grid=300)
            results = analyzer.run_complete_analysis(verbose=False)
            assert results is not None


# =============================================================================
# NUMERICAL ACCURACY TESTS
# =============================================================================

class TestNumericalAccuracy:
    """Test numerical accuracy and precision."""
    
    def test_operator_hermiticity(self, modal_analyzer):
        """Test that operator is Hermitian (symmetric real)."""
        modal_analyzer.run_fase1(verbose=False)
        O = modal_analyzer.O
        
        # O should be symmetric (Hermitian for real matrices)
        assert np.allclose(O, O.T, atol=1e-10)
    
    def test_eigenvalue_reality(self, modal_analyzer):
        """Test that eigenvalues are real."""
        modal_analyzer.run_fase1(verbose=False)
        modal_analyzer.run_fase2(verbose=False)
        
        eigenvalues = modal_analyzer.eigenvalues
        
        # For symmetric real matrix, eigenvalues should be real
        assert np.allclose(eigenvalues.imag, 0, atol=1e-10)
    
    def test_integration_convergence(self):
        """Test that coupling matrix shows reasonable convergence with grid refinement."""
        T = 10.0
        n_modes = 10
        phi = build_orthonormal_basis(T, n_modes, "fourier")
        forcing = lambda t: np.cos(OMEGA_0 * t)
        
        # Compute with different grid resolutions
        K_coarse = compute_coupling_matrix(phi, forcing, T, n_modes, n_grid=100)
        K_fine = compute_coupling_matrix(phi, forcing, T, n_modes, n_grid=1000)
        K_very_fine = compute_coupling_matrix(phi, forcing, T, n_modes, n_grid=5000)
        
        # Check that fine and very_fine are closer than coarse and fine
        rel_diff_1 = np.linalg.norm(K_fine - K_coarse, 'fro') / np.linalg.norm(K_fine, 'fro')
        rel_diff_2 = np.linalg.norm(K_very_fine - K_fine, 'fro') / np.linalg.norm(K_very_fine, 'fro')
        
        # Convergence: error should decrease with finer grid
        assert rel_diff_2 < rel_diff_1, f"Should converge: {rel_diff_1} vs {rel_diff_2}"


# =============================================================================
# MAIN TEST EXECUTION
# =============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
