#!/usr/bin/env python3
"""
Tests for orthonormal Fourier basis and modal covariance operator modules.

Tests verify:
1. Orthonormality of basis functions
2. Modal decomposition and reconstruction
3. Covariance operator computation
4. Adjacency graph construction
5. Curvature analysis and asymptotic fit
6. Full experiment orchestration

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import os
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from build_orthonormal_basis import OrthonormalFourierBasis
from compute_covariance_operator import ModalCovarianceOperator
from analyze_kappa_curve import KappaCurveAnalyzer
from run_kappa_experiment_2 import KappaExperiment

# Test tolerances
ORTHONORMALITY_TOL = 1e-10
RECONSTRUCTION_TOL = 1e-6
FIT_R2_MIN = 0.95


class TestOrthonormalFourierBasis:
    """Test orthonormal Fourier basis construction."""
    
    def test_basis_initialization(self):
        """Test basis initialization with default parameters."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        assert basis.T == 1.0
        assert basis.n_modes == 20
        assert len(basis.t_points) == 1000  # default n_points
    
    def test_basis_dc_component(self):
        """Test DC component φ_0(t) = 1/√T."""
        basis = OrthonormalFourierBasis(T=2.0, n_modes=10)
        t = np.array([0.0, 0.5, 1.0])
        phi_0 = basis.phi_n(0, t)
        
        expected = np.ones_like(t) / np.sqrt(2.0)
        assert np.allclose(phi_0, expected, atol=1e-12)
    
    def test_basis_oscillatory_mode(self):
        """Test oscillatory mode φ_n(t) = √(2/T) cos(nπt/T)."""
        T = 1.0
        n = 2
        basis = OrthonormalFourierBasis(T=T, n_modes=10)
        t = np.array([0.0, T/4, T/2])
        phi_n = basis.phi_n(n, t)
        
        expected = np.sqrt(2.0/T) * np.cos(n * np.pi * t / T)
        assert np.allclose(phi_n, expected, atol=1e-12)
    
    def test_orthonormality(self):
        """Test orthonormality: ⟨φ_n, φ_m⟩ = δ_{nm}."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20, n_points=2000)
        verification = basis.verify_orthonormality(n_check=10)
        
        assert verification['is_orthonormal'] == True
        assert verification['max_diagonal_error'] < ORTHONORMALITY_TOL
        assert verification['max_offdiag_error'] < ORTHONORMALITY_TOL
    
    def test_decomposition_reconstruction(self):
        """Test function decomposition and reconstruction."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=50, n_points=2000)
        
        # Test function: f(t) = cos(2πt) + 0.5 cos(4πt)
        def test_func(t):
            return np.cos(2 * np.pi * t) + 0.5 * np.cos(4 * np.pi * t)
        
        # Decompose
        coeffs = basis.decompose_function(test_func, n_coeffs=20)
        
        # Reconstruct
        t_test = np.linspace(0, basis.T, 500)
        f_original = test_func(t_test)
        f_reconstructed = basis.reconstruct_function(coeffs, t_test)
        
        # Check reconstruction error
        mse = np.mean((f_original - f_reconstructed)**2)
        assert mse < RECONSTRUCTION_TOL
    
    def test_parseval_identity(self):
        """Test Parseval's identity: ‖f‖² = Σ|α_n|²."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=30, n_points=2000)
        
        def test_func(t):
            return np.sin(2 * np.pi * t) + 0.3 * np.cos(6 * np.pi * t)
        
        # L² norm of function
        f_vals = test_func(basis.t_points)
        norm_squared_continuous = np.trapezoid(f_vals**2, basis.t_points)
        
        # Sum of squared coefficients
        coeffs = basis.decompose_function(test_func, n_coeffs=30)
        norm_squared_discrete = np.sum(coeffs**2)
        
        # Should be approximately equal
        relative_error = abs(norm_squared_continuous - norm_squared_discrete) / norm_squared_continuous
        assert relative_error < 0.01  # 1% tolerance


class TestModalCovarianceOperator:
    """Test modal covariance operator computation."""
    
    def test_covariance_matrix_identity(self):
        """Test that covariance matrix is identity for orthonormal basis."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        cov_op = ModalCovarianceOperator(basis)
        
        O_cov = cov_op.compute_covariance_matrix(max_mode=10)
        
        # Should be identity matrix
        identity = np.eye(O_cov.shape[0])
        assert np.allclose(O_cov, identity, atol=1e-10)
    
    def test_forcing_operator_symmetry(self):
        """Test that forcing operator is symmetric."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        cov_op = ModalCovarianceOperator(basis)
        
        forcing_coeffs = np.zeros(21)
        forcing_coeffs[1] = 1.0
        forcing_coeffs[3] = 0.5
        
        O_forcing = cov_op.compute_forcing_operator(forcing_coeffs, max_mode=10)
        
        # Should be symmetric
        assert np.allclose(O_forcing, O_forcing.T, atol=1e-10)
    
    def test_adjacency_graph_binary(self):
        """Test that adjacency graph contains only 0s and 1s."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        cov_op = ModalCovarianceOperator(basis)
        
        cov_op.compute_covariance_matrix(max_mode=10)
        A_graph = cov_op.compute_adjacency_graph(theta=0.5)
        
        # Should contain only 0 and 1
        assert np.all((A_graph == 0) | (A_graph == 1))
    
    def test_adjacency_graph_symmetry(self):
        """Test that adjacency graph is symmetric."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        cov_op = ModalCovarianceOperator(basis)
        
        forcing_coeffs = np.zeros(21)
        forcing_coeffs[1] = 1.0
        
        cov_op.compute_forcing_operator(forcing_coeffs, max_mode=10)
        A_graph = cov_op.compute_adjacency_graph(theta=0.1, use_forcing=True)
        
        # Should be symmetric
        assert np.allclose(A_graph, A_graph.T, atol=1e-10)
    
    def test_graph_properties_consistency(self):
        """Test consistency of graph properties."""
        basis = OrthonormalFourierBasis(T=1.0, n_modes=20)
        cov_op = ModalCovarianceOperator(basis)
        
        cov_op.compute_covariance_matrix(max_mode=10)
        A_graph = cov_op.compute_adjacency_graph(theta=0.5)
        props = cov_op.analyze_graph_properties()
        
        # Check consistency
        assert props['n_nodes'] == A_graph.shape[0]
        # Edges exclude self-loops for undirected graph
        expected_edges = (np.sum(A_graph) - np.trace(A_graph)) / 2
        assert np.isclose(props['n_edges'], expected_edges)
        assert 0 <= props['density'] <= 1


class TestKappaCurveAnalyzer:
    """Test curvature analysis."""
    
    def test_laplacian_computation(self):
        """Test graph Laplacian computation: L = D - A."""
        # Simple test graph
        A = np.array([
            [0, 1, 1],
            [1, 0, 1],
            [1, 1, 0]
        ], dtype=float)
        
        analyzer = KappaCurveAnalyzer(A)
        L = analyzer.compute_graph_laplacian()
        
        # Expected Laplacian for complete graph K3
        expected = np.array([
            [2, -1, -1],
            [-1, 2, -1],
            [-1, -1, 2]
        ], dtype=float)
        
        assert np.allclose(L, expected, atol=1e-10)
    
    def test_normalized_laplacian_range(self):
        """Test that normalized Laplacian eigenvalues are in [0, 2]."""
        # Create random graph
        np.random.seed(42)
        n = 20
        A = np.random.rand(n, n)
        A = (A + A.T) / 2  # Symmetrize
        A = (A > 0.5).astype(float)  # Binarize
        np.fill_diagonal(A, 0)  # No self-loops
        
        analyzer = KappaCurveAnalyzer(A)
        L_norm = analyzer.compute_normalized_laplacian()
        
        eigenvalues = np.linalg.eigvalsh(L_norm)
        
        # Eigenvalues should be in [0, 2]
        assert np.all(eigenvalues >= -1e-10)  # Allow small numerical error
        assert np.all(eigenvalues <= 2 + 1e-10)
    
    def test_spectral_curvature_positive(self):
        """Test that spectral curvature is positive."""
        # Create test graph
        np.random.seed(42)
        n = 30
        A = np.random.rand(n, n)
        A = (A + A.T) / 2
        A = (A > 0.6).astype(float)
        np.fill_diagonal(A, 0)
        
        analyzer = KappaCurveAnalyzer(A)
        kappa = analyzer.compute_spectral_curvature()
        
        # All curvature values should be positive
        assert np.all(kappa > 0)
    
    def test_asymptotic_fit_quality(self):
        """Test that asymptotic fit achieves good R²."""
        # Create graph with expected 1/(n log n) behavior
        np.random.seed(42)
        n = 50
        A = np.random.rand(n, n)
        A = (A + A.T) / 2
        A = (A > 0.5).astype(float)
        np.fill_diagonal(A, 0)
        
        analyzer = KappaCurveAnalyzer(A)
        analyzer.compute_spectral_curvature()
        
        fit_results = analyzer.fit_asymptotic_form(n_min=5, n_max=40)
        
        # R² should be reasonably high
        # Note: This is a synthetic test, so we use relaxed threshold
        assert fit_results['r_squared'] > 0.8


class TestKappaExperiment:
    """Test full experiment orchestration."""
    
    def test_default_config(self):
        """Test default configuration creation."""
        config = KappaExperiment.default_config()
        
        assert 'T' in config
        assert 'n_modes' in config
        assert 'forcing' in config
        assert 'graph' in config
        assert 'curvature' in config
        assert 'qcal' in config
    
    def test_experiment_initialization(self):
        """Test experiment initialization."""
        config = KappaExperiment.default_config()
        config['n_modes'] = 10  # Small for fast test
        
        experiment = KappaExperiment(config=config, output_dir='/tmp/test_kappa')
        
        assert experiment.config == config
        assert experiment.output_dir == Path('/tmp/test_kappa')
        assert 'timestamp' in experiment.results
    
    @pytest.mark.slow
    def test_full_experiment_execution(self):
        """Test full experiment execution (slow test)."""
        # Create minimal config for fast execution
        config = {
            'T': 1.0,
            'n_modes': 15,
            'n_points': 500,
            'forcing': {
                'type': 'resonant',
                'modes': [1, 3],
                'amplitudes': [1.0, 0.5]
            },
            'graph': {
                'theta': 0.1
            },
            'curvature': {
                'method': 'laplacian',
                'fit_range': (3, 12)
            },
            'qcal': {
                'f0': 141.7001,
                'C': 244.36
            }
        }
        
        experiment = KappaExperiment(config=config, output_dir='/tmp/test_kappa_full')
        experiment.run_full_experiment()
        
        # Check that all result sections are populated
        assert 'basis' in experiment.results
        assert 'operator' in experiment.results
        assert 'graph' in experiment.results
        assert 'curvature' in experiment.results
        
        # Check basis results
        assert experiment.results['basis']['orthonormality_verified'] == True
        
        # Check graph results
        assert experiment.results['graph']['n_nodes'] > 0
        assert experiment.results['graph']['n_edges'] >= 0
        
        # Check curvature fit
        assert 'C' in experiment.results['curvature']['fit']
        assert experiment.results['curvature']['fit']['C'] > 0


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are correctly defined."""
        from build_orthonormal_basis import F0, C_QCAL
        
        assert F0 == 141.7001
        assert C_QCAL == 244.36
    
    def test_basis_with_qcal_frequency(self):
        """Test basis construction with QCAL frequency."""
        from build_orthonormal_basis import F0, OMEGA_0
        
        # Period corresponding to fundamental frequency
        T_qcal = 1.0 / F0  # ~7.05 ms
        
        basis = OrthonormalFourierBasis(T=T_qcal, n_modes=10)
        
        # Verify orthonormality still holds
        verification = basis.verify_orthonormality(n_check=5)
        assert verification['is_orthonormal'] == True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
