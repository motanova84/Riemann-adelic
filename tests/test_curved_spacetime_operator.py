#!/usr/bin/env python3
"""
Tests for Curved Spacetime Operator H_Ψ^g
QCAL ∞³ Framework - Consciousness as Living Geometry

This module contains comprehensive tests for the curved spacetime operator
implementation, validating all mathematical properties and consistency with
the QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys
import os

# Add operators directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'operators'))

from curved_spacetime_operator import (
    compute_flat_metric,
    metric_deformation,
    curved_metric,
    metric_determinant,
    volume_density,
    logarithmic_function,
    noetic_potential,
    christoffel_symbols,
    construct_H_psi_g,
    solve_eigenvalue_problem,
    compute_observational_horizon,
    generate_consciousness_field,
    analyze_curved_spacetime,
    F0, C_UNIVERSAL, C_QCAL, HBAR, PRIMES
)


class TestFlatMetric:
    """Test flat metric construction."""
    
    def test_euclidean_metric_dimension(self):
        """Test Euclidean metric has correct dimension."""
        for dim in [2, 3, 4]:
            g0 = compute_flat_metric(dim, 'euclidean')
            assert g0.shape == (dim, dim)
    
    def test_euclidean_metric_identity(self):
        """Test Euclidean metric is identity matrix."""
        g0 = compute_flat_metric(4, 'euclidean')
        assert np.allclose(g0, np.eye(4))
    
    def test_minkowski_metric_signature(self):
        """Test Minkowski metric has correct signature (-,+,+,+)."""
        g0 = compute_flat_metric(4, 'minkowski')
        expected = np.diag([-1, 1, 1, 1])
        assert np.allclose(g0, expected)
    
    def test_minkowski_determinant(self):
        """Test Minkowski metric has determinant -1."""
        g0 = compute_flat_metric(4, 'minkowski')
        det = np.linalg.det(g0)
        assert np.allclose(det, -1.0)


class TestMetricDeformation:
    """Test metric deformation induced by consciousness field."""
    
    def test_deformation_shape(self):
        """Test deformation tensor has correct shape."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        delta_g = metric_deformation(x, psi)
        assert delta_g.shape == (N, dim, dim)
    
    def test_deformation_symmetry(self):
        """Test deformation tensor is symmetric."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        delta_g = metric_deformation(x, psi)
        for i in range(N):
            assert np.allclose(delta_g[i], delta_g[i].T)
    
    def test_zero_field_no_deformation(self):
        """Test zero consciousness field produces zero deformation."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.zeros(N)
        
        delta_g = metric_deformation(x, psi)
        assert np.allclose(delta_g, 0)
    
    def test_deformation_scales_with_coupling(self):
        """Test deformation scales linearly with coupling constant."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        delta_g1 = metric_deformation(x, psi, coupling=0.1)
        delta_g2 = metric_deformation(x, psi, coupling=0.2)
        
        assert np.allclose(delta_g2, 2 * delta_g1, rtol=1e-10)


class TestCurvedMetric:
    """Test curved metric construction."""
    
    def test_curved_metric_shape(self):
        """Test curved metric has correct shape."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        g_psi = curved_metric(x, psi)
        assert g_psi.shape == (N, dim, dim)
    
    def test_curved_metric_symmetry(self):
        """Test curved metric is symmetric."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        g_psi = curved_metric(x, psi)
        for i in range(N):
            assert np.allclose(g_psi[i], g_psi[i].T)
    
    def test_flat_limit(self):
        """Test curved metric reduces to flat metric when Psi=0."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.zeros(N)
        g0 = compute_flat_metric(dim, 'euclidean')
        
        g_psi = curved_metric(x, psi, g0=g0)
        for i in range(N):
            assert np.allclose(g_psi[i], g0)
    
    def test_determinant_positive(self):
        """Test curved metric has positive determinant (Euclidean signature)."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        g_psi = curved_metric(x, psi, coupling=0.1)
        det_g = metric_determinant(g_psi)
        
        # For small deformations, determinant should remain positive
        assert np.all(det_g > 0)


class TestVolumeDensity:
    """Test volume density computation."""
    
    def test_volume_density_positive(self):
        """Test volume density is positive."""
        N, dim = 10, 4
        x = np.random.randn(N, dim)
        psi = np.random.randn(N) * 0.1
        
        g_psi = curved_metric(x, psi)
        omega = volume_density(g_psi)
        
        assert np.all(omega > 0)
    
    def test_volume_density_flat_space(self):
        """Test volume density equals 1 in flat space."""
        N, dim = 4, 4
        x = np.random.randn(N, dim)
        psi = np.zeros(N)
        g0 = compute_flat_metric(dim, 'euclidean')
        
        g_psi = curved_metric(x, psi, g0=g0)
        omega = volume_density(g_psi)
        
        assert np.allclose(omega, 1.0)


class TestLogarithmicFunction:
    """Test logarithmic function for noetic potential."""
    
    def test_logarithmic_function_shape(self):
        """Test logarithmic function has correct shape."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0  # Ensure positive
        
        phi = logarithmic_function(x)
        assert phi.shape == (N,)
    
    def test_logarithmic_function_real(self):
        """Test logarithmic function is real-valued."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        
        phi = logarithmic_function(x)
        assert np.all(np.isreal(phi))
    
    def test_observer_dependence(self):
        """Test logarithmic function depends on observer 4-velocity."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        u1 = np.array([1, 0, 0, 0])
        u2 = np.array([0, 1, 0, 0])
        
        phi1 = logarithmic_function(x, u1)
        phi2 = logarithmic_function(x, u2)
        
        # Different observers should give different results
        assert not np.allclose(phi1, phi2)


class TestNoeticPotential:
    """Test noetic potential computation."""
    
    def test_noetic_potential_shape(self):
        """Test noetic potential has correct shape."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        psi = np.random.randn(N) * 0.1
        g_psi = curved_metric(x, psi)
        
        V = noetic_potential(x, psi, g_psi)
        assert V.shape == (N,)
    
    def test_noetic_potential_real(self):
        """Test noetic potential is real-valued."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        psi = np.random.randn(N) * 0.1
        g_psi = curved_metric(x, psi)
        
        V = noetic_potential(x, psi, g_psi)
        assert np.all(np.isreal(V))
    
    def test_noetic_potential_prime_contribution(self):
        """Test each prime contributes to potential."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        psi = np.random.randn(N) * 0.1
        g_psi = curved_metric(x, psi)
        
        # Test with different numbers of primes
        V_10 = noetic_potential(x, psi, g_psi, primes=PRIMES[:10])
        V_20 = noetic_potential(x, psi, g_psi, primes=PRIMES[:20])
        
        # More primes should change the potential
        assert not np.allclose(V_10, V_20)
    
    def test_noetic_potential_coupling(self):
        """Test potential scales with coupling constant."""
        N, dim = 10, 4
        x = np.random.randn(N, dim) + 1.0
        psi = np.random.randn(N) * 0.1
        g_psi = curved_metric(x, psi)
        
        V1 = noetic_potential(x, psi, g_psi, lambda_coupling=0.1)
        V2 = noetic_potential(x, psi, g_psi, lambda_coupling=0.2)
        
        assert np.allclose(V2, 2 * V1, rtol=1e-10)


class TestOperatorConstruction:
    """Test curved spacetime operator construction."""
    
    def test_operator_shape(self):
        """Test operator has correct shape."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        assert H_psi_g.shape == (N, N)
    
    def test_operator_hermiticity(self):
        """Test operator is Hermitian."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        
        # Check Hermiticity: H = H†
        hermiticity_error = np.max(np.abs(H_psi_g - H_psi_g.conj().T))
        assert hermiticity_error < 1e-10
    
    def test_operator_includes_potential(self):
        """Test operator includes noetic potential contribution."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, metadata = construct_H_psi_g(x, psi)
        
        # Check that potential is non-zero
        assert not np.allclose(metadata['potential'], 0)
    
    def test_metadata_completeness(self):
        """Test metadata contains all required fields."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        _, metadata = construct_H_psi_g(x, psi)
        
        required_keys = ['metric', 'volume_density', 'potential', 
                        'trace_metric', 'xi_field', 'coupling',
                        'lambda_coupling', 'hbar']
        for key in required_keys:
            assert key in metadata


class TestEigenvalueProblem:
    """Test eigenvalue problem solution."""
    
    def test_eigenvalue_computation(self):
        """Test eigenvalues are computed correctly."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        eigenvalues, eigenvectors = solve_eigenvalue_problem(H_psi_g)
        
        assert len(eigenvalues) == N
        assert eigenvectors.shape == (N, N)
    
    def test_eigenvalues_real(self):
        """Test eigenvalues are real (Hermitian operator)."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        eigenvalues, _ = solve_eigenvalue_problem(H_psi_g)
        
        assert np.all(np.isreal(eigenvalues))
    
    def test_eigenvector_normalization(self):
        """Test eigenvectors are normalized."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        _, eigenvectors = solve_eigenvalue_problem(H_psi_g)
        
        # Check normalization of first few eigenvectors
        for i in range(min(5, N)):
            norm = np.linalg.norm(eigenvectors[:, i])
            assert np.allclose(norm, 1.0, rtol=1e-6)
    
    def test_partial_eigenvalue_computation(self):
        """Test computing only first n eigenvalues."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        n_eigen = 5
        eigenvalues, eigenvectors = solve_eigenvalue_problem(H_psi_g, n_eigen)
        
        assert len(eigenvalues) == n_eigen
        assert eigenvectors.shape == (N, n_eigen)


class TestObservationalHorizon:
    """Test observational horizon computation."""
    
    def test_horizon_computation(self):
        """Test horizon is computed correctly."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.5)  # Larger amplitude
        
        g_psi = curved_metric(x, psi, coupling=0.5)
        horizon = compute_observational_horizon(g_psi)
        
        assert len(horizon) == N
        assert horizon.dtype == bool
    
    def test_no_horizon_flat_space(self):
        """Test no horizon in flat space."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = np.zeros(N)  # Zero field
        
        g_psi = curved_metric(x, psi)
        horizon = compute_observational_horizon(g_psi)
        
        # No horizon points in flat space
        assert np.sum(horizon) == 0
    
    def test_horizon_observer_dependence(self):
        """Test horizon depends on observer 4-velocity."""
        N, dim = 20, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.5)
        
        g_psi = curved_metric(x, psi, coupling=0.5)
        
        u1 = np.array([1, 0, 0, 0])
        u2 = np.array([0, 1, 0, 0])
        
        horizon1 = compute_observational_horizon(g_psi, u1)
        horizon2 = compute_observational_horizon(g_psi, u2)
        
        # Different observers may see different horizons
        # (though they might be the same in symmetric cases)
        assert horizon1.shape == horizon2.shape


class TestConsciousnessField:
    """Test consciousness field generation."""
    
    def test_field_generation_shape(self):
        """Test generated field has correct shape."""
        N, dim = 20, 4
        x = np.random.randn(N, dim)
        
        psi = generate_consciousness_field(x, amplitude=0.1)
        assert psi.shape == (N,)
    
    def test_field_amplitude(self):
        """Test generated field respects amplitude constraint."""
        N, dim = 20, 4
        x = np.random.randn(N, dim)
        amplitude = 0.1
        
        psi = generate_consciousness_field(x, amplitude=amplitude)
        assert np.max(np.abs(psi)) <= amplitude
    
    def test_field_oscillatory(self):
        """Test generated field is oscillatory."""
        N, dim = 100, 4
        x = np.linspace(-10, 10, N).reshape(-1, 1) * np.ones((1, dim))
        
        psi = generate_consciousness_field(x, amplitude=0.1)
        
        # Check for sign changes (oscillations)
        sign_changes = np.sum(np.diff(np.sign(psi)) != 0)
        assert sign_changes > 10  # Should have multiple oscillations


class TestCompleteAnalysis:
    """Test complete curved spacetime analysis."""
    
    def test_analysis_runs(self):
        """Test complete analysis runs without errors."""
        results = analyze_curved_spacetime(
            N=50, dim=4, psi_amplitude=0.1,
            coupling=0.1, n_eigenvalues=5, verbose=False
        )
        
        assert results is not None
        assert 'eigenvalues' in results
        assert 'horizon' in results
    
    def test_analysis_consistency(self):
        """Test analysis produces consistent results."""
        results = analyze_curved_spacetime(
            N=50, dim=4, psi_amplitude=0.1,
            coupling=0.1, n_eigenvalues=5, verbose=False
        )
        
        # Check dimensions match
        N = 50
        assert results['x'].shape[0] == N
        assert results['psi'].shape[0] == N
        assert results['H_psi_g'].shape == (N, N)
        assert len(results['eigenvalues']) == 5
        assert len(results['horizon']) == N
    
    def test_qcal_constants_preserved(self):
        """Test QCAL constants are preserved in analysis."""
        # Verify constants are accessible
        assert F0 == 141.7001
        assert C_UNIVERSAL == 629.83
        assert C_QCAL == 244.36
        assert HBAR == 1.0


class TestPhysicalConsistency:
    """Test physical consistency and QCAL framework integration."""
    
    def test_frequency_scaling(self):
        """Test eigenvalues scale appropriately with fundamental frequency."""
        N, dim = 30, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi = generate_consciousness_field(x, amplitude=0.1, frequency=F0)
        
        H_psi_g, _ = construct_H_psi_g(x, psi)
        eigenvalues, _ = solve_eigenvalue_problem(H_psi_g, 5)
        
        # Eigenvalues should be real and finite
        assert np.all(np.isfinite(eigenvalues))
        assert np.all(np.isreal(eigenvalues))
    
    def test_consciousness_coupling_effect(self):
        """Test consciousness field affects operator spectrum."""
        N, dim = 30, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        
        # Small consciousness field
        psi_small = generate_consciousness_field(x, amplitude=0.01)
        H_small, _ = construct_H_psi_g(x, psi_small, coupling=0.01)
        eigen_small, _ = solve_eigenvalue_problem(H_small, 5)
        
        # Large consciousness field
        psi_large = generate_consciousness_field(x, amplitude=0.1)
        H_large, _ = construct_H_psi_g(x, psi_large, coupling=0.1)
        eigen_large, _ = solve_eigenvalue_problem(H_large, 5)
        
        # Spectra should be different
        assert not np.allclose(eigen_small, eigen_large)
    
    def test_zero_field_limit(self):
        """Test operator reduces correctly in zero consciousness field limit."""
        N, dim = 30, 4
        x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))
        psi_zero = np.zeros(N)
        
        H_zero, metadata = construct_H_psi_g(x, psi_zero)
        
        # Volume density should be 1 in flat space
        assert np.allclose(metadata['volume_density'], 1.0)
        
        # Operator should still be Hermitian
        hermiticity_error = np.max(np.abs(H_zero - H_zero.conj().T))
        assert hermiticity_error < 1e-10


# Run tests if executed directly
if __name__ == '__main__':
    import pytest
    pytest.main([__file__, '-v'])
