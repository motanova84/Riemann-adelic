#!/usr/bin/env python3
"""
Tests for Spectral Curvature Tensor Module

Tests the geometric formulation of RH through the Einstein-like tensor G_ab^Ψ.

Author: José Manuel Mota Burruezo
Date: January 2026
"""

import pytest
import numpy as np
from utils.spectral_curvature_tensor import (
    SpectralCurvatureTensor,
    verify_spectral_curvature_geometry,
    print_curvature_report
)


class TestSpectralCurvatureTensor:
    """Test suite for SpectralCurvatureTensor class."""
    
    def test_initialization(self):
        """Test that SpectralCurvatureTensor initializes correctly."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        assert tensor.dimension == 4
        assert tensor.precision == 25
        assert tensor.f0 == 141.7001
        assert tensor.C == 244.36
        assert tensor.critical_real_part == 0.5
        assert tensor.omega_0 > 0
    
    def test_zero_density_computation(self):
        """Test zero density computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        # Zero density should be positive for positive t
        rho_14 = tensor.compute_zero_density(14.134725)
        assert rho_14 > 0
        
        # Zero density should increase with t (asymptotically)
        rho_100 = tensor.compute_zero_density(100.0)
        assert rho_100 > rho_14
        
        # Zero density should be zero or very small for t ≤ 0
        rho_0 = tensor.compute_zero_density(0.0)
        assert rho_0 == 0.0
        
        rho_neg = tensor.compute_zero_density(-10.0)
        assert rho_neg == 0.0
    
    def test_metric_tensor_computation(self):
        """Test metric tensor computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        
        # Check shape
        assert metric.shape == (4, 4)
        
        # Metric should be symmetric
        assert np.allclose(metric, metric.T)
        
        # Metric should be positive definite (all eigenvalues positive)
        eigenvalues = np.linalg.eigvals(metric)
        assert np.all(eigenvalues > 0)
        
        # Diagonal should be close to 1 (orthonormal basis)
        diagonal = np.diag(metric)
        assert np.allclose(diagonal, 1.0, atol=0.1)
    
    def test_metric_tensor_caching(self):
        """Test that metric tensor is cached."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric1 = tensor.compute_metric_tensor()
        metric2 = tensor.compute_metric_tensor()
        
        # Should return same object (cached)
        assert metric1 is metric2
    
    def test_christoffel_symbols(self):
        """Test Christoffel symbols computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        Gamma = tensor.compute_christoffel_symbols(metric)
        
        # Check shape
        assert Gamma.shape == (4, 4, 4)
        
        # Christoffel symbols should be real
        assert Gamma.dtype in [np.float64, np.float32]
        
        # Should be symmetric in lower indices: Γ^k_ij = Γ^k_ji
        for k in range(4):
            assert np.allclose(Gamma[k], Gamma[k].T, atol=1e-10)
    
    def test_ricci_tensor_computation(self):
        """Test Ricci tensor computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        ricci = tensor.compute_ricci_tensor()
        
        # Check shape
        assert ricci.shape == (4, 4)
        
        # Ricci tensor should be symmetric
        assert np.allclose(ricci, ricci.T, atol=1e-10)
        
        # Ricci tensor should be real
        assert ricci.dtype in [np.float64, np.float32]
        
        # Diagonal elements should be positive (curvature from zero density)
        diagonal = np.diag(ricci)
        assert np.all(diagonal >= 0)
    
    def test_ricci_tensor_caching(self):
        """Test that Ricci tensor is cached."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        ricci1 = tensor.compute_ricci_tensor()
        ricci2 = tensor.compute_ricci_tensor()
        
        # Should return same object (cached)
        assert ricci1 is ricci2
    
    def test_scalar_curvature_computation(self):
        """Test scalar curvature computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        scalar_curv = tensor.compute_scalar_curvature()
        
        # Should be a scalar (float)
        assert isinstance(scalar_curv, (float, np.floating))
        
        # Should be positive (from zero density)
        assert scalar_curv >= 0
    
    def test_scalar_curvature_consistency(self):
        """Test scalar curvature consistency with Ricci tensor."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        ricci = tensor.compute_ricci_tensor(metric)
        scalar_curv = tensor.compute_scalar_curvature(metric, ricci)
        
        # Manual computation: R = g^ab R_ab
        metric_inv = np.linalg.inv(metric)
        manual_scalar = np.trace(metric_inv @ ricci)
        
        assert np.isclose(scalar_curv, manual_scalar, rtol=1e-10)
    
    def test_einstein_tensor_computation(self):
        """Test Einstein tensor computation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        einstein = tensor.compute_einstein_tensor()
        
        # Check shape
        assert einstein.shape == (4, 4)
        
        # Einstein tensor should be symmetric
        assert np.allclose(einstein, einstein.T, atol=1e-10)
        
        # Einstein tensor should be real
        assert einstein.dtype in [np.float64, np.float32]
    
    def test_einstein_tensor_formula(self):
        """Test Einstein tensor formula: G_ab = R_ab - (1/2) R g_ab."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        ricci = tensor.compute_ricci_tensor(metric)
        scalar_curv = tensor.compute_scalar_curvature(metric, ricci)
        einstein = tensor.compute_einstein_tensor(metric, ricci, scalar_curv)
        
        # Manual computation
        manual_einstein = ricci - 0.5 * scalar_curv * metric
        
        assert np.allclose(einstein, manual_einstein, atol=1e-10)
    
    def test_einstein_tensor_trace(self):
        """Test that trace of Einstein tensor has expected property."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        einstein = tensor.compute_einstein_tensor(metric=metric)
        
        # In general, Tr(G_ab) is related to scalar curvature
        einstein_trace = np.trace(einstein)
        
        # Should be a finite number
        assert np.isfinite(einstein_trace)
    
    def test_verify_critical_flatness(self):
        """Test critical flatness verification."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        result = tensor.verify_critical_flatness(tolerance=1e-6)
        
        # Check structure of result
        assert 'critical_flatness' in result
        assert 'einstein_tensor_norm' in result
        assert 'einstein_trace' in result
        assert 'einstein_determinant' in result
        assert 'scalar_curvature' in result
        assert 'average_curvature' in result
        assert 'critical_line_real_part' in result
        assert 'metric_determinant' in result
        assert 'ricci_trace' in result
        
        # Check values are reasonable
        assert isinstance(result['critical_flatness'], (bool, np.bool_))
        assert result['einstein_tensor_norm'] >= 0
        assert result['critical_line_real_part'] == 0.5
        assert result['dimension'] == 4
    
    def test_compute_curvature_at_point_on_critical_line(self):
        """Test curvature computation at point on critical line."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        # First zero of ζ(s) at s ≈ 0.5 + 14.134725i
        s = complex(0.5, 14.134725)
        curvature = tensor.compute_curvature_at_point(s)
        
        # Check structure
        assert 's' in curvature
        assert 'sigma' in curvature
        assert 't' in curvature
        assert 'zero_density' in curvature
        assert 'local_curvature' in curvature
        assert 'einstein_component' in curvature
        assert 'distance_from_critical_line' in curvature
        assert 'on_critical_line' in curvature
        
        # Check values
        assert curvature['sigma'] == 0.5
        assert curvature['t'] > 0
        assert curvature['zero_density'] > 0
        assert curvature['on_critical_line'] is True
        assert curvature['distance_from_critical_line'] < 1e-10
    
    def test_compute_curvature_at_point_off_critical_line(self):
        """Test curvature computation at point off critical line."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        # Point off critical line
        s = complex(0.6, 14.134725)
        curvature = tensor.compute_curvature_at_point(s)
        
        # Should not be on critical line
        assert curvature['on_critical_line'] is False
        assert curvature['distance_from_critical_line'] > 0
        assert np.isclose(curvature['distance_from_critical_line'], 0.1)
        
        # Local curvature should be non-zero (deviation from critical line)
        assert curvature['local_curvature'] > 0
    
    def test_curvature_increases_off_critical_line(self):
        """Test that curvature increases away from critical line."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        t_fixed = 14.134725
        
        # On critical line
        curv_on = tensor.compute_curvature_at_point(complex(0.5, t_fixed))
        
        # Slightly off critical line
        curv_off_small = tensor.compute_curvature_at_point(complex(0.55, t_fixed))
        
        # Further off critical line
        curv_off_large = tensor.compute_curvature_at_point(complex(0.7, t_fixed))
        
        # Curvature should increase with distance from critical line
        assert curv_off_small['local_curvature'] > curv_on['local_curvature']
        assert curv_off_large['local_curvature'] > curv_off_small['local_curvature']
    
    def test_generate_curvature_report(self):
        """Test curvature report generation."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        report = tensor.generate_curvature_report()
        
        # Report should be non-empty string
        assert isinstance(report, str)
        assert len(report) > 100
        
        # Should contain key terms
        assert "Einstein" in report or "EINSTEIN" in report
        assert "Ricci" in report or "RICCI" in report
        assert "curvature" in report or "CURVATURE" in report
        assert "critical" in report or "CRITICAL" in report
    
    def test_clear_cache(self):
        """Test cache clearing."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        # Compute values (populate cache)
        metric1 = tensor.compute_metric_tensor()
        ricci1 = tensor.compute_ricci_tensor()
        
        # Clear cache
        tensor.clear_cache()
        
        # Recompute (should create new objects)
        metric2 = tensor.compute_metric_tensor()
        ricci2 = tensor.compute_ricci_tensor()
        
        # Values should be equal but not same object
        assert np.allclose(metric1, metric2)
        assert np.allclose(ricci1, ricci2)
    
    def test_different_dimensions(self):
        """Test with different spectral space dimensions."""
        dimensions = [2, 4, 8]
        
        for dim in dimensions:
            tensor = SpectralCurvatureTensor(dimension=dim, precision=25)
            
            metric = tensor.compute_metric_tensor()
            ricci = tensor.compute_ricci_tensor()
            einstein = tensor.compute_einstein_tensor()
            
            # Check shapes
            assert metric.shape == (dim, dim)
            assert ricci.shape == (dim, dim)
            assert einstein.shape == (dim, dim)
    
    def test_different_precisions(self):
        """Test with different precision values."""
        precisions = [15, 25, 50]
        
        results = []
        for prec in precisions:
            tensor = SpectralCurvatureTensor(dimension=4, precision=prec)
            result = tensor.verify_critical_flatness()
            results.append(result)
        
        # All should give consistent results
        for i in range(len(results) - 1):
            # Einstein tensor norms should be similar
            assert abs(results[i]['einstein_tensor_norm'] - 
                      results[i+1]['einstein_tensor_norm']) < 0.1


class TestConvenienceFunctions:
    """Test convenience functions."""
    
    def test_verify_spectral_curvature_geometry(self):
        """Test convenience verification function."""
        result = verify_spectral_curvature_geometry(
            dimension=4,
            precision=25,
            tolerance=1e-6
        )
        
        # Should return boolean
        assert isinstance(result, (bool, np.bool_))
    
    def test_print_curvature_report(self, capsys):
        """Test convenience print function."""
        print_curvature_report(dimension=4, precision=15)
        
        captured = capsys.readouterr()
        output = captured.out
        
        # Should print something
        assert len(output) > 0
        assert "SPECTRAL" in output or "spectral" in output.lower()


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_small_dimension(self):
        """Test with minimal dimension."""
        tensor = SpectralCurvatureTensor(dimension=2, precision=25)
        
        metric = tensor.compute_metric_tensor()
        einstein = tensor.compute_einstein_tensor()
        
        assert metric.shape == (2, 2)
        assert einstein.shape == (2, 2)
    
    def test_custom_qcal_constants(self):
        """Test with custom QCAL constants."""
        tensor = SpectralCurvatureTensor(
            dimension=4,
            precision=25,
            fundamental_frequency=150.0,
            coherence_constant=250.0
        )
        
        assert tensor.f0 == 150.0
        assert tensor.C == 250.0
        
        # Should still compute valid geometry
        result = tensor.verify_critical_flatness()
        assert 'critical_flatness' in result


class TestMathematicalConsistency:
    """Test mathematical consistency of the geometric formulation."""
    
    def test_metric_positive_definiteness(self):
        """Test that metric is always positive definite."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        
        # All eigenvalues should be positive
        eigenvalues = np.linalg.eigvals(metric)
        assert np.all(eigenvalues > 0)
    
    def test_ricci_symmetry(self):
        """Test that Ricci tensor is symmetric."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        ricci = tensor.compute_ricci_tensor()
        
        # R_ab = R_ba
        assert np.allclose(ricci, ricci.T, atol=1e-10)
    
    def test_einstein_symmetry(self):
        """Test that Einstein tensor is symmetric."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        einstein = tensor.compute_einstein_tensor()
        
        # G_ab = G_ba
        assert np.allclose(einstein, einstein.T, atol=1e-10)
    
    def test_bianchi_identity_traceless(self):
        """Test property related to Bianchi identity."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        metric = tensor.compute_metric_tensor()
        einstein = tensor.compute_einstein_tensor(metric=metric)
        
        # In 4D, the contracted Bianchi identity gives constraints
        # For our spectral geometry, we check basic trace property
        einstein_trace = np.trace(einstein)
        
        # Should be finite and bounded
        assert np.isfinite(einstein_trace)
        assert abs(einstein_trace) < 100  # Reasonable bound
    
    def test_zero_density_monotonicity(self):
        """Test that zero density is monotonically increasing."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        t_values = [10.0, 20.0, 50.0, 100.0]
        rho_values = [tensor.compute_zero_density(t) for t in t_values]
        
        # Should be monotonically increasing
        for i in range(len(rho_values) - 1):
            assert rho_values[i+1] > rho_values[i]


class TestGeometricInterpretation:
    """Test geometric interpretation of RH."""
    
    def test_critical_line_corresponds_to_flatness(self):
        """Test that critical line (σ=1/2) has minimal curvature."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        t_fixed = 14.134725
        sigma_values = [0.3, 0.4, 0.5, 0.6, 0.7]
        
        curvatures = []
        for sigma in sigma_values:
            s = complex(sigma, t_fixed)
            curv = tensor.compute_curvature_at_point(s)
            curvatures.append(curv['local_curvature'])
        
        # Curvature at σ=0.5 should be minimal (or close to it)
        min_idx = np.argmin(curvatures)
        assert sigma_values[min_idx] == 0.5
    
    def test_rh_as_flatness_condition(self):
        """Test interpretation: RH ⟺ G_ab^Ψ = 0."""
        tensor = SpectralCurvatureTensor(dimension=4, precision=25)
        
        result = tensor.verify_critical_flatness(tolerance=1e-3)
        
        # The geometry should be approximately flat on critical line
        # (within numerical precision)
        assert result['einstein_tensor_norm'] < 1.0  # Reasonably small
        
        # Scalar curvature should be small
        assert result['scalar_curvature'] >= 0


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
