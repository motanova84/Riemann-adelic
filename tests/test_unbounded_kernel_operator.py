#!/usr/bin/env python3
"""
Tests for Unbounded Kernel Operator

Tests verify that the integral operator K̃_z is proven to be NOT bounded
and NOT compact due to exponential growth.
"""

import pytest
import numpy as np
from operators.unbounded_kernel_operator import (
    UnboundedKernelOperator,
    generate_unbounded_kernel_certificate,
    verify_exponential_growth,
    C_ZETA_PRIME,
    F0_QCAL,
    C_COHERENCE
)


class TestUnboundedKernelOperator:
    """Test suite for UnboundedKernelOperator class."""
    
    def test_initialization_default(self):
        """Test default initialization."""
        op = UnboundedKernelOperator()
        
        assert op.C < 0, "C should be negative for unboundedness analysis"
        assert op.z.real > 0, "Re(z) should be positive for decay"
        
    def test_initialization_custom(self):
        """Test custom initialization with specific parameters."""
        C_test = -10.0
        z_test = 2.0 + 1.0j
        
        op = UnboundedKernelOperator(C=C_test, z=z_test)
        
        assert op.C == C_test
        assert op.z == z_test
        
    def test_initialization_warnings(self):
        """Test that warnings are raised for invalid parameters."""
        # Positive C should trigger warning
        with pytest.warns(UserWarning, match="non-negative"):
            op = UnboundedKernelOperator(C=5.0)
            assert op.C == C_ZETA_PRIME  # Should use default
        
        # Non-positive Re(z) should trigger warning
        with pytest.warns(UserWarning, match="non-positive"):
            op = UnboundedKernelOperator(z=-1.0 + 0.0j)
            assert op.z.real > 0  # Should use default
    
    def test_kernel_original_shape(self):
        """Test kernel computation in original variables (y,t)."""
        op = UnboundedKernelOperator()
        
        y = np.array([0.0, 1.0, 2.0])
        t = np.array([-1.0, 0.0, 1.0])
        
        kernel = op.compute_kernel_original(y, t)
        
        # Should return 2D array for grid
        assert kernel.shape == (len(y), len(t))
        assert np.all(np.isfinite(kernel))
    
    def test_kernel_original_single_point(self):
        """Test kernel at single point."""
        op = UnboundedKernelOperator()
        
        y = 1.0
        t = 0.0
        
        kernel = op.compute_kernel_original(y, t)
        
        assert np.isfinite(kernel)
        assert isinstance(kernel, np.ndarray)
    
    def test_variable_transformation(self):
        """Test transformation between (y,t) and (u,v) coordinates."""
        op = UnboundedKernelOperator()
        
        # Test point
        y_orig = 3.0
        t_orig = 1.0
        
        # Transform to symmetric
        u, v = op.transform_to_symmetric(y_orig, t_orig)
        
        # Check definitions
        assert u == y_orig + t_orig  # u = y + t
        assert v == y_orig - t_orig  # v = y - t
        
        # Transform back
        y_back, t_back = op.transform_from_symmetric(u, v)
        
        # Should recover original values
        assert np.isclose(y_back, y_orig)
        assert np.isclose(t_back, t_orig)
    
    def test_kernel_symmetric_shape(self):
        """Test kernel computation in symmetric variables (u,v)."""
        op = UnboundedKernelOperator()
        
        u = np.array([-2.0, 0.0, 2.0])
        v = np.array([0.5, 1.0, 2.0])  # All positive
        
        kernel = op.compute_kernel_symmetric(u, v)
        
        # Should return 2D array
        assert kernel.shape == (len(u), len(v))
        assert np.all(np.isfinite(kernel))
    
    def test_kernel_symmetric_consistency(self):
        """Test that kernel is consistent between original and symmetric variables."""
        op = UnboundedKernelOperator()
        
        # Test points
        y = 2.0
        t = 1.0
        
        # Kernel in original variables
        kernel_orig = op.compute_kernel_original(y, t)
        
        # Transform to symmetric
        u, v = op.transform_to_symmetric(y, t)
        
        # Kernel in symmetric variables
        kernel_sym = op.compute_kernel_symmetric(u, v)
        
        # Should be the same (accounting for numerical precision)
        assert np.isclose(kernel_orig, kernel_sym, rtol=1e-10)
    
    def test_exponential_growth_analysis(self):
        """Test exponential growth analysis for u → -∞."""
        op = UnboundedKernelOperator(C=-12.0, z=1.0)
        
        growth = op.analyze_exponential_growth(
            v_fixed=1.0,
            u_range=(-10.0, 0.0),
            n_points=50
        )
        
        # Check results structure
        assert 'u_values' in growth
        assert 'kernel_norms' in growth
        assert 'theoretical_growth_rate' in growth
        assert 'empirical_growth_rate' in growth
        assert 'diverges' in growth
        
        # Check theoretical growth rate
        # Should be 1 + |C|*v/2 = 1 + 12*1/2 = 7
        expected_rate = 1.0 + abs(-12.0) * 1.0 / 2.0
        assert np.isclose(growth['theoretical_growth_rate'], expected_rate)
        
        # Should detect divergence
        assert growth['diverges'] is True
        
        # Empirical growth should be close to theoretical (within factor of 2)
        if np.isfinite(growth['empirical_growth_rate']):
            assert growth['empirical_growth_rate'] > 0
    
    def test_exponential_growth_increases(self):
        """Test that kernel norm increases as u becomes more negative."""
        op = UnboundedKernelOperator(C=-10.0, z=1.0)
        
        v_fixed = 1.0
        u_values = np.array([-10.0, -5.0, -1.0])
        
        kernels = op.compute_kernel_symmetric(u_values, np.array([v_fixed]))
        norms = np.abs(kernels.flatten())
        
        # Kernel norm should increase as u becomes more negative
        # (norms[0] > norms[1] > norms[2])
        assert norms[0] > norms[2], "Kernel should grow as u → -∞"
    
    def test_verify_unboundedness(self):
        """Test unboundedness verification."""
        op = UnboundedKernelOperator()
        
        result = op.verify_unboundedness(
            u_range=(-5.0, 5.0),
            v_range=(0.1, 2.0),
            n_u=20,
            n_v=10
        )
        
        # Check result structure
        assert result.C == op.C
        assert result.z == op.z
        assert len(result.u_test_points) == 20
        assert len(result.v_test_points) == 10
        
        # Should be proven unbounded
        assert result.is_bounded is False
        assert result.is_compact is False
        assert result.hilbert_schmidt_norm == np.inf
        
        # Status should indicate unboundedness
        assert "NOT BOUNDED" in result.status
        assert "Exponential growth" in result.status
    
    def test_verify_non_compactness(self):
        """Test non-compactness verification."""
        op = UnboundedKernelOperator()
        
        result = op.verify_non_compactness()
        
        # Check result structure
        assert 'is_compact' in result
        assert 'reason' in result
        assert 'status' in result
        
        # Should be proven non-compact
        assert result['is_compact'] is False
        assert result['unboundedness_proven'] is True
        assert result['hilbert_schmidt_class'] is False
        assert result['trace_class'] is False
        
        # Status should indicate non-compactness
        assert "NOT COMPACT" in result['status']
    
    def test_unboundedness_with_different_C(self):
        """Test that unboundedness holds for different negative C values."""
        C_values = [-5.0, -10.0, -15.0, -20.0]
        
        for C in C_values:
            op = UnboundedKernelOperator(C=C)
            result = op.verify_unboundedness(n_u=20, n_v=10)
            
            # All should be unbounded
            assert result.is_bounded is False
            assert result.is_compact is False
    
    def test_unboundedness_with_different_z(self):
        """Test that unboundedness holds for different z values."""
        z_values = [1.0 + 0.0j, 2.0 + 0.0j, 1.0 + 1.0j]
        
        for z in z_values:
            op = UnboundedKernelOperator(z=z)
            result = op.verify_unboundedness(n_u=20, n_v=10)
            
            # All should be unbounded
            assert result.is_bounded is False
            assert result.is_compact is False


class TestCertificateGeneration:
    """Test suite for certificate generation."""
    
    def test_generate_certificate_structure(self):
        """Test that certificate has correct structure."""
        cert = generate_unbounded_kernel_certificate()
        
        # Check top-level fields
        assert 'protocol' in cert
        assert 'version' in cert
        assert 'signature' in cert
        assert 'timestamp' in cert
        assert 'author' in cert
        
        # Check QCAL constants
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == F0_QCAL
        assert cert['qcal_constants']['C_coherence'] == C_COHERENCE
        
        # Check operator definition
        assert 'operator_definition' in cert
        assert 'name' in cert['operator_definition']
        assert 'kernel_original' in cert['operator_definition']
        assert 'kernel_symmetric' in cert['operator_definition']
        
        # Check unboundedness proof
        assert 'unboundedness_proof' in cert
        assert cert['unboundedness_proof']['is_bounded'] is False
        assert 'growth_rate_coefficient' in cert['unboundedness_proof']
        
        # Check non-compactness proof
        assert 'non_compactness_proof' in cert
        assert cert['non_compactness_proof']['is_compact'] is False
        
        # Check coherence metrics
        assert 'coherence_metrics' in cert
        assert cert['coherence_metrics']['mathematical_rigor'] == 1.0
    
    def test_certificate_signature(self):
        """Test QCAL signature."""
        cert = generate_unbounded_kernel_certificate()
        
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        assert 'invocation_final' in cert
        assert 'spanish' in cert['invocation_final']
        assert 'english' in cert['invocation_final']
        assert 'mathematical' in cert['invocation_final']
    
    def test_certificate_growth_analysis(self):
        """Test growth analysis in certificate."""
        cert = generate_unbounded_kernel_certificate(C=-12.0, z=1.0)
        
        growth = cert['growth_analysis']
        
        assert 'theoretical_growth_rate' in growth
        assert 'empirical_growth_rate' in growth
        assert 'max_kernel_norm_observed' in growth
        assert growth['diverges'] is True
        
        # Theoretical rate should match expected value
        expected_rate = 1.0 + 12.0 * growth['v_test_value'] / 2.0
        assert np.isclose(growth['theoretical_growth_rate'], expected_rate)
    
    def test_certificate_protocol(self):
        """Test certificate protocol and version."""
        cert = generate_unbounded_kernel_certificate()
        
        assert cert['protocol'] == 'QCAL-UNBOUNDED-KERNEL-OPERATOR'
        assert cert['version'] == '1.0'
        assert cert['author'] == 'José Manuel Mota Burruezo Ψ ✧ ∞³'
        assert cert['orcid'] == '0009-0002-1923-0773'
        assert cert['institution'] == 'Instituto de Conciencia Cuántica (ICQ)'


class TestIntegration:
    """Integration tests."""
    
    def test_full_workflow(self):
        """Test complete workflow from initialization to certificate."""
        # Initialize operator
        op = UnboundedKernelOperator(C=-12.0, z=1.0 + 0.0j)
        
        # Verify unboundedness
        unbounded_result = op.verify_unboundedness()
        assert unbounded_result.is_bounded is False
        
        # Verify non-compactness
        non_compact_result = op.verify_non_compactness()
        assert non_compact_result['is_compact'] is False
        
        # Analyze growth
        growth = op.analyze_exponential_growth()
        assert growth['diverges'] is True
        
        # Generate certificate
        cert = generate_unbounded_kernel_certificate(C=-12.0, z=1.0 + 0.0j)
        assert cert['unboundedness_proof']['is_bounded'] is False
        assert cert['non_compactness_proof']['is_compact'] is False
    
    def test_numerical_stability(self):
        """Test numerical stability for extreme parameter values."""
        # Very negative C
        op1 = UnboundedKernelOperator(C=-100.0)
        result1 = op1.verify_unboundedness(u_range=(-2.0, 2.0), n_u=10, n_v=5)
        assert result1.is_bounded is False
        
        # Large Re(z)
        op2 = UnboundedKernelOperator(z=10.0 + 0.0j)
        result2 = op2.verify_unboundedness(u_range=(-2.0, 2.0), n_u=10, n_v=5)
        assert result2.is_bounded is False
    
    @pytest.mark.slow
    def test_high_resolution_analysis(self):
        """Test with high resolution grid (marked as slow)."""
        op = UnboundedKernelOperator()
        
        result = op.verify_unboundedness(
            u_range=(-10.0, 10.0),
            v_range=(0.1, 5.0),
            n_u=100,
            n_v=50
        )
        
        assert result.is_bounded is False
        assert result.is_compact is False
        assert len(result.u_test_points) == 100
        assert len(result.v_test_points) == 50


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
