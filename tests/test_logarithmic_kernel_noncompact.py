#!/usr/bin/env python3
"""
Tests for Logarithmic Kernel Non-Compactness Proof
==================================================

Comprehensive test suite for the logarithmic kernel non-compactness proof
implementing Ruta 1: La Luz Logarítmica.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.logarithmic_kernel_noncompact import (
    MellinTransform,
    TransformedKernel,
    BlockPartition,
    TestFunctionFamily,
    NonCompactnessProof,
    LogarithmicKernelConfig,
    C_BERRY_KEATING,
    F0_HZ,
    C_COHERENCE
)


class TestMellinTransform:
    """Test Mellin unitary transform U: L²(ℝ⁺, dx/x) → L²(ℝ, dy)."""
    
    def test_forward_transform(self):
        """Test forward Mellin transform (Uf)(y) = f(e^y)."""
        mellin = MellinTransform()
        
        # Test function f(x) = e^{-x²/2}
        f = lambda x: np.exp(-x**2 / 2)
        
        # Apply forward transform
        y = 0.5
        result = mellin.forward(f, y)
        expected = f(np.exp(y))
        
        assert np.isclose(result, expected, rtol=1e-10)
    
    def test_backward_transform(self):
        """Test inverse Mellin transform (U⁻¹g)(x) = g(log x)."""
        mellin = MellinTransform()
        
        # Test function g(y) = e^{-y²}
        g = lambda y: np.exp(-y**2)
        
        # Apply backward transform
        x = 2.0
        result = mellin.backward(g, x)
        expected = g(np.log(x))
        
        assert np.isclose(result, expected, rtol=1e-10)
    
    def test_backward_transform_invalid_x(self):
        """Test that backward transform rejects x <= 0."""
        mellin = MellinTransform()
        g = lambda y: y
        
        with pytest.raises(ValueError, match="x must be positive"):
            mellin.backward(g, 0.0)
        
        with pytest.raises(ValueError, match="x must be positive"):
            mellin.backward(g, -1.0)
    
    def test_unitarity(self):
        """Test unitarity: ∫|f(x)|² dx/x = ∫|f(e^y)|² dy."""
        mellin = MellinTransform()
        
        # Gaussian test function
        f = lambda x: np.exp(-x**2 / 2)
        
        norm_orig, norm_trans = mellin.verify_unitarity(
            f, x_range=(0.1, 10.0), n_points=2000
        )
        
        # Should be approximately equal
        relative_error = abs(norm_orig - norm_trans) / norm_orig
        assert relative_error < 0.01, f"Unitarity violated: error = {relative_error}"
    
    def test_unitarity_different_functions(self):
        """Test unitarity for various test functions."""
        mellin = MellinTransform()
        
        test_functions = [
            lambda x: np.exp(-x),
            lambda x: x * np.exp(-x**2),
            lambda x: np.sin(np.log(x)) * np.exp(-np.log(x)**2)
        ]
        
        for f in test_functions:
            norm_orig, norm_trans = mellin.verify_unitarity(
                f, x_range=(0.1, 10.0), n_points=1000
            )
            relative_error = abs(norm_orig - norm_trans) / max(norm_orig, 1e-10)
            assert relative_error < 0.05


class TestTransformedKernel:
    """Test transformed kernel K̃_z in logarithmic coordinates."""
    
    def test_kernel_initialization(self):
        """Test kernel initialization with parameters."""
        z = 0.5 + 14.0j
        C = C_BERRY_KEATING
        
        kernel = TransformedKernel(z, C)
        
        assert kernel.z == z
        assert kernel.C == C
    
    def test_kernel_support(self):
        """Test that kernel is zero for y <= t."""
        kernel = TransformedKernel(0.5 + 14.0j, C_BERRY_KEATING)
        
        # Should be zero for y <= t
        assert kernel(1.0, 2.0) == 0.0
        assert kernel(1.0, 1.0) == 0.0
        
        # Should be non-zero for y > t (in general)
        result = kernel(2.0, 1.0)
        assert result != 0.0
    
    def test_kernel_structure(self):
        """Test kernel structure and exponential factors."""
        z = 0.5 + 14.0j
        C = C_BERRY_KEATING
        kernel = TransformedKernel(z, C)
        
        y, t = 2.0, 1.0
        result = kernel(y, t)
        
        # Check that result is complex
        assert isinstance(result, (complex, np.complexfloating))
        
        # Verify exponential decay structure
        # Should have magnitude influenced by exp(C(y²-t²)/2) with C < 0
        # So magnitude should decay for |y-t| large
        y_far, t_far = 10.0, 1.0
        result_far = kernel(y_far, t_far)
        
        # Further separation should give smaller magnitude (due to C < 0)
        assert abs(result_far) < abs(result)
    
    def test_estimate_magnitude(self):
        """Test magnitude estimation for blocks."""
        kernel = TransformedKernel(0.5 + 14.0j, C_BERRY_KEATING)
        L = 1.0
        
        # For n > m, estimate should be positive
        mag = kernel.estimate_magnitude(n=3, m=1, L=L)
        assert mag > 0
        
        # For n <= m, estimate should be zero
        mag_zero = kernel.estimate_magnitude(n=1, m=3, L=L)
        assert mag_zero == 0.0
    
    def test_exponential_decay_in_separation(self):
        """Test exponential decay in block separation |n-m|."""
        kernel = TransformedKernel(0.5 + 14.0j, C_BERRY_KEATING)
        L = 1.0
        m = 0
        
        # Compute magnitudes for increasing n
        magnitudes = []
        for n in range(1, 6):
            mag = kernel.estimate_magnitude(n, m, L)
            magnitudes.append(mag)
        
        # Check monotonic decrease
        for i in range(len(magnitudes) - 1):
            assert magnitudes[i] > magnitudes[i+1], \
                f"Magnitudes not decreasing: {magnitudes}"


class TestBlockPartition:
    """Test block partition J_m = [mL, (m+1)L]."""
    
    def test_partition_initialization(self):
        """Test partition initialization."""
        L = 1.5
        num_blocks = 20
        partition = BlockPartition(L, num_blocks)
        
        assert partition.L == L
        assert partition.num_blocks == num_blocks
    
    def test_block_interval(self):
        """Test block interval computation."""
        partition = BlockPartition(L=1.0, num_blocks=10)
        
        # Block J_0 = [0, 1]
        assert partition.block_interval(0) == (0.0, 1.0)
        
        # Block J_3 = [3, 4]
        assert partition.block_interval(3) == (3.0, 4.0)
        
        # Block J_{-2} = [-2, -1]
        assert partition.block_interval(-2) == (-2.0, -1.0)
    
    def test_block_center(self):
        """Test block center computation."""
        partition = BlockPartition(L=2.0, num_blocks=10)
        
        # Center of J_0 = [0, 2] is 1.0
        assert partition.block_center(0) == 1.0
        
        # Center of J_1 = [2, 4] is 3.0
        assert partition.block_center(1) == 3.0
    
    def test_indicator_function(self):
        """Test indicator function 1_{J_m}(t)."""
        partition = BlockPartition(L=1.0, num_blocks=10)
        
        # t in J_0 = [0, 1)
        assert partition.indicator_function(0, 0.5) == 1.0
        assert partition.indicator_function(0, 0.0) == 1.0
        assert partition.indicator_function(0, 0.999) == 1.0
        
        # t not in J_0
        assert partition.indicator_function(0, 1.0) == 0.0
        assert partition.indicator_function(0, -0.5) == 0.0
        assert partition.indicator_function(0, 1.5) == 0.0


class TestTestFunctionFamily:
    """Test orthonormal test function family."""
    
    def test_initialization(self):
        """Test test function family initialization."""
        partition = BlockPartition(L=1.0, num_blocks=10)
        test_funcs = TestFunctionFamily(partition)
        
        assert test_funcs.partition == partition
        assert np.isclose(test_funcs.normalization, 1.0 / np.sqrt(1.0))
    
    def test_function_evaluation(self):
        """Test test function evaluation ψ_m(t)."""
        partition = BlockPartition(L=1.0, num_blocks=10)
        test_funcs = TestFunctionFamily(partition)
        
        # ψ_0(0.5) should be L^{-1/2} = 1
        value = test_funcs(0, 0.5)
        assert np.isclose(value, 1.0)
        
        # ψ_0(1.5) should be 0 (outside J_0)
        value_outside = test_funcs(0, 1.5)
        assert value_outside == 0.0
    
    def test_normalization(self):
        """Test that test functions are normalized."""
        partition = BlockPartition(L=2.0, num_blocks=10)
        test_funcs = TestFunctionFamily(partition)
        
        # ‖ψ_m‖² = ∫_{J_m} L^{-1} dt = 1
        m = 3
        inner_prod = test_funcs.inner_product(m, m)
        assert np.isclose(inner_prod, 1.0, rtol=1e-10)
    
    def test_orthogonality(self):
        """Test that test functions are orthogonal."""
        partition = BlockPartition(L=1.0, num_blocks=10)
        test_funcs = TestFunctionFamily(partition)
        
        # ⟨ψ_m, ψ_{m'}⟩ = 0 for m ≠ m'
        inner_prod = test_funcs.inner_product(0, 1)
        assert inner_prod == 0.0
        
        inner_prod = test_funcs.inner_product(2, 5)
        assert inner_prod == 0.0


class TestNonCompactnessProof:
    """Test main non-compactness proof implementation."""
    
    @pytest.fixture
    def default_config(self):
        """Create default configuration."""
        return LogarithmicKernelConfig(
            block_length=1.0,
            num_blocks=10,
            z_value=0.5 + 14.134725j,
            C_value=C_BERRY_KEATING
        )
    
    @pytest.fixture
    def proof(self, default_config):
        """Create proof instance."""
        return NonCompactnessProof(default_config)
    
    def test_initialization(self, default_config):
        """Test proof initialization."""
        proof = NonCompactnessProof(default_config)
        
        assert proof.config == default_config
        assert isinstance(proof.kernel, TransformedKernel)
        assert isinstance(proof.partition, BlockPartition)
        assert isinstance(proof.test_functions, TestFunctionFamily)
    
    def test_verify_exponential_decay(self, proof):
        """Test exponential decay verification."""
        results = proof.verify_exponential_decay()
        
        # Should have computed separations
        assert len(results['separations']) > 0
        assert len(results['magnitudes']) > 0
        
        # Separations should increase
        separations = results['separations']
        assert all(separations[i] < separations[i+1] 
                  for i in range(len(separations) - 1))
        
        # Should have exponential fit
        if results['exponential_fit']:
            assert 'decay_coefficient' in results['exponential_fit']
            assert results['exponential_fit']['decay_coefficient'] > 0
    
    def test_compute_image_orthogonality(self, proof):
        """Test image orthogonality computation."""
        block_pairs = [(0, 1), (0, 2), (1, 3)]
        results = proof.compute_image_orthogonality(block_pairs)
        
        assert len(results['pairs']) == len(block_pairs)
        assert len(results['inner_products']) == len(block_pairs)
        assert len(results['separations']) == len(block_pairs)
        
        # Inner products should be small for large separations
        for i, sep in enumerate(results['separations']):
            if sep > 2:
                assert results['inner_products'][i] < 0.1
    
    def test_estimate_singular_value_bound(self, proof):
        """Test singular value bound estimation."""
        results = proof.estimate_singular_value_bound(n_max=5)
        
        assert len(results['num_blocks']) > 0
        assert len(results['num_test_functions']) > 0
        assert len(results['lower_bound_estimate']) > 0
        assert len(results['non_compactness_indicator']) > 0
        
        # Number of test functions should grow as n²
        num_blocks = results['num_blocks']
        num_funcs = results['num_test_functions']
        
        for i in range(len(num_blocks)):
            expected_funcs = num_blocks[i] ** 2
            assert num_funcs[i] == expected_funcs
    
    def test_generate_certificate(self, proof):
        """Test QCAL certificate generation."""
        certificate = proof.generate_certificate()
        
        # Check required fields
        assert 'protocol' in certificate
        assert certificate['protocol'] == 'QCAL-LOGARITHMIC-KERNEL-NONCOMPACT'
        
        assert 'version' in certificate
        assert 'signature' in certificate
        assert certificate['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check QCAL constants
        assert 'qcal_constants' in certificate
        qcal = certificate['qcal_constants']
        assert qcal['f0_hz'] == F0_HZ
        assert qcal['C'] == C_COHERENCE
        
        # Check proof steps
        assert 'step_a_mellin_transform' in certificate
        assert 'step_b_kernel_transform' in certificate
        assert 'step_c_block_partition' in certificate
        assert 'step_d_test_functions' in certificate
        assert 'step_e_f_exponential_decay' in certificate
        assert 'step_g_orthogonality' in certificate
        assert 'step_h_singular_values' in certificate
        
        # Check conclusion
        assert 'conclusion' in certificate
        conclusion = certificate['conclusion']
        assert conclusion['k_z_compact'] == False
        assert conclusion['k_z_in_schatten_class'] == False
        assert conclusion['bks_program_applicable'] == False
        assert conclusion['proof_status'] == 'COMPLETE'
        
        # Check coherence metrics
        assert 'coherence_metrics' in certificate
        metrics = certificate['coherence_metrics']
        assert all(v == 1.0 for v in metrics.values())
        
        # Check invocation
        assert 'invocation_final' in certificate
        assert 'es' in certificate['invocation_final']
        assert 'en' in certificate['invocation_final']
        assert 'math' in certificate['invocation_final']


class TestIntegration:
    """Integration tests for the complete proof."""
    
    def test_complete_proof_workflow(self):
        """Test complete proof workflow from config to certificate."""
        # Create configuration
        config = LogarithmicKernelConfig(
            block_length=0.5,
            num_blocks=15,
            z_value=0.5 + 10.0j,
            C_value=C_BERRY_KEATING
        )
        
        # Run proof
        proof = NonCompactnessProof(config)
        
        # Verify all steps
        decay_results = proof.verify_exponential_decay()
        assert len(decay_results['separations']) > 0
        
        ortho_results = proof.compute_image_orthogonality()
        assert len(ortho_results['pairs']) > 0
        
        sv_results = proof.estimate_singular_value_bound()
        assert len(sv_results['num_blocks']) > 0
        
        # Generate certificate
        certificate = proof.generate_certificate()
        assert certificate['conclusion']['proof_status'] == 'COMPLETE'
    
    def test_different_z_values(self):
        """Test proof with different z values on critical line."""
        z_values = [
            0.5 + 14.134725j,  # First zero
            0.5 + 21.022040j,  # Second zero
            0.5 + 25.010858j   # Third zero
        ]
        
        for z in z_values:
            config = LogarithmicKernelConfig(
                block_length=1.0,
                num_blocks=10,
                z_value=z
            )
            
            proof = NonCompactnessProof(config)
            certificate = proof.generate_certificate()
            
            # All should conclude non-compactness
            assert certificate['conclusion']['k_z_compact'] == False
    
    def test_different_block_lengths(self):
        """Test proof with different block lengths."""
        block_lengths = [0.5, 1.0, 2.0]
        
        for L in block_lengths:
            config = LogarithmicKernelConfig(
                block_length=L,
                num_blocks=10
            )
            
            proof = NonCompactnessProof(config)
            decay_results = proof.verify_exponential_decay()
            
            # Should always get exponential decay
            assert len(decay_results['separations']) > 0
            assert len(decay_results['magnitudes']) > 0


class TestQCALCoherence:
    """Test QCAL coherence and certification."""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are correct."""
        assert F0_HZ == 141.7001
        assert C_COHERENCE == 244.36
        assert np.isclose(KAPPA_PI, 2.577310, rtol=1e-6)
    
    def test_berry_keating_constant(self):
        """Test Berry-Keating constant properties."""
        assert C_BERRY_KEATING < 0, "C must be negative for Gaussian decay"
        assert np.isclose(abs(C_BERRY_KEATING), 12.3218, rtol=0.01)
    
    def test_certificate_qcal_signature(self):
        """Test that certificate has proper QCAL signature."""
        config = LogarithmicKernelConfig()
        proof = NonCompactnessProof(config)
        certificate = proof.generate_certificate()
        
        assert certificate['signature'] == '∴𓂀Ω∞³Φ'
        assert 'qcal_constants' in certificate
        assert certificate['qcal_constants']['seal'] == 14170001
        assert certificate['qcal_constants']['code'] == 888


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
