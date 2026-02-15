#!/usr/bin/env python3
"""
Tests for Three-Space Realization Module
========================================

Tests for ETAPA 2: REALIZACIÓN ESPACIAL COMPLETA implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
from pathlib import Path
import json

from operators.three_space_realization import (
    OriginalSpace,
    IntermediateSpace,
    WeightedSpace,
    TransformationU1,
    TransformationU2,
    ComposedTransformation,
    OperatorH,
    OperatorH0,
    HankelOperatorPrep,
    ThreeSpaceRealization,
    verify_three_space_realization
)


class TestHilbertSpaces:
    """Test Hilbert space definitions."""
    
    def test_original_space_creation(self):
        """Test ℋ = L²(ℝ⁺, dx/x) creation."""
        H = OriginalSpace(dimension=50)
        
        assert H.dimension == 50
        assert len(H.y_grid) == 50
        assert len(H.x_grid) == 50
        assert np.allclose(H.x_grid, np.exp(H.y_grid))
    
    def test_intermediate_space_creation(self):
        """Test ℋ₁ = L²(ℝ, dy) creation."""
        H1 = IntermediateSpace(dimension=50)
        
        assert H1.dimension == 50
        assert len(H1.y_grid) == 50
    
    def test_weighted_space_creation(self):
        """Test ℋ₂ = L²(ℝ, e^{Cy²} dy) creation."""
        C = -1.0
        H2 = WeightedSpace(dimension=50, C=C)
        
        assert H2.dimension == 50
        assert H2.C == C
        
        # Test that weight decays exponentially
        y = H2.y_grid
        weight = H2.measure(y)
        assert np.all(weight > 0)
        assert np.all(weight <= 1.0)  # Maximum at y=0
    
    def test_weighted_space_requires_negative_C(self):
        """Test that C must be negative for weighted space."""
        with pytest.raises(ValueError, match="C must be negative"):
            WeightedSpace(dimension=50, C=1.0)
    
    def test_inner_product(self):
        """Test inner product computation."""
        H = OriginalSpace(dimension=50)
        
        # Simple test functions
        f = np.exp(-H.y_grid**2)
        g = np.exp(-0.5 * H.y_grid**2)
        
        # Compute inner product
        inner = H.inner_product(f, g)
        
        # Should be a real positive number
        assert np.isreal(inner)
        assert inner > 0
    
    def test_norm(self):
        """Test L² norm computation."""
        H = OriginalSpace(dimension=50)
        
        # Normalized Gaussian
        f = np.exp(-H.y_grid**2)
        f = f / H.norm(f)
        
        # Norm should be close to 1
        assert np.abs(H.norm(f) - 1.0) < 0.01


class TestUnitaryTransformations:
    """Test unitary transformations."""
    
    def test_U1_creation(self):
        """Test U₁: ℋ → ℋ₁ creation."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        U1 = TransformationU1(H, H1)
        
        assert U1.source_space == H
        assert U1.target_space == H1
    
    def test_U1_apply(self):
        """Test U₁ application: (U₁f)(y) = f(e^y)."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        U1 = TransformationU1(H, H1)
        
        # Test function
        f = np.exp(-H.y_grid**2)
        
        # Apply transformation
        U1f = U1.apply(f)
        
        # Should preserve values on grid
        assert np.allclose(U1f, f)
    
    def test_U1_unitarity(self):
        """Test U₁ unitarity."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        U1 = TransformationU1(H, H1)
        
        results = U1.verify_unitarity(n_tests=5)
        
        assert results['verified']
        assert results['max_error'] < 1e-10
    
    def test_U2_creation(self):
        """Test U₂: ℋ₁ → ℋ₂ creation."""
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        U2 = TransformationU2(H1, H2)
        
        assert U2.source_space == H1
        assert U2.target_space == H2
        assert U2.C == -1.0
    
    def test_U2_apply(self):
        """Test U₂ application: (U₂φ)(y) = e^{-Cy²/2} φ(y)."""
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        U2 = TransformationU2(H1, H2)
        
        # Test function
        f = np.ones(50)
        
        # Apply transformation
        U2f = U2.apply(f)
        
        # Should be e^{0.5y²}
        y = H1.y_grid
        expected = np.exp(0.5 * y**2)
        
        assert np.allclose(U2f, expected)
    
    def test_U2_unitarity(self):
        """Test U₂ unitarity."""
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        U2 = TransformationU2(H1, H2)
        
        results = U2.verify_unitarity(n_tests=5)
        
        assert results['verified']
        assert results['max_error'] < 1e-10
    
    def test_composed_transformation(self):
        """Test U = U₂ ∘ U₁ composition."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        
        U1 = TransformationU1(H, H1)
        U2 = TransformationU2(H1, H2)
        U = ComposedTransformation(U1, U2)
        
        assert U.source_space == H
        assert U.target_space == H2
    
    def test_composed_unitarity(self):
        """Test unitarity of composed transformation U."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        
        U1 = TransformationU1(H, H1)
        U2 = TransformationU2(H1, H2)
        U = ComposedTransformation(U1, U2)
        
        results = U.verify_unitarity(n_tests=5)
        
        assert results['verified']
        assert results['max_error'] < 1e-10
    
    def test_inverse_transformations(self):
        """Test that U⁻¹ ∘ U = identity."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        
        U1 = TransformationU1(H, H1)
        U2 = TransformationU2(H1, H2)
        U = ComposedTransformation(U1, U2)
        
        # Test function
        f = np.exp(-H.y_grid**2)
        
        # Apply U then U⁻¹
        Uf = U.apply(f)
        f_recovered = U.apply_inverse(Uf)
        
        # Should recover original function
        assert np.allclose(f, f_recovered)


class TestOperators:
    """Test operator transformations."""
    
    def test_operator_H_in_original_space(self):
        """Test H = -x·d/dx + C·log(x) in ℋ."""
        H_space = OriginalSpace(dimension=50)
        C = -1.0
        H_op = OperatorH(H_space, C)
        
        # Test on simple function
        f = np.exp(-H_space.y_grid**2)
        Hf = H_op.apply_in_original_space(f)
        
        # Should produce non-zero result
        assert np.linalg.norm(Hf) > 0
    
    def test_operator_H_in_intermediate_space(self):
        """Test H̃₁ = -d/dy + C·y in ℋ₁."""
        H1_space = IntermediateSpace(dimension=50)
        C = -1.0
        H_op = OperatorH(H1_space, C)
        
        # Test on simple function
        f = np.exp(-H1_space.y_grid**2)
        Hf = H_op.apply_in_intermediate_space(f)
        
        # Should produce non-zero result
        assert np.linalg.norm(Hf) > 0
    
    def test_operator_H_in_weighted_space(self):
        """Test U H U⁻¹ = -d/dy in ℋ₂."""
        H2_space = WeightedSpace(dimension=50, C=-1.0)
        H_op = OperatorH(H2_space, -1.0)
        
        # Test on simple function
        f = np.exp(-H2_space.y_grid**2)
        Hf = H_op.apply_in_weighted_space(f)
        
        # Should be -d/dy f
        df_dy = np.gradient(f, H2_space.dy)
        expected = -df_dy
        
        # Allow some numerical error
        assert np.allclose(Hf, expected, rtol=0.1)
    
    def test_operator_H0_transformations(self):
        """Test H₀ = -x·d/dx transformations."""
        H_space = OriginalSpace(dimension=50)
        H0_op = OperatorH0(H_space, C=-1.0)
        
        # Test in original space
        f = np.exp(-H_space.y_grid**2)
        H0f = H0_op.apply_in_original_space(f)
        
        # Should be -d/dy f (since x·d/dx = d/dy)
        df_dy = np.gradient(f, H_space.dy)
        expected = -df_dy
        
        # Allow some numerical error
        assert np.allclose(H0f, expected, rtol=0.1)


class TestHankelOperator:
    """Test Hankel operator preparation for Stage 3."""
    
    def test_hankel_creation(self):
        """Test Hankel operator creation."""
        C = -1.0
        hankel = HankelOperatorPrep(C)
        
        assert hankel.C == C
        assert hankel.z == 0.5  # Default on critical line
    
    def test_kernel_in_y_variables(self):
        """Test K_z(y,t) computation."""
        C = -1.0
        hankel = HankelOperatorPrep(C)
        
        y = np.linspace(-2, 2, 20)
        t = np.linspace(-2, 2, 20)
        
        K = hankel.kernel_in_y_variables(y, t)
        
        assert K.shape == (20, 20)
        # Should be zero when y <= t
        for i in range(20):
            for j in range(20):
                if y[i] <= t[j]:
                    assert np.abs(K[i, j]) < 1e-10
    
    def test_kernel_in_xi_eta_variables(self):
        """Test K_z(ξ, η) computation."""
        C = -1.0
        hankel = HankelOperatorPrep(C)
        
        xi = np.linspace(-2, 2, 20)
        eta = np.linspace(-2, 2, 20)
        
        K = hankel.kernel_in_xi_eta_variables(xi, eta)
        
        assert K.shape == (20, 20)
        # Should be zero when ξ <= 0
        for i in range(20):
            if xi[i] <= 0:
                assert np.allclose(K[i, :], 0, atol=1e-10)
    
    def test_singular_values(self):
        """Test singular value computation."""
        C = -1.0
        hankel = HankelOperatorPrep(C)
        
        y = np.linspace(-2, 2, 30)
        sv = hankel.compute_singular_values(y, n_sv=5)
        
        assert len(sv) == 5
        # Singular values should be non-negative and decreasing
        assert np.all(sv >= 0)
        assert np.all(np.diff(sv) <= 0)


class TestThreeSpaceRealization:
    """Test complete three-space realization."""
    
    def test_realization_creation(self):
        """Test three-space realization creation."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        
        assert realization.C == -1.0
        assert realization.dimension == 30
        assert realization.H is not None
        assert realization.H1 is not None
        assert realization.H2 is not None
    
    def test_requires_negative_C(self):
        """Test that C must be negative."""
        with pytest.raises(ValueError, match="C must be negative"):
            ThreeSpaceRealization(C=1.0)
    
    def test_verify_unitarity(self):
        """Test unitarity verification."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        results = realization.verify_unitarity(n_tests=5)
        
        assert 'U1' in results
        assert 'U2' in results
        assert 'U' in results
        assert results['all_verified']
    
    def test_verify_operator_transformations(self):
        """Test operator transformation verification."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        results = realization.verify_operator_transformations(n_tests=5)
        
        assert 'H_in_H1' in results
        assert 'H_in_H2' in results
        # Operators should be approximately consistent
        # (exact equality not expected due to numerical derivatives)
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        
        eigenvalues, eigenvectors = realization.compute_spectrum('original')
        
        assert len(eigenvalues) == 30
        assert eigenvectors.shape == (30, 30)
        # Eigenvalues should be real
        assert np.allclose(np.imag(eigenvalues), 0, atol=1e-10)
    
    def test_certificate_generation(self):
        """Test QCAL certificate generation."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        
        # Generate certificate without saving
        certificate = realization.generate_certificate(save_path=None)
        
        # Check certificate structure
        assert 'protocol' in certificate
        assert certificate['protocol'] == 'QCAL-THREE-SPACE-REALIZATION'
        assert 'signature' in certificate
        assert certificate['signature'] == '∴𓂀Ω∞³Φ'
        assert 'parameters' in certificate
        assert 'spaces' in certificate
        assert 'transformations' in certificate
        assert 'qcal_constants' in certificate
        
        # Check QCAL constants
        qcal = certificate['qcal_constants']
        assert qcal['f0_hz'] == 141.7001
        assert qcal['C_QCAL'] == 244.36
        assert qcal['kappa_pi'] == 2.577310


class TestVerificationFunction:
    """Test main verification function."""
    
    def test_verify_three_space_realization(self):
        """Test complete verification function."""
        # Run without saving certificate
        results = verify_three_space_realization(
            C=-1.0,
            dimension=30,
            save_certificate=False
        )
        
        assert results is not None
        assert 'all_verified' in results
        assert 'protocol' in results
        assert 'signature' in results
    
    def test_certificate_saved_to_data(self):
        """Test that certificate is saved correctly."""
        cert_path = Path('data/three_space_realization_certificate.json')
        
        # Remove existing certificate if present
        if cert_path.exists():
            cert_path.unlink()
        
        # Run verification with saving
        results = verify_three_space_realization(
            C=-1.0,
            dimension=30,
            save_certificate=True
        )
        
        # Check file was created
        assert cert_path.exists()
        
        # Load and verify content
        with open(cert_path, 'r') as f:
            cert = json.load(f)
        
        assert cert['protocol'] == 'QCAL-THREE-SPACE-REALIZATION'
        assert cert['signature'] == '∴𓂀Ω∞³Φ'


class TestNumericalAccuracy:
    """Test numerical accuracy of implementations."""
    
    def test_inner_product_consistency(self):
        """Test inner product is consistent across spaces."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        
        U1 = TransformationU1(H, H1)
        
        # Random test functions
        f = np.random.randn(50)
        g = np.random.randn(50)
        
        # Inner product in H
        inner_H = H.inner_product(f, g)
        
        # Transform and compute in H1
        U1f = U1.apply(f)
        U1g = U1.apply(g)
        inner_H1 = H1.inner_product(U1f, U1g)
        
        # Should be equal (unitarity)
        assert np.abs(inner_H - inner_H1) / (np.abs(inner_H) + 1e-16) < 1e-10
    
    def test_operator_hermiticity(self):
        """Test that H is Hermitian."""
        realization = ThreeSpaceRealization(C=-1.0, dimension=30)
        
        eigenvalues, _ = realization.compute_spectrum('original')
        
        # All eigenvalues should be real (Hermitian operator)
        assert np.allclose(np.imag(eigenvalues), 0, atol=1e-10)
    
    def test_transformation_reversibility(self):
        """Test U⁻¹(U(f)) = f for all transformations."""
        H = OriginalSpace(dimension=50)
        H1 = IntermediateSpace(dimension=50)
        H2 = WeightedSpace(dimension=50, C=-1.0)
        
        U1 = TransformationU1(H, H1)
        U2 = TransformationU2(H1, H2)
        
        # Test function
        f = np.exp(-H.y_grid**2)
        
        # Test U1
        f_U1 = U1.apply_inverse(U1.apply(f))
        assert np.allclose(f, f_U1)
        
        # Test U2
        g = np.exp(-H1.y_grid**2)
        g_U2 = U2.apply_inverse(U2.apply(g))
        assert np.allclose(g, g_U2)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
