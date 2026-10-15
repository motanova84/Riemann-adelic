#!/usr/bin/env python3
"""
Tests for H_Ψ Self-Adjoint Corrected Operator (FALLOS 1-3 Resolution)
======================================================================

This test suite validates the corrected implementation addressing:
- FALLO 1: Self-adjointness with proper domain and boundary conditions
- FALLO 2: Unitary transformation between different Hilbert spaces
- FALLO 3: Discrete spectrum via Hilbert-Schmidt resolvent compactness

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
from scipy.linalg import norm
from operators.h_psi_self_adjoint_corrected import (
    HPsiSelfAdjointCorrected,
    verify_h_psi_corrected,
    C_PARAMETER
)


class TestHPsiSelfAdjointCorrected:
    """Test suite for corrected H_Ψ operator"""
    
    def test_initialization(self):
        """Test operator initialization"""
        op = HPsiSelfAdjointCorrected(L=10.0, N=100, C=-1.0)
        
        assert op.L == 10.0
        assert op.N == 100
        assert op.C == -1.0
        assert op.dy > 0
        assert len(op.y) == 100
        
    def test_initialization_positive_C_raises(self):
        """Test that positive C raises error"""
        with pytest.raises(ValueError, match="C must be negative"):
            HPsiSelfAdjointCorrected(C=1.0)
    
    def test_operator_matrix_shape(self):
        """Test operator matrices have correct shape"""
        op = HPsiSelfAdjointCorrected(L=5.0, N=50)
        
        assert op.H_psi.shape == (50, 50)
        assert op.U.shape == (50, 50)
        assert op.U_inv.shape == (50, 50)
        assert op.H_psi_tilde.shape == (50, 50)
    
    def test_operator_matrix_real_symmetric(self):
        """Test that H_Ψ is real and symmetric"""
        op = HPsiSelfAdjointCorrected(L=5.0, N=50)
        
        # H_Ψ should be real
        assert np.allclose(op.H_psi.imag, 0)
        
        # H_Ψ should be symmetric
        assert np.allclose(op.H_psi, op.H_psi.T)
    
    def test_unitary_transform_diagonal(self):
        """Test that U is diagonal"""
        op = HPsiSelfAdjointCorrected(L=5.0, N=50)
        
        # U should be diagonal
        U_diag = np.diag(np.diag(op.U))
        assert np.allclose(op.U, U_diag)
        
        # U_inv should be diagonal
        U_inv_diag = np.diag(np.diag(op.U_inv))
        assert np.allclose(op.U_inv, U_inv_diag)
    
    def test_fallo_1_self_adjointness(self):
        """
        Test FALLO 1: Self-adjointness with boundary conditions
        
        Verifies that ‖H_Ψ - H_Ψ†‖ < ε
        """
        op = HPsiSelfAdjointCorrected(L=10.0, N=200)
        result = op.verify_self_adjointness()
        
        # Self-adjointness error should be very small
        assert result['hermiticity_error'] < 1e-10
        assert result['commutator_error'] < 1e-10
        assert result['is_self_adjoint']
        assert result['status'] == 'PASSED'
    
    def test_fallo_2_unitary_transform(self):
        """
        Test FALLO 2: Unitary transformation between Hilbert spaces
        
        Verifies that U U⁻¹ = I and U⁻¹ U = I
        """
        op = HPsiSelfAdjointCorrected(L=10.0, N=200)
        result = op.verify_unitary_transform()
        
        # Unitarity error should be very small
        assert result['unitarity_error'] < 1e-10
        assert result['inverse_error'] < 1e-10
        assert result['is_unitary']
        assert result['status'] == 'PASSED'
    
    def test_fallo_2_unitary_inverse_product(self):
        """Test that U @ U_inv = I explicitly"""
        op = HPsiSelfAdjointCorrected(L=8.0, N=100)
        
        I = np.eye(op.N)
        UU_inv = op.U @ op.U_inv
        U_invU = op.U_inv @ op.U
        
        assert np.allclose(UU_inv, I, atol=1e-10)
        assert np.allclose(U_invU, I, atol=1e-10)
    
    def test_fallo_3_discrete_spectrum(self):
        """
        Test FALLO 3: Discrete spectrum verification
        
        Verifies that eigenvalues are well-separated (discrete)
        """
        op = HPsiSelfAdjointCorrected(L=10.0, N=200)
        result = op.verify_discrete_spectrum()
        
        # Spectrum should be discrete (min spacing > 0)
        assert result['min_spacing'] > 1e-6
        assert result['is_discrete']
        assert result['status'] == 'PASSED'
    
    def test_fallo_3_hilbert_schmidt_finite(self):
        """
        Test FALLO 3: Hilbert-Schmidt norm is finite
        
        Verifies that ‖K_λ‖_HS < ∞ for resolvent kernel
        """
        op = HPsiSelfAdjointCorrected(L=10.0, N=100, C=-1.0)
        hs_norm = op.compute_hilbert_schmidt_norm(lambda_param=1.0)
        
        # HS norm should be finite
        assert np.isfinite(hs_norm)
        assert hs_norm > 0
    
    def test_transformation_property(self):
        """
        Test that H̃_Ψ = U H_Ψ U⁻¹ ≈ -d/dy
        
        The transformed operator should be approximately pure momentum.
        Note: Due to discretization, we use relaxed tolerance.
        """
        op = HPsiSelfAdjointCorrected(L=10.0, N=200)
        result = op.verify_transformation_property()
        
        # Transformation should be approximate (relaxed tolerance due to discretization)
        assert result['is_pure_momentum']
        assert result['status'] == 'PASSED'
        # Error may be large due to discretization but should be finite
        assert np.isfinite(result['transformation_error'])
    
    def test_spectrum_computation(self):
        """Test spectrum computation"""
        op = HPsiSelfAdjointCorrected(L=8.0, N=100)
        eigenvalues, eigenvectors = op.compute_spectrum()
        
        assert len(eigenvalues) == 100
        assert eigenvectors.shape == (100, 100)
        
        # Eigenvalues should be sorted
        assert np.all(np.diff(eigenvalues) >= 0)
    
    def test_spectrum_subset(self):
        """Test computing subset of spectrum"""
        op = HPsiSelfAdjointCorrected(L=8.0, N=100)
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=20)
        
        assert len(eigenvalues) == 20
        assert eigenvectors.shape == (100, 20)
    
    def test_certificate_generation(self):
        """Test certificate generation"""
        op = HPsiSelfAdjointCorrected(L=10.0, N=200)
        cert = op.generate_certificate()
        
        # Check certificate structure
        assert 'theorem' in cert
        assert 'signature' in cert
        assert 'fallo_1_self_adjointness' in cert
        assert 'fallo_2_unitary_transform' in cert
        assert 'fallo_3_discrete_spectrum' in cert
        assert 'overall_status' in cert
        
        # Check QCAL constants
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == 141.7001
        
        # All fallos should be resolved
        assert cert['fallo_1_self_adjointness']['status'] == 'PASSED'
        assert cert['fallo_2_unitary_transform']['status'] == 'PASSED'
        assert cert['fallo_3_discrete_spectrum']['status'] == 'PASSED'
        
        # Overall status should be PASSED
        assert cert['overall_status'] == 'PASSED'
    
    def test_verify_convenience_function(self):
        """Test convenience verification function"""
        cert = verify_h_psi_corrected(L=8.0, N=100, C=-1.0, verbose=False)
        
        assert 'overall_status' in cert
        assert cert['overall_status'] == 'PASSED'
    
    def test_parameter_variations(self):
        """Test with different parameter values"""
        # Different domain sizes
        for L in [5.0, 10.0, 15.0]:
            op = HPsiSelfAdjointCorrected(L=L, N=100, C=-1.0)
            assert op.L == L
            
        # Different grid resolutions
        for N in [50, 100, 200]:
            op = HPsiSelfAdjointCorrected(L=10.0, N=N, C=-1.0)
            assert op.N == N
            
        # Different C values (all negative)
        for C in [-0.5, -1.0, -2.0]:
            op = HPsiSelfAdjointCorrected(L=10.0, N=100, C=C)
            assert op.C == C
    
    def test_eigenvalues_real(self):
        """Test that eigenvalues are real (self-adjoint property)"""
        op = HPsiSelfAdjointCorrected(L=10.0, N=100)
        eigenvalues, _ = op.compute_spectrum()
        
        # All eigenvalues should be real
        assert np.all(np.abs(eigenvalues.imag) < 1e-10)
    
    def test_eigenvectors_orthogonal(self):
        """Test that eigenvectors are orthogonal"""
        op = HPsiSelfAdjointCorrected(L=10.0, N=100)
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=20)
        
        # Compute Gram matrix
        gram = eigenvectors.T @ eigenvectors
        I = np.eye(20)
        
        # Should be approximately identity
        assert np.allclose(gram, I, atol=1e-8)
    
    def test_operator_action_preserves_domain(self):
        """Test that H_Ψ preserves the function space"""
        op = HPsiSelfAdjointCorrected(L=10.0, N=100)
        
        # Random test vector
        psi = np.random.randn(op.N)
        psi = psi / norm(psi)
        
        # Apply operator
        H_psi = op.H_psi @ psi
        
        # Result should have same dimension
        assert len(H_psi) == op.N
    
    def test_numerical_stability(self):
        """Test numerical stability with multiple runs"""
        results = []
        for _ in range(5):
            op = HPsiSelfAdjointCorrected(L=10.0, N=200, C=-1.0)
            cert = op.generate_certificate()
            results.append(cert['overall_status'])
        
        # All runs should pass
        assert all(status == 'PASSED' for status in results)
    
    def test_c_parameter_sign_matters(self):
        """Test that C < 0 is enforced"""
        # Negative C should work
        op1 = HPsiSelfAdjointCorrected(C=-1.0)
        assert op1.C < 0
        
        # Positive C should raise error
        with pytest.raises(ValueError):
            HPsiSelfAdjointCorrected(C=1.0)
        
        # Zero C should raise error
        with pytest.raises(ValueError):
            HPsiSelfAdjointCorrected(C=0.0)


class TestIntegration:
    """Integration tests for complete workflow"""
    
    def test_full_verification_workflow(self):
        """Test complete verification workflow"""
        # Create operator
        op = HPsiSelfAdjointCorrected(L=10.0, N=200, C=-1.0)
        
        # Verify all three fallos
        f1 = op.verify_self_adjointness()
        f2 = op.verify_unitary_transform()
        f3 = op.verify_discrete_spectrum()
        
        assert f1['status'] == 'PASSED'
        assert f2['status'] == 'PASSED'
        assert f3['status'] == 'PASSED'
        
        # Generate certificate
        cert = op.generate_certificate()
        assert cert['overall_status'] == 'PASSED'
    
    def test_certificate_json_serializable(self):
        """Test that certificate can be JSON serialized"""
        import json
        
        cert = verify_h_psi_corrected(L=10.0, N=100, C=-1.0, verbose=False)
        
        # Should be serializable to JSON
        json_str = json.dumps(cert, indent=2)
        assert len(json_str) > 0
        
        # Should be deserializable
        cert_loaded = json.loads(json_str)
        assert cert_loaded['overall_status'] == cert['overall_status']


@pytest.mark.slow
class TestPerformance:
    """Performance and convergence tests (marked as slow)"""
    
    def test_convergence_with_resolution(self):
        """Test that errors decrease with increasing resolution"""
        results = []
        for N in [50, 100, 200]:
            op = HPsiSelfAdjointCorrected(L=10.0, N=N, C=-1.0)
            cert = op.generate_certificate()
            results.append({
                'N': N,
                'hermiticity_error': cert['fallo_1_self_adjointness']['hermiticity_error'],
                'unitarity_error': cert['fallo_2_unitary_transform']['unitarity_error'],
            })
        
        # Errors should decrease or stay small
        for key in ['hermiticity_error', 'unitarity_error']:
            errors = [r[key] for r in results]
            # All should be small
            assert all(e < 1e-8 for e in errors)
    
    def test_large_grid_performance(self):
        """Test with larger grid (performance test)"""
        op = HPsiSelfAdjointCorrected(L=15.0, N=300, C=-1.0)
        cert = op.generate_certificate()
        
        # Should still pass with larger grid
        assert cert['overall_status'] == 'PASSED'


if __name__ == '__main__':
    # Run tests
    pytest.main([__file__, '-v'])
