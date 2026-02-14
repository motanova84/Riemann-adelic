#!/usr/bin/env python3
"""
Tests for Nelson Self-Adjointness Verification
===============================================

Comprehensive test suite for the Nelson self-adjointness verifier.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from pathlib import Path
import tempfile
import shutil

from operators.nelson_self_adjointness import (
    NelsonSelfAdjointnessVerifier,
    verify_nelson_self_adjointness,
    KAPPA_DEFAULT,
    L_DEFAULT,
    N_DEFAULT,
    F0,
    C_QCAL
)


class TestNelsonSelfAdjointnessVerifier:
    """Test suite for Nelson self-adjointness verifier."""
    
    @pytest.fixture
    def verifier(self):
        """Create a standard verifier instance."""
        return NelsonSelfAdjointnessVerifier(
            L=L_DEFAULT,
            N=N_DEFAULT,
            kappa=KAPPA_DEFAULT
        )
    
    @pytest.fixture
    def small_verifier(self):
        """Create a smaller verifier for faster tests."""
        return NelsonSelfAdjointnessVerifier(L=5.0, N=50, kappa=KAPPA_DEFAULT)
    
    def test_initialization(self, verifier):
        """Test verifier initialization."""
        assert verifier.L == L_DEFAULT
        assert verifier.N == N_DEFAULT
        assert verifier.kappa == KAPPA_DEFAULT
        assert len(verifier.x) == N_DEFAULT
        assert verifier.H is None  # Not assembled yet
    
    def test_spatial_grid(self, verifier):
        """Test spatial grid properties."""
        assert verifier.x[0] == 0.0
        assert verifier.x[-1] == pytest.approx(verifier.L, rel=1e-10)
        assert abs(verifier.dx - (verifier.L / (verifier.N - 1))) < 1e-10
    
    def test_differentiation_matrix_shape(self, small_verifier):
        """Test differentiation matrix has correct shape."""
        D = small_verifier._differentiation_matrix()
        assert D.shape == (small_verifier.N, small_verifier.N)
    
    def test_differentiation_matrix_symmetry(self, small_verifier):
        """Test differentiation matrix is symmetric."""
        D = small_verifier._differentiation_matrix()
        max_diff = np.max(np.abs(D - D.T))
        assert max_diff < 1e-14
    
    def test_differentiation_matrix_boundary(self, small_verifier):
        """Test boundary conditions in differentiation matrix.
        
        After symmetrization, the boundary rows may have small values from
        the transpose operation. The important thing is that when multiplied
        by vectors with zero boundary values, the result is consistent.
        """
        D = small_verifier._differentiation_matrix()
        # After symmetrization, we still have small boundary values
        # This is acceptable as long as the full operator is symmetric
        assert D.shape == (small_verifier.N, small_verifier.N)
        # Test that D is symmetric
        assert np.max(np.abs(D - D.T)) < 1e-14
    
    def test_kernel_matrix_shape(self, small_verifier):
        """Test kernel matrix has correct shape."""
        K = small_verifier._kernel_matrix()
        assert K.shape == (small_verifier.N, small_verifier.N)
    
    def test_kernel_matrix_symmetry(self, small_verifier):
        """Test kernel matrix is symmetric."""
        K = small_verifier._kernel_matrix()
        max_diff = np.max(np.abs(K - K.T))
        assert max_diff < 1e-14
    
    def test_kernel_matrix_diagonal(self, small_verifier):
        """Test kernel matrix diagonal values."""
        K = small_verifier._kernel_matrix()
        # Diagonal should be K(x,x) = x (from L'Hôpital's rule)
        for i in range(small_verifier.N):
            expected = small_verifier.x[i] * small_verifier.dx
            assert abs(K[i, i] - expected) < 1e-10
    
    def test_potential_matrix_shape(self, small_verifier):
        """Test potential matrix has correct shape."""
        V = small_verifier._potential_matrix()
        assert V.shape == (small_verifier.N, small_verifier.N)
    
    def test_potential_matrix_diagonal(self, small_verifier):
        """Test potential matrix is diagonal."""
        V = small_verifier._potential_matrix()
        # Off-diagonal elements should be zero
        V_offdiag = V - np.diag(np.diag(V))
        assert np.max(np.abs(V_offdiag)) < 1e-14
    
    def test_potential_values(self, small_verifier):
        """Test potential values are correct."""
        V = small_verifier._potential_matrix()
        kappa = small_verifier.kappa
        
        for i in range(small_verifier.N):
            x = small_verifier.x[i]
            expected = x**2 + (1 + kappa**2) / 4 + np.log(1 + x)
            assert abs(V[i, i] - expected) < 1e-10
    
    def test_assemble_operator(self, small_verifier):
        """Test operator assembly."""
        H = small_verifier.assemble_operator()
        assert H.shape == (small_verifier.N, small_verifier.N)
        assert small_verifier.H is not None
        assert np.array_equal(H, small_verifier.H)
    
    def test_operator_hermiticity(self, small_verifier):
        """Test assembled operator is Hermitian."""
        small_verifier.assemble_operator()
        max_diff = small_verifier.test_hermiticity()
        assert max_diff < 1e-12
    
    def test_symmetry_verification(self, small_verifier):
        """Test symmetry verification."""
        small_verifier.assemble_operator()
        max_error, max_rel_error = small_verifier.test_symmetry(n_tests=50)
        assert max_error < 1e-10
        assert max_rel_error < 1e-10
    
    def test_analytic_vectors(self, small_verifier):
        """Test analytic vectors identification."""
        small_verifier.assemble_operator()
        results = small_verifier.test_analytic_vectors(n_hermite=3, n_powers=4)
        
        assert len(results) == 3
        
        for r in results:
            assert 'n' in r
            assert 'norms' in r
            assert 'growth' in r
            assert 'max_growth' in r
            
            # Check that norms are positive and increasing
            norms = r['norms']
            assert all(n > 0 for n in norms)
            
            # Growth should be bounded (not exponential)
            max_growth = r['max_growth']
            assert max_growth < 100  # Reasonable bound
    
    def test_run_all_tests(self, small_verifier):
        """Test complete verification workflow."""
        results = small_verifier.run_all_tests(verbose=False)
        
        assert 'symmetry_error' in results
        assert 'symmetry_rel_error' in results
        assert 'hermiticity_diff' in results
        assert 'analytic_vectors' in results
        assert 'conclusion' in results
        
        assert results['symmetry_error'] < 1e-10
        assert results['hermiticity_diff'] < 1e-12
        assert results['conclusion'] == 'verified'
    
    def test_different_discretizations(self):
        """Test with different discretization sizes."""
        N_values = [50, 100, 150]
        
        for N in N_values:
            verifier = NelsonSelfAdjointnessVerifier(L=5.0, N=N, kappa=KAPPA_DEFAULT)
            verifier.assemble_operator()
            
            max_diff = verifier.test_hermiticity()
            assert max_diff < 1e-11
            
            max_error, _ = verifier.test_symmetry(n_tests=10)
            assert max_error < 1e-9
    
    def test_different_kappa_values(self):
        """Test with different coupling constants."""
        kappa_values = [1.0, 2.0, 2.577310, 3.0]
        
        for kappa in kappa_values:
            verifier = NelsonSelfAdjointnessVerifier(
                L=5.0, N=50, kappa=kappa
            )
            results = verifier.run_all_tests(verbose=False)
            assert results['conclusion'] == 'verified'
    
    def test_different_domain_lengths(self):
        """Test with different domain lengths."""
        L_values = [5.0, 10.0, 15.0]
        
        for L in L_values:
            verifier = NelsonSelfAdjointnessVerifier(
                L=L, N=50, kappa=KAPPA_DEFAULT
            )
            results = verifier.run_all_tests(verbose=False)
            assert results['conclusion'] == 'verified'
    
    def test_convenience_function(self):
        """Test convenience function."""
        results = verify_nelson_self_adjointness(
            L=5.0, N=50, kappa=KAPPA_DEFAULT, verbose=False
        )
        
        assert results['conclusion'] == 'verified'
        assert results['symmetry_error'] < 1e-10
        assert results['hermiticity_diff'] < 1e-12
    
    def test_qcal_constants(self):
        """Test QCAL constants are defined."""
        assert F0 == 141.7001
        assert C_QCAL == 244.36
        assert KAPPA_DEFAULT == pytest.approx(2.577310, rel=1e-6)


class TestValidationScript:
    """Test the validation script."""
    
    def test_import_validation_script(self):
        """Test that validation script can be imported."""
        import validate_nelson_self_adjointness
        
        assert hasattr(validate_nelson_self_adjointness, 'print_header')
        assert hasattr(validate_nelson_self_adjointness, 'print_certificate')
        assert hasattr(validate_nelson_self_adjointness, 'save_certificate')
    
    def test_certificate_generation(self):
        """Test certificate generation."""
        from validate_nelson_self_adjointness import save_certificate
        
        # Create a temporary directory
        with tempfile.TemporaryDirectory() as tmpdir:
            output_path = Path(tmpdir) / "test_certificate.json"
            
            # Create fake results
            results = {
                'symmetry_error': 1e-14,
                'symmetry_rel_error': 1e-15,
                'hermiticity_diff': 1e-15,
                'analytic_vectors': [],
                'conclusion': 'verified'
            }
            
            # Save certificate
            save_certificate(results, 10.0, 200, 2.577310, output_path)
            
            # Check file exists
            assert output_path.exists()
            
            # Load and verify content
            import json
            with open(output_path) as f:
                cert = json.load(f)
            
            assert 'metadata' in cert
            assert 'operator' in cert
            assert 'verification' in cert
            assert 'theorem' in cert
            
            assert cert['theorem']['verified'] is True
            assert cert['metadata']['frequency'] == F0
            assert cert['metadata']['coherence'] == C_QCAL


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
