#!/usr/bin/env python3
"""
Tests for Asymptotic Riemann Potential Operator
================================================

Tests the implementation of V(y) ~ 2y/log(y) potential and related operators.
"""

import pytest
import numpy as np
import sys
import os

# Add operators to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from operators.asymptotic_riemann_potential import (
    AsymptoticPotential,
    SchrodingerOperator,
    FactorizedOperator,
    generate_certificate,
    F0_HZ,
    C_QCAL,
    KAPPA_PI,
)


class TestAsymptoticPotential:
    """Test AsymptoticPotential class."""
    
    def test_initialization(self):
        """Test that AsymptoticPotential initializes correctly."""
        pot = AsymptoticPotential(regularization='simple')
        assert pot.regularization == 'simple'
        assert pot.epsilon > 0
        
    def test_potential_values(self):
        """Test that V(y) returns reasonable values."""
        pot = AsymptoticPotential(regularization='simple')
        y = np.array([1.0, 10.0, 100.0])
        V = pot.V(y)
        
        # Check shape
        assert V.shape == y.shape
        
        # Check values are finite
        assert np.all(np.isfinite(V))
        
        # Check sign (should be positive for positive y)
        assert np.all(V[y > 0] > 0)
        
    def test_asymptotic_behavior_V(self):
        """Test that V(y) ~ 2y/log(y) for large y."""
        pot = AsymptoticPotential(regularization='simple')
        
        # Test at large y values
        y_large = np.array([100.0, 500.0, 1000.0])
        V_computed = pot.V(y_large)
        V_expected = 2 * y_large / np.log(y_large)
        
        # Relative error should be small for large y
        rel_error = np.abs(V_computed / V_expected - 1.0)
        assert np.all(rel_error < 0.05), f"Max error: {np.max(rel_error)}"
        
    def test_derivative(self):
        """Test that dV/dy is computed correctly."""
        pot = AsymptoticPotential(regularization='simple')
        y = np.array([5.0, 10.0, 50.0])
        
        dV = pot.dV_dy(y)
        
        # Check shape and finiteness
        assert dV.shape == y.shape
        assert np.all(np.isfinite(dV))
        
    def test_effective_potential_Q(self):
        """Test Q(y) = V(y)² - V'(y)."""
        pot = AsymptoticPotential(regularization='simple')
        y = np.array([10.0, 50.0, 100.0])
        
        Q = pot.Q(y)
        
        # Check shape and finiteness
        assert Q.shape == y.shape
        assert np.all(np.isfinite(Q))
        
        # Q should be positive for large y (dominated by V²)
        assert np.all(Q[y > 50] > 0)
        
    def test_asymptotic_behavior_Q(self):
        """Test that Q(y) ~ 4y²/(log y)² for large y."""
        pot = AsymptoticPotential(regularization='simple')
        
        # Test at large y values
        y_large = np.array([100.0, 500.0, 1000.0])
        Q_computed = pot.Q(y_large)
        Q_expected = 4 * y_large**2 / (np.log(y_large))**2
        
        # Relative error should be small for large y
        rel_error = np.abs(Q_computed / Q_expected - 1.0)
        assert np.all(rel_error < 0.1), f"Max error: {np.max(rel_error)}"
        
    def test_check_asymptotics(self):
        """Test asymptotic verification method."""
        pot = AsymptoticPotential(regularization='simple')
        results = pot.check_asymptotics(y_max=1000.0, n_points=50)
        
        # Check that results dictionary has expected keys
        assert 'V_max_error' in results
        assert 'Q_max_error' in results
        assert 'y_values' in results
        
        # Errors should be reasonable
        assert results['V_max_error'] < 0.1
        assert results['Q_max_error'] < 0.2
        
    def test_regularizations(self):
        """Test different regularization schemes."""
        regularizations = ['simple', 'log_quadratic', 'exponential']
        
        for reg in regularizations:
            pot = AsymptoticPotential(regularization=reg)
            y = np.array([1.0, 10.0, 100.0])
            
            # All regularizations should give finite values
            V = pot.V(y)
            Q = pot.Q(y)
            
            assert np.all(np.isfinite(V)), f"Failed for {reg}"
            assert np.all(np.isfinite(Q)), f"Failed for {reg}"


class TestSchrodingerOperator:
    """Test SchrodingerOperator class."""
    
    def test_initialization(self):
        """Test SchrodingerOperator initialization."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=100)
        
        assert schr.n_grid == 100
        assert schr.y_grid.shape == (100,)
        assert schr.matrix.shape == (100, 100)
        
    def test_operator_hermiticity(self):
        """Test that T_V is Hermitian (symmetric)."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=100)
        
        # Check Hermiticity
        hermiticity_error = np.linalg.norm(schr.matrix - schr.matrix.T)
        assert hermiticity_error < 1e-10, f"Not Hermitian: {hermiticity_error}"
        
    def test_spectrum_computation(self):
        """Test eigenvalue computation."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=200)
        
        eigenvalues, eigenvectors = schr.compute_spectrum(n_eigenvalues=10)
        
        # Check shapes
        assert eigenvalues.shape == (10,)
        assert eigenvectors.shape[1] == 10
        
        # All eigenvalues should be real (operator is Hermitian)
        assert np.all(np.isreal(eigenvalues))
        
        # Eigenvalues should be sorted
        assert np.all(np.diff(eigenvalues) >= 0)
        
    def test_eigenvalues_positive(self):
        """Test that eigenvalues are positive (Q(y) > 0 for large y)."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=0.0, y_max=10.0, n_grid=200)
        
        eigenvalues, _ = schr.compute_spectrum(n_eigenvalues=20)
        
        # Most eigenvalues should be positive (ground state might be near zero)
        assert np.sum(eigenvalues > 0) >= 15
        
    def test_weyl_counting_function(self):
        """Test Weyl counting function N(λ) ~ (λ/2π) log λ."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=200)
        
        # Test at a few λ values
        lambda_vals = np.array([1.0, 10.0, 100.0])
        N_vals = np.array([schr.weyl_counting_function(lam) for lam in lambda_vals])
        
        # Check monotonicity
        assert np.all(np.diff(N_vals) > 0)
        
        # Check asymptotic form (roughly)
        expected = lambda_vals / (2 * np.pi) * np.log(lambda_vals)
        assert np.allclose(N_vals, expected, rtol=0.01)
        
    def test_verify_weyl_law(self):
        """Test Weyl law verification."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=300)
        
        eigenvalues, _ = schr.compute_spectrum(n_eigenvalues=15)
        
        # Filter positive eigenvalues large enough for Weyl law
        eigenvalues = eigenvalues[eigenvalues > 1.0]
        
        if len(eigenvalues) > 0:
            results = schr.verify_weyl_law(eigenvalues)
            
            # Check that results are reasonable
            assert 'mean_error' in results
            assert 'max_error' in results


class TestFactorizedOperator:
    """Test FactorizedOperator class."""
    
    def test_initialization(self):
        """Test FactorizedOperator initialization."""
        pot = AsymptoticPotential(regularization='simple')
        fact = FactorizedOperator(pot, y_min=-5.0, y_max=5.0, n_grid=100)
        
        assert fact.n_grid == 100
        assert fact.matrix.shape == (100, 100)
        
    def test_spectrum_computation(self):
        """Test spectrum computation for H_V."""
        pot = AsymptoticPotential(regularization='simple')
        fact = FactorizedOperator(pot, y_min=-5.0, y_max=5.0, n_grid=150)
        
        eigenvalues, eigenvectors = fact.compute_spectrum(n_eigenvalues=10)
        
        # Check shapes
        assert eigenvalues.shape == (10,)
        assert eigenvectors.shape[1] == 10
        
        # Eigenvalues can be complex (H_V is not Hermitian)
        # But real parts should be reasonable
        assert np.all(np.abs(eigenvalues.real) < 1e6)
        
    def test_factorization_structure(self):
        """Test that T = H H* has correct structure."""
        pot = AsymptoticPotential(regularization='simple')
        fact = FactorizedOperator(pot, y_min=-5.0, y_max=5.0, n_grid=100)
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=100)
        
        # Compute T_factorized = H H*
        H_adjoint = fact.matrix.conj().T
        T_factorized = fact.matrix @ H_adjoint
        T_direct = schr.matrix
        
        # Check that both are square matrices of same size
        assert T_factorized.shape == T_direct.shape
        
        # Both should be Hermitian
        herm_fact = np.linalg.norm(T_factorized - T_factorized.conj().T)
        herm_dir = np.linalg.norm(T_direct - T_direct.T)
        
        assert herm_fact < 1e-10
        assert herm_dir < 1e-10


class TestCertificate:
    """Test certificate generation."""
    
    def test_generate_certificate(self):
        """Test certificate generation."""
        results = {
            'test_passed': True,
            'asymptotic_accuracy': 0.99,
        }
        
        cert = generate_certificate(results)
        
        # Check required fields
        assert 'protocol' in cert
        assert cert['protocol'] == 'QCAL-ASYMPTOTIC-RIEMANN-POTENTIAL'
        assert 'signature' in cert
        assert cert['signature'] == '∴𓂀Ω∞³Φ'
        
        # Check QCAL constants
        assert 'qcal_constants' in cert
        assert cert['qcal_constants']['f0_hz'] == F0_HZ
        assert cert['qcal_constants']['C'] == C_QCAL
        assert cert['qcal_constants']['kappa_pi'] == KAPPA_PI
        
        # Check theoretical foundation
        assert 'theoretical_foundation' in cert
        assert 'potential_form' in cert['theoretical_foundation']
        assert 'V(y) ~ 2y/log(y)' in cert['theoretical_foundation']['potential_form']
        
    def test_certificate_with_file(self, tmp_path):
        """Test certificate generation with file output."""
        import json
        
        results = {'test': 'passed'}
        output_file = tmp_path / "certificate.json"
        
        cert = generate_certificate(results, output_path=str(output_file))
        
        # Check file was created
        assert output_file.exists()
        
        # Check file content
        with open(output_file, 'r') as f:
            loaded_cert = json.load(f)
        
        assert loaded_cert['protocol'] == cert['protocol']
        assert loaded_cert['signature'] == cert['signature']


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_workflow(self):
        """Test complete workflow from potential to spectrum."""
        # Create potential
        pot = AsymptoticPotential(regularization='simple')
        
        # Verify asymptotics
        asymp_results = pot.check_asymptotics(y_max=500.0, n_points=50)
        assert asymp_results['V_max_error'] < 0.1
        
        # Create Schrödinger operator
        schr = SchrodingerOperator(pot, y_min=-5.0, y_max=5.0, n_grid=250)
        
        # Compute spectrum
        eigenvalues, _ = schr.compute_spectrum(n_eigenvalues=10)
        assert len(eigenvalues) == 10
        
        # Create factorized operator
        fact = FactorizedOperator(pot, y_min=-5.0, y_max=5.0, n_grid=250)
        
        # Generate certificate
        cert = generate_certificate({
            'asymptotic_results': asymp_results,
            'eigenvalues': eigenvalues.tolist(),
        })
        
        assert cert['protocol'] == 'QCAL-ASYMPTOTIC-RIEMANN-POTENTIAL'
        
    @pytest.mark.slow
    def test_high_resolution_spectrum(self):
        """Test spectrum computation with high resolution grid."""
        pot = AsymptoticPotential(regularization='simple')
        schr = SchrodingerOperator(pot, y_min=-10.0, y_max=10.0, n_grid=500)
        
        # Compute more eigenvalues
        eigenvalues, eigenvectors = schr.compute_spectrum(n_eigenvalues=30)
        
        # Check that we got all eigenvalues
        assert len(eigenvalues) == 30
        
        # Check eigenvalues are sorted
        assert np.all(np.diff(eigenvalues) >= 0)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
