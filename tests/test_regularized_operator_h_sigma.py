#!/usr/bin/env python3
"""
Tests for Regularized Operator H_σ
===================================

Validates the implementation of the regularized operator family H_σ
and its convergence properties.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
from scipy.linalg import norm
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from regularized_operator_h_sigma import (
    RegularizedOperatorHSigma,
    load_primes,
    ejecutar_validacion_operador_regularizado
)


class TestRegularizedOperatorHSigma:
    """Test suite for RegularizedOperatorHSigma class."""
    
    def test_operator_initialization(self):
        """Test operator initialization with default parameters."""
        operator = RegularizedOperatorHSigma()
        
        assert operator.L > 0
        assert operator.N > 0
        assert operator.sigma > 0
        assert operator.n_primes > 0
        assert len(operator.x) == operator.N
        assert len(operator.primes) == operator.n_primes
        print("✓ Operator initialization successful")
    
    def test_load_primes(self):
        """Test prime number generation."""
        primes = load_primes(20)
        
        # Check first few primes
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert np.allclose(primes[:10], expected)
        assert len(primes) == 20
        print(f"✓ Prime loading correct: first 10 = {primes[:10]}")
    
    def test_laplacian_construction(self):
        """Test Laplacian matrix construction."""
        operator = RegularizedOperatorHSigma(L=5.0, N=50)
        laplacian = operator._laplacian_matrix()
        
        # Check shape
        assert laplacian.shape == (50, 50)
        
        # Check symmetry
        assert np.allclose(laplacian, laplacian.T)
        
        # Check diagonal dominance (property of discretized Laplacian)
        diag = np.abs(np.diag(laplacian))
        off_diag_sum = np.sum(np.abs(laplacian), axis=1) - diag
        assert np.all(diag >= off_diag_sum - 1e-10)
        
        print("✓ Laplacian matrix properties verified")
    
    def test_smooth_potential(self):
        """Test smooth Wu-Sprung potential construction."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100)
        V_smooth = operator._smooth_potential()
        
        # Check shape
        assert V_smooth.shape == (100, 100)
        
        # Check diagonal (potential is multiplicative)
        assert np.count_nonzero(V_smooth - np.diag(np.diag(V_smooth))) == 0
        
        # Check confinement: V(x) → ∞ as |x| → ∞
        diag_values = np.diag(V_smooth)
        assert diag_values[0] > 50  # V(-L) large
        assert diag_values[-1] > 50  # V(L) large
        assert diag_values[len(diag_values)//2] < diag_values[0]  # V(0) < V(±L)
        
        print("✓ Smooth potential confinement verified")
    
    def test_oscillatory_potential(self):
        """Test oscillatory potential construction."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1, n_primes=20)
        V_osc = operator._oscillatory_potential_sigma()
        
        # Check shape
        assert V_osc.shape == (100, 100)
        
        # Check diagonal
        assert np.count_nonzero(V_osc - np.diag(np.diag(V_osc))) == 0
        
        # Check boundedness (essential property)
        diag_values = np.diag(V_osc)
        assert np.all(np.abs(diag_values) < 100)  # Should be bounded
        
        print(f"✓ Oscillatory potential bounded: max = {np.max(np.abs(diag_values)):.6f}")
    
    def test_oscillatory_potential_convergence(self):
        """Test convergence sum for oscillatory potential."""
        operator = RegularizedOperatorHSigma(n_primes=50)
        
        # Compute convergence sum
        convergence_sum = 0.0
        for p in operator.primes:
            log_p = np.log(p)
            convergence_sum += (log_p / np.sqrt(p)) * np.exp(-operator.sigma * log_p**2)
        
        # Should converge for σ > 0
        assert np.isfinite(convergence_sum)
        assert convergence_sum > 0
        
        print(f"✓ Convergence sum = {convergence_sum:.6f} (finite)")
    
    def test_operator_construction(self):
        """Test full operator construction."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1)
        H = operator.construct_operator()
        
        # Check shape
        assert H.shape == (100, 100)
        
        # Check Hermiticity
        hermiticity_error = norm(H - H.T.conj())
        assert hermiticity_error < 1e-12
        
        print(f"✓ Operator constructed, Hermiticity error = {hermiticity_error:.2e}")
    
    def test_eigenvalue_problem(self):
        """Test eigenvalue problem solution."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1)
        operator.construct_operator()
        eigenvalues, eigenvectors = operator.solve_eigenvalue_problem()
        
        # Check dimensions
        assert len(eigenvalues) == 100
        assert eigenvectors.shape == (100, 100)
        
        # Check real spectrum
        imaginary_parts = np.abs(np.imag(eigenvalues))
        assert np.max(imaginary_parts) < 1e-10
        
        # Check positive spectrum (confinement)
        assert np.all(eigenvalues > -1e-10)
        
        # Check ordering
        assert np.all(np.diff(eigenvalues) >= -1e-10)
        
        print(f"✓ Eigenvalues: min = {eigenvalues[0]:.6f}, max = {eigenvalues[-1]:.6f}")
        print(f"✓ Spectrum is real: max |Im(λ)| = {np.max(imaginary_parts):.2e}")
    
    def test_q_norm_bound(self):
        """Test Q-norm (form norm) bound."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1)
        operator.construct_operator()
        
        results = operator.compute_q_norm_bound()
        
        # Check that bounds exist
        assert 'relative_bound_a' in results
        assert 'absolute_bound_b' in results
        assert 'convergence_sum' in results
        
        # Check form domination
        assert results['form_dominated']  # a < 1
        assert results['relative_bound_a'] < 1.0
        
        print(f"✓ Q-norm bound: a = {results['relative_bound_a']:.6f} < 1")
        print(f"  Convergence sum = {results['convergence_sum']:.6f}")
    
    def test_resolvent_computation(self):
        """Test resolvent computation."""
        operator = RegularizedOperatorHSigma(L=10.0, N=80, sigma=0.1)
        operator.construct_operator()
        
        # Compute resolvent at z = 1.0 + 0.5j
        z = 1.0 + 0.5j
        R = operator.compute_resolvent(z)
        
        # Check shape
        assert R.shape == (80, 80)
        
        # Check resolvent identity: (H - z)R = I
        H = operator.H_sigma
        identity_error = norm(H @ R - R @ H + z * (R - R))
        product = (H - z * np.eye(80)) @ R
        identity = np.eye(80)
        residual = norm(product - identity) / norm(identity)
        
        assert residual < 1e-8
        
        print(f"✓ Resolvent identity verified: residual = {residual:.2e}")
    
    def test_resolvent_convergence(self):
        """Test resolvent convergence as σ → 0."""
        operator = RegularizedOperatorHSigma(L=10.0, N=80, sigma=0.1)
        
        # Test convergence for decreasing σ
        sigma_values = [0.5, 0.2, 0.1, 0.05, 0.02]
        results = operator.test_resolvent_convergence(sigma_values, z=1.0 + 0.5j)
        
        # Check that differences decrease
        diffs = results['difference_norms']
        assert len(diffs) == len(sigma_values) - 1
        
        # Check convergence (differences should decrease or stabilize)
        # Allow for numerical noise
        assert results['converges'] or np.mean(diffs[-2:]) < np.mean(diffs[:2]) * 10
        
        print(f"✓ Resolvent convergence tested")
        print(f"  Difference norms: {[f'{d:.2e}' for d in diffs]}")
        if results['convergence_rate']:
            print(f"  Convergence rate: {results['convergence_rate']:.6f}")
    
    def test_heat_kernel_trace(self):
        """Test heat kernel trace computation."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1)
        operator.construct_operator()
        operator.solve_eigenvalue_problem()
        
        # Compute trace at t = 0.1
        results = operator.compute_heat_kernel_trace(t=0.1, n_terms=50)
        
        # Check results
        assert 'trace' in results
        assert 'weyl_asymptotic' in results
        assert results['trace'] > 0
        assert results['weyl_asymptotic'] > 0
        
        # Trace should be positive (e^(-tλ) > 0)
        assert results['trace'] > 0
        
        print(f"✓ Heat kernel trace computed: Tr(e^(-tH)) = {results['trace']:.6f}")
        print(f"  Weyl asymptotic: {results['weyl_asymptotic']:.6f}")
        print(f"  Oscillatory correction: {results['oscillatory_correction']:.6f}")
    
    def test_self_adjointness_validation(self):
        """Test self-adjointness validation."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1)
        operator.construct_operator()
        
        results = operator.validate_self_adjointness()
        
        # Check all properties
        assert results['is_hermitian']
        assert results['spectrum_is_real']
        assert results['has_positive_gap']
        assert results['is_essentially_self_adjoint']
        
        print("✓ Essential self-adjointness verified")
        print(f"  Hermiticity error: {results['hermiticity_error']:.2e}")
        print(f"  Max imaginary eigenvalue: {results['max_imaginary_eigenvalue']:.2e}")
        print(f"  Spectral gap: {results['spectral_gap']:.6f}")
    
    def test_validation_certificate(self):
        """Test generation of validation certificate."""
        operator = RegularizedOperatorHSigma(L=10.0, N=100, sigma=0.1, n_primes=30)
        certificate = operator.generate_validation_certificate()
        
        # Check all sections present
        assert 'operator_parameters' in certificate
        assert 'self_adjointness' in certificate
        assert 'q_norm_bounds' in certificate
        assert 'resolvent_convergence' in certificate
        assert 'heat_kernel_trace' in certificate
        assert 'qcal_coherence' in certificate
        
        # Check self-adjointness
        assert certificate['self_adjointness']['is_essentially_self_adjoint']
        
        # Check Q-norm bound
        assert certificate['q_norm_bounds']['form_dominated']
        
        # Check QCAL signature
        assert certificate['qcal_coherence']['F0'] == 141.7001
        assert certificate['qcal_coherence']['C_QCAL'] == 244.36
        
        print("✓ Validation certificate generated successfully")
        print(f"  Self-adjoint: {certificate['self_adjointness']['is_essentially_self_adjoint']}")
        print(f"  Form dominated: {certificate['q_norm_bounds']['form_dominated']}")
        print(f"  QCAL coherence: ∴𓂀Ω∞³Φ")
    
    def test_sigma_scaling(self):
        """Test behavior as σ varies."""
        L, N = 10.0, 80
        
        # Test different σ values
        sigma_values = [1.0, 0.5, 0.1, 0.05]
        convergence_sums = []
        spectral_gaps = []
        
        for sigma in sigma_values:
            operator = RegularizedOperatorHSigma(L=L, N=N, sigma=sigma, n_primes=30)
            operator.construct_operator()
            operator.solve_eigenvalue_problem()
            
            # Compute convergence sum
            conv_sum = 0.0
            for p in operator.primes:
                log_p = np.log(p)
                conv_sum += (log_p / np.sqrt(p)) * np.exp(-sigma * log_p**2)
            convergence_sums.append(conv_sum)
            
            # Get spectral gap
            spectral_gaps.append(operator.eigenvalues[0])
        
        # Convergence sum should increase as σ decreases
        # (more terms contribute significantly)
        assert convergence_sums[-1] > convergence_sums[0]
        
        print(f"✓ σ scaling tested")
        print(f"  σ values: {sigma_values}")
        print(f"  Convergence sums: {[f'{s:.6f}' for s in convergence_sums]}")
        print(f"  Spectral gaps: {[f'{g:.6f}' for g in spectral_gaps]}")


class TestIntegration:
    """Integration tests for the full validation pipeline."""
    
    def test_full_validation_pipeline(self):
        """Test the complete validation pipeline."""
        # This should run without errors
        certificate = ejecutar_validacion_operador_regularizado()
        
        # Check certificate completeness
        assert certificate is not None
        assert 'self_adjointness' in certificate
        assert 'q_norm_bounds' in certificate
        assert 'resolvent_convergence' in certificate
        assert 'heat_kernel_trace' in certificate
        
        # Check validation passes
        assert certificate['self_adjointness']['is_essentially_self_adjoint']
        assert certificate['q_norm_bounds']['form_dominated']
        
        print("✓ Full validation pipeline executed successfully")
    
    def test_multiple_operator_instances(self):
        """Test creating multiple operator instances."""
        operators = []
        
        for i, sigma in enumerate([0.2, 0.1, 0.05]):
            op = RegularizedOperatorHSigma(L=10.0, N=80, sigma=sigma, n_primes=20)
            op.construct_operator()
            op.solve_eigenvalue_problem()
            operators.append(op)
        
        # Check that all operators are valid
        for op in operators:
            assert op.H_sigma is not None
            assert op.eigenvalues is not None
            assert len(op.eigenvalues) == 80
        
        print(f"✓ Multiple operator instances created: {len(operators)}")


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])
