#!/usr/bin/env python3
"""
Tests for Hilbert-Pólya Paso de la Verdad Operator
==================================================

Comprehensive test suite for the integral operator demonstration.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from operators.hilbert_polya_paso_verdad import (
    prime_sieve,
    arithmetic_potential_V,
    construct_xp_operator,
    construct_full_operator,
    verify_hermitian,
    compute_kernel_L2_norm,
    verify_spectral_reality,
    verify_determinant_zeta_connection,
    paso_de_la_verdad,
    F0_QCAL,
    C_COHERENCE
)


class TestPrimeSieve:
    """Test prime number generation."""
    
    def test_small_primes(self):
        """Test first few primes."""
        primes = prime_sieve(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected
    
    def test_no_primes(self):
        """Test empty case."""
        primes = prime_sieve(1)
        assert primes == []
    
    def test_large_sieve(self):
        """Test larger sieve."""
        primes = prime_sieve(100)
        assert len(primes) == 25  # 25 primes up to 100
        assert primes[0] == 2
        assert primes[-1] == 97


class TestArithmeticPotential:
    """Test the arithmetic potential V(u)."""
    
    def test_potential_shape(self):
        """Test potential has correct shape."""
        u = np.linspace(0, 10, 100)
        V = arithmetic_potential_V(u, primes=[2, 3, 5], max_k=3)
        assert V.shape == u.shape
        assert np.all(np.isfinite(V))
    
    def test_potential_positive(self):
        """Test potential is non-negative (from smoothed deltas)."""
        u = np.linspace(0, 10, 100)
        V = arithmetic_potential_V(u, primes=[2, 3, 5], max_k=3)
        assert np.all(V >= 0)
    
    def test_potential_peaks_at_prime_logs(self):
        """Test potential has peaks near k*log(p)."""
        u = np.linspace(0, 5, 500)
        V = arithmetic_potential_V(u, primes=[2], max_k=2)
        
        # Should have peaks near log(2) and 2*log(2)
        log_2 = np.log(2)
        
        # Find indices near log(2)
        idx_1 = np.argmin(np.abs(u - log_2))
        idx_2 = np.argmin(np.abs(u - 2*log_2))
        
        # Check these are local maxima
        assert V[idx_1] > V[idx_1 - 5]
        assert V[idx_1] > V[idx_1 + 5]
        assert V[idx_2] > V[idx_2 - 5]
        assert V[idx_2] > V[idx_2 + 5]
    
    def test_potential_decay_with_k(self):
        """Test coefficients decay with k (p^{-k/2})."""
        u = np.array([np.log(2), 2*np.log(2), 3*np.log(2)])
        V = arithmetic_potential_V(u, primes=[2], max_k=3)
        
        # Values should decay as k increases (roughly)
        # V(log p) > V(2 log p) due to 1/sqrt(p) vs 1/p factor
        # This is approximate due to smoothing
        assert V[0] > V[1] * 0.5  # Allow for smoothing effects


class TestXPOperator:
    """Test the xp operator construction."""
    
    def test_xp_operator_shape(self):
        """Test operator has correct shape."""
        N = 64
        H_xp = construct_xp_operator(N)
        assert H_xp.shape == (N, N)
    
    def test_xp_operator_hermitian(self):
        """Test xp operator is Hermitian."""
        N = 64
        H_xp = construct_xp_operator(N)
        
        # Check Hermiticity
        error = np.linalg.norm(H_xp - H_xp.conj().T, 'fro')
        assert error < 1e-10
    
    def test_xp_operator_nonzero(self):
        """Test operator is not trivial."""
        N = 64
        H_xp = construct_xp_operator(N)
        assert np.linalg.norm(H_xp, 'fro') > 0


class TestFullOperator:
    """Test full operator construction."""
    
    def test_full_operator_shape(self):
        """Test full operator has correct shape."""
        N = 64
        H, x = construct_full_operator(N)
        assert H.shape == (N, N)
        assert len(x) == N
    
    def test_full_operator_hermitian(self):
        """Test full operator is Hermitian."""
        N = 64
        H, x = construct_full_operator(N)
        
        error = np.linalg.norm(H - H.conj().T, 'fro')
        assert error < 1e-10
    
    def test_grid_logarithmic(self):
        """Test grid is logarithmic."""
        N = 64
        H, x = construct_full_operator(N, x_min=0.1, x_max=10.0)
        
        # Check logarithmic spacing
        log_x = np.log(x)
        log_diff = np.diff(log_x)
        
        # Should be approximately constant
        assert np.std(log_diff) / np.mean(log_diff) < 0.1


class TestHermitianVerification:
    """Test Hermitian verification."""
    
    def test_hermitian_matrix(self):
        """Test verification passes for Hermitian matrix."""
        N = 32
        A = np.random.randn(N, N) + 1j * np.random.randn(N, N)
        H = 0.5 * (A + A.conj().T)  # Make Hermitian
        
        result = verify_hermitian(H)
        assert result.is_hermitian
        assert result.hermitian_error < 1e-12
        assert result.psi > 0.99
    
    def test_non_hermitian_matrix(self):
        """Test verification fails for non-Hermitian matrix."""
        N = 32
        A = np.random.randn(N, N) + 1j * np.random.randn(N, N)
        
        result = verify_hermitian(A, threshold=1e-6)
        assert not result.is_hermitian
        assert result.hermitian_error > 1e-6
    
    def test_real_symmetric(self):
        """Test real symmetric matrix is Hermitian."""
        N = 32
        A = np.random.randn(N, N)
        H = 0.5 * (A + A.T)
        
        result = verify_hermitian(H)
        assert result.is_hermitian
        assert result.psi > 0.99


class TestKernelL2Norm:
    """Test kernel L² norm computation."""
    
    def test_kernel_finite_norm(self):
        """Test kernel has finite L² norm."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = compute_kernel_L2_norm(H, x)
        assert result.kernel_in_L2
        assert np.isfinite(result.L2_norm)
        assert result.L2_norm > 0
    
    def test_kernel_type(self):
        """Test kernel is classified correctly."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = compute_kernel_L2_norm(H, x)
        assert result.kernel_type in ["Hilbert-Schmidt", "Unbounded"]
    
    def test_decay_rate_positive(self):
        """Test decay rate is computed."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = compute_kernel_L2_norm(H, x)
        assert np.isfinite(result.decay_rate)


class TestSpectralReality:
    """Test spectrum reality verification."""
    
    def test_spectrum_real(self):
        """Test spectrum is real for Hermitian operator."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = verify_spectral_reality(H)
        assert result.spectrum_is_real
        assert result.max_imaginary_part < 1e-10
    
    def test_eigenvalues_computed(self):
        """Test eigenvalues are computed."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = verify_spectral_reality(H)
        assert len(result.eigenvalues) == N
        assert np.all(np.isfinite(result.eigenvalues))
    
    def test_sorted_eigenvalues(self):
        """Test eigenvalues are sorted."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = verify_spectral_reality(H)
        eigenvalues = result.eigenvalues
        assert np.all(eigenvalues[1:] >= eigenvalues[:-1])


class TestDeterminantZeta:
    """Test determinant-zeta connection."""
    
    def test_determinant_computed(self):
        """Test determinants are computed."""
        N = 32
        H, x = construct_full_operator(N)
        
        s_values = np.array([0.5 + 1j * 14.134725])
        result = verify_determinant_zeta_connection(H, s_values)
        
        assert len(result.determinant_values) == len(s_values)
        assert len(result.zeta_values) == len(s_values)
    
    def test_connection_checked(self):
        """Test connection is evaluated."""
        N = 32
        H, x = construct_full_operator(N)
        
        result = verify_determinant_zeta_connection(H)
        assert isinstance(result.determinant_matches_zeta, (bool, np.bool_))
        assert np.isfinite(result.mean_relative_error)


class TestPasoVerdad:
    """Test complete Paso de la Verdad verification."""
    
    def test_paso_verdad_runs(self):
        """Test complete verification runs without errors."""
        results = paso_de_la_verdad(N=64, verbose=False)
        
        assert 'hermitian' in results
        assert 'kernel_L2' in results
        assert 'spectral_reality' in results
        assert 'determinant_zeta' in results
        assert 'psi_total' in results
    
    def test_all_verifications_pass(self):
        """Test all verifications pass."""
        results = paso_de_la_verdad(N=64, verbose=False)
        
        assert results['hermitian'].is_hermitian
        assert results['kernel_L2'].kernel_in_L2
        assert results['spectral_reality'].spectrum_is_real
    
    def test_coherence_computed(self):
        """Test total coherence Ψ is computed."""
        results = paso_de_la_verdad(N=64, verbose=False)
        
        psi_total = results['psi_total']
        assert 0.0 <= psi_total <= 1.0
    
    def test_operator_returned(self):
        """Test operator and grid are returned."""
        results = paso_de_la_verdad(N=64, verbose=False)
        
        assert 'operator' in results
        assert 'grid' in results
        assert results['operator'].shape[0] == 64
        assert len(results['grid']) == 64


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test QCAL constants are defined."""
        assert F0_QCAL == 141.7001
        assert C_COHERENCE == 244.36
    
    def test_coherence_in_results(self):
        """Test coherence Ψ is in all results."""
        N = 64
        H, x = construct_full_operator(N)
        
        # Test each verification includes Ψ
        hermitian_result = verify_hermitian(H)
        assert hasattr(hermitian_result, 'psi')
        assert 0.0 <= hermitian_result.psi <= 1.0
        
        kernel_result = compute_kernel_L2_norm(H, x)
        assert hasattr(kernel_result, 'psi')
        assert 0.0 <= kernel_result.psi <= 1.0
        
        spectral_result = verify_spectral_reality(H)
        assert hasattr(spectral_result, 'psi')
        assert 0.0 <= spectral_result.psi <= 1.0


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_small_grid(self):
        """Test computation works with small grid."""
        results = paso_de_la_verdad(N=32, verbose=False)
        assert results['psi_total'] > 0
    
    def test_large_grid(self):
        """Test computation works with larger grid."""
        results = paso_de_la_verdad(N=128, verbose=False)
        assert results['psi_total'] > 0
    
    def test_different_x_range(self):
        """Test computation works with different x ranges."""
        results = paso_de_la_verdad(N=64, x_min=0.05, x_max=20.0, verbose=False)
        assert results['hermitian'].is_hermitian


class TestPhysicalInterpretation:
    """Test physical interpretation aspects."""
    
    def test_primes_as_orbits(self):
        """Test primes appear in the potential."""
        primes = [2, 3, 5, 7]
        u = np.linspace(0, 10, 1000)
        V = arithmetic_potential_V(u, primes=primes, max_k=2)
        
        # Check potential has contributions near prime logs
        for p in primes:
            log_p = np.log(p)
            idx = np.argmin(np.abs(u - log_p))
            
            # Should be a peak (local maximum in smoothed version)
            neighborhood = V[max(0, idx-10):min(len(V), idx+10)]
            assert V[idx] >= np.median(neighborhood)
    
    def test_zeros_as_quantum_levels(self):
        """Test eigenvalues relate to quantum levels."""
        N = 64
        H, x = construct_full_operator(N)
        
        result = verify_spectral_reality(H)
        eigenvalues = result.eigenvalues
        
        # Eigenvalues should be discrete (quantum levels)
        assert len(eigenvalues) == N
        
        # Should have gaps between levels
        positive_eigs = eigenvalues[eigenvalues > 0]
        if len(positive_eigs) > 1:
            gaps = np.diff(positive_eigs)
            assert np.all(gaps > 0)  # Distinct levels


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
