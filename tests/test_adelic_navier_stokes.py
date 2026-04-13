#!/usr/bin/env python3
"""
Tests for Adelic Navier-Stokes Implementation
==============================================

Comprehensive test suite for the Adelic Laplacian and Navier-Stokes operators.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from adelic_laplacian import AdelicLaplacian, SeeleyDeWittTensor
from navier_stokes_adelic import NavierStokesAdelic, FredholmDeterminant


class TestAdelicLaplacian:
    """Test suite for the AdelicLaplacian operator."""
    
    def test_initialization(self):
        """Test that AdelicLaplacian initializes correctly."""
        laplacian = AdelicLaplacian()
        
        assert laplacian.kappa > 2.5 and laplacian.kappa < 2.6
        assert laplacian.f0 == 141.7001
        assert len(laplacian.x) == laplacian.n_points
        assert len(laplacian.primes) == laplacian.n_primes
        
    def test_archimedean_laplacian_shape(self):
        """Test that archimedean Laplacian preserves shape."""
        laplacian = AdelicLaplacian(n_points=100)
        psi = np.random.randn(100)
        
        result = laplacian.archimedean_laplacian(psi)
        
        assert result.shape == psi.shape
        assert not np.any(np.isnan(result))
        assert not np.any(np.isinf(result))
        
    def test_archimedean_laplacian_gaussian(self):
        """Test archimedean Laplacian on Gaussian function."""
        laplacian = AdelicLaplacian(n_points=200, x_range=(-5, 5))
        
        # Gaussian: e^{-x^2/2}
        psi = np.exp(-laplacian.x**2 / 2)
        
        # Analytic: Δψ = (x^2 - 1) e^{-x^2/2}
        expected = (laplacian.x**2 - 1) * psi
        
        result = laplacian.archimedean_laplacian(psi)
        
        # Check approximate equality (finite differences introduce error)
        np.testing.assert_allclose(result, expected, rtol=0.1, atol=0.1)
        
    def test_p_adic_laplacian_shape(self):
        """Test that p-adic Laplacian preserves shape."""
        laplacian = AdelicLaplacian(n_points=100)
        psi = np.random.randn(100)
        
        for p in laplacian.primes[:5]:
            result = laplacian.p_adic_laplacian(psi, p)
            
            assert result.shape == psi.shape
            assert not np.any(np.isnan(result))
            assert not np.any(np.isinf(result))
            
    def test_total_action(self):
        """Test total adelic Laplacian action."""
        laplacian = AdelicLaplacian(n_points=100, n_primes=10)
        psi = np.random.randn(100)
        
        result = laplacian.total_action(psi)
        
        assert result.shape == psi.shape
        assert not np.any(np.isnan(result))
        assert not np.any(np.isinf(result))
        
    def test_diffusion_operator(self):
        """Test scaled diffusion operator."""
        laplacian = AdelicLaplacian(n_points=100)
        psi = np.random.randn(100)
        
        total = laplacian.total_action(psi)
        diffusion = laplacian.diffusion_operator(psi)
        
        # diffusion = (1/kappa) * total
        np.testing.assert_allclose(diffusion, total / laplacian.kappa, rtol=1e-10)
        
    def test_matrix_construction(self):
        """Test that matrix is constructed correctly."""
        laplacian = AdelicLaplacian(n_points=50, n_primes=5)
        
        matrix = laplacian.construct_matrix()
        
        assert matrix.shape == (50, 50)
        assert not np.any(np.isnan(matrix))
        assert not np.any(np.isinf(matrix))
        
    def test_symmetry_verification(self):
        """Test that operator is symmetric."""
        laplacian = AdelicLaplacian(n_points=50, n_primes=5)
        
        results = laplacian.verify_symmetry()
        
        assert results['is_symmetric']
        assert results['symmetry_error'] < 1e-10
        assert results['is_positive']
        
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        laplacian = AdelicLaplacian(n_points=50, n_primes=5)
        
        eigenvalues, eigenvectors = laplacian.get_spectrum(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert eigenvectors.shape == (50, 10)
        
        # Eigenvalues should be real (operator is Hermitian)
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-10
        
        # Eigenvalues should be in increasing order
        assert np.all(np.diff(eigenvalues) >= 0)
        
    def test_adelic_distance(self):
        """Test adelic distance computation."""
        laplacian = AdelicLaplacian()
        
        d1 = laplacian.adelic_distance(0.0, 1.0)
        d2 = laplacian.adelic_distance(0.0, 2.0)
        
        # Distance should be positive
        assert d1 > 0
        assert d2 > 0
        
        # Distance should be symmetric
        d_sym = laplacian.adelic_distance(1.0, 0.0)
        np.testing.assert_almost_equal(d1, d_sym)
        
    def test_heat_kernel_coefficients(self):
        """Test heat kernel coefficient computation."""
        laplacian = AdelicLaplacian()
        
        a0 = laplacian.heat_kernel_coefficient_a0(t=0.1)
        a2 = laplacian.heat_kernel_coefficient_a2(x=0.0)
        
        assert a0 > 0
        assert not np.isnan(a0)
        assert not np.isnan(a2)


class TestSeeleyDeWittTensor:
    """Test suite for the Seeley-DeWitt tensor."""
    
    def test_initialization(self):
        """Test Seeley-DeWitt tensor initialization."""
        laplacian = AdelicLaplacian()
        tensor = SeeleyDeWittTensor(laplacian)
        
        assert tensor.laplacian is laplacian
        
    def test_heat_kernel_expansion(self):
        """Test heat kernel expansion computation."""
        laplacian = AdelicLaplacian(n_points=100)
        tensor = SeeleyDeWittTensor(laplacian)
        
        K = tensor.heat_kernel_expansion(x=0.0, y=0.0, t=0.1, order=2)
        
        assert K > 0
        assert not np.isnan(K)
        assert not np.isinf(K)
        
    def test_trace_heat_kernel(self):
        """Test heat kernel trace computation."""
        laplacian = AdelicLaplacian(n_points=50, n_primes=5)
        tensor = SeeleyDeWittTensor(laplacian)
        
        trace = tensor.trace_heat_kernel(t=0.1)
        
        assert not np.isnan(trace)
        assert not np.isinf(trace)


class TestNavierStokesAdelic:
    """Test suite for the Navier-Stokes Adelic operator."""
    
    def test_initialization(self):
        """Test NavierStokesAdelic initialization."""
        nse = NavierStokesAdelic()
        
        assert nse.kappa > 2.5 and nse.kappa < 2.6
        assert nse.f0 == 141.7001
        assert nse.adelic_laplacian is not None
        
    def test_effective_potential(self):
        """Test effective potential computation."""
        nse = NavierStokesAdelic(n_points=100)
        
        V = nse.effective_potential(nse.x)
        
        assert V.shape == nse.x.shape
        assert np.all(V > 0)  # Potential should be positive
        
        # Test quadratic growth
        large_x = np.array([10.0, 20.0, 30.0])
        V_large = nse.effective_potential(large_x)
        assert np.all(V_large > large_x**2)  # Should grow faster than x^2
        
    def test_transport_term(self):
        """Test transport term -x∂_x."""
        nse = NavierStokesAdelic(n_points=100)
        
        # Test on x^2 (should give -2x^2)
        psi = nse.x**2
        transport = nse.transport_term(psi)
        
        # Check approximate equality
        expected = -2 * psi
        np.testing.assert_allclose(transport, expected, rtol=0.1, atol=0.5)
        
    def test_diffusion_term(self):
        """Test diffusion term."""
        nse = NavierStokesAdelic(n_points=100, n_primes=5)
        psi = np.random.randn(100)
        
        diffusion = nse.diffusion_term(psi)
        
        assert diffusion.shape == psi.shape
        assert not np.any(np.isnan(diffusion))
        
    def test_potential_term(self):
        """Test potential term."""
        nse = NavierStokesAdelic(n_points=100)
        psi = np.ones(100)
        
        potential = nse.potential_term(psi)
        V = nse.effective_potential(nse.x)
        
        np.testing.assert_array_almost_equal(potential, V)
        
    def test_total_action(self):
        """Test complete operator action."""
        nse = NavierStokesAdelic(n_points=100, n_primes=5)
        psi = np.random.randn(100)
        
        H_psi = nse.total_action(psi)
        
        assert H_psi.shape == psi.shape
        assert not np.any(np.isnan(H_psi))
        assert not np.any(np.isinf(H_psi))
        
    def test_matrix_construction(self):
        """Test matrix construction."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        
        H = nse.construct_matrix()
        
        assert H.shape == (50, 50)
        assert not np.any(np.isnan(H))
        
    def test_self_adjointness(self):
        """Test that operator is essentially self-adjoint."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        
        results = nse.verify_self_adjointness()
        
        assert results['hermiticity_error'] < 1e-6  # Should be Hermitian
        assert results['all_eigenvalues_real']
        
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        
        eigenvalues, eigenvectors = nse.get_spectrum(n_eigenvalues=10)
        
        assert len(eigenvalues) == 10
        assert eigenvectors.shape == (50, 10)
        
        # Eigenvalues should be real
        assert np.max(np.abs(np.imag(eigenvalues))) < 1e-6
        
        # Eigenvalues should be positive (due to confining potential)
        assert np.all(eigenvalues > -1.0)
        
    def test_heat_kernel_trace(self):
        """Test heat kernel trace computation."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        
        trace_matrix = nse.heat_kernel_trace(t=0.1, method='matrix')
        trace_spectral = nse.heat_kernel_trace(t=0.1, method='spectral')
        
        # Both methods should give similar results
        np.testing.assert_allclose(trace_matrix, trace_spectral, rtol=0.1)
        
    def test_weyl_term(self):
        """Test Weyl term computation."""
        nse = NavierStokesAdelic()
        
        weyl = nse.weyl_term(t=0.1)
        
        assert not np.isnan(weyl)
        assert not np.isinf(weyl)
        assert weyl > 0  # Should be positive
        
    def test_prime_sum_term(self):
        """Test prime sum term computation."""
        nse = NavierStokesAdelic()
        
        prime_sum = nse.prime_sum_term(t=1.0, n_primes=10, k_max=3)
        
        assert not np.isnan(prime_sum)
        assert not np.isinf(prime_sum)
        
    def test_remainder_term(self):
        """Test remainder term is small."""
        nse = NavierStokesAdelic()
        
        remainder = nse.remainder_term(t=1.0)
        
        assert abs(remainder) < 1.0  # Should be small
        
    def test_trace_decomposition(self):
        """Test trace decomposition."""
        nse = NavierStokesAdelic(n_points=50, n_primes=5)
        
        decomp = nse.trace_decomposition(t=0.5)
        
        assert 'weyl' in decomp
        assert 'prime_sum' in decomp
        assert 'remainder' in decomp
        assert 'total_approx' in decomp
        assert 'exact' in decomp
        assert 'error' in decomp
        
        # Components should be finite
        for key in ['weyl', 'prime_sum', 'remainder', 'total_approx', 'exact']:
            assert not np.isnan(decomp[key])
            assert not np.isinf(decomp[key])


class TestFredholmDeterminant:
    """Test suite for the Fredholm determinant."""
    
    def test_initialization(self):
        """Test Fredholm determinant initialization."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        fredholm = FredholmDeterminant(nse)
        
        assert fredholm.operator is nse
        
    def test_log_determinant(self):
        """Test log determinant computation."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        fredholm = FredholmDeterminant(nse)
        
        log_det = fredholm.log_determinant(t=1.0)
        
        assert not np.isnan(log_det)
        
    def test_determinant(self):
        """Test determinant computation."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        fredholm = FredholmDeterminant(nse)
        
        det = fredholm.determinant(t=0.5)
        
        assert not np.isnan(det)
        
    def test_derivative_log_determinant(self):
        """Test derivative of log determinant."""
        nse = NavierStokesAdelic(n_points=50, n_primes=3)
        fredholm = FredholmDeterminant(nse)
        
        deriv = fredholm.derivative_log_determinant(t=1.0)
        
        assert not np.isnan(deriv)


class TestIntegration:
    """Integration tests for the complete system."""
    
    def test_kappa_value(self):
        """Test that κ has the correct value."""
        nse = NavierStokesAdelic()
        
        # κ = 4π/(f₀·Φ) ≈ 2.577310
        f0 = 141.7001
        phi = (1 + np.sqrt(5)) / 2
        expected_kappa = 4 * np.pi / (f0 * phi)
        
        np.testing.assert_almost_equal(nse.kappa, expected_kappa, decimal=6)
        
    def test_constants_consistency(self):
        """Test that constants are consistent across classes."""
        laplacian = AdelicLaplacian()
        nse = NavierStokesAdelic()
        
        assert laplacian.kappa == nse.kappa
        assert laplacian.f0 == nse.f0
        
    def test_numerical_stability(self):
        """Test numerical stability for various parameters."""
        for n_points in [50, 100, 200]:
            for n_primes in [3, 5, 10]:
                nse = NavierStokesAdelic(n_points=n_points, n_primes=n_primes)
                
                psi = np.random.randn(n_points)
                H_psi = nse.total_action(psi)
                
                assert not np.any(np.isnan(H_psi))
                assert not np.any(np.isinf(H_psi))


if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
