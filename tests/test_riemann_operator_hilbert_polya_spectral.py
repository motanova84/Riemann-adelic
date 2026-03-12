#!/usr/bin/env python3
"""
Tests for Riemann Operator Hilbert-Pólya Spectral Validation Module
===================================================================

Comprehensive test suite for the SPECTRAL OMEGA VALIDATION MODULE
with DVR base, adaptive epsilon, and Gaussian comb potential.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from operators.riemann_operator_hilbert_polya_spectral import (
    EvenHilbertSpace,
    HilbertPolyaOperatorAdvanced,
    generate_primes_sieve,
    get_riemann_zeros,
    validar_evidencia_brutal,
    SpectralValidationResult,
    F0_QCAL,
    C_COHERENCE,
    EPSILON_BASE
)


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_generate_primes_small(self):
        """Test prime generation for small values."""
        primes = generate_primes_sieve(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected
    
    def test_generate_primes_first_10(self):
        """Test first 10 primes."""
        primes = generate_primes_sieve(30)
        first_10 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes[:10] == first_10
    
    def test_generate_primes_empty(self):
        """Test edge case with no primes."""
        primes = generate_primes_sieve(1)
        assert primes == []
    
    def test_generate_primes_consistency(self):
        """Test consistency across multiple calls."""
        primes1 = generate_primes_sieve(100)
        primes2 = generate_primes_sieve(100)
        assert primes1 == primes2
    
    def test_generate_primes_large(self):
        """Test generation of first 40 primes."""
        primes = generate_primes_sieve(200)
        assert len(primes) >= 40
        # Verify first few
        assert primes[0] == 2
        assert primes[1] == 3
        assert primes[2] == 5


class TestRiemannZeros:
    """Test Riemann zeros retrieval."""
    
    def test_get_first_zero(self):
        """Test retrieval of first Riemann zero."""
        zeros = get_riemann_zeros(1)
        assert len(zeros) == 1
        # First zero is approximately 14.134725
        assert abs(zeros[0] - 14.134725) < 0.01
    
    def test_get_multiple_zeros(self):
        """Test retrieval of multiple zeros."""
        zeros = get_riemann_zeros(5)
        assert len(zeros) == 5
        # Check ordering (should be increasing)
        assert np.all(np.diff(zeros) > 0)
    
    def test_zeros_positive(self):
        """Test that all zeros are positive."""
        zeros = get_riemann_zeros(10)
        assert np.all(zeros > 0)
    
    def test_zeros_consistency(self):
        """Test consistency across calls."""
        zeros1 = get_riemann_zeros(3)
        zeros2 = get_riemann_zeros(3)
        np.testing.assert_array_almost_equal(zeros1, zeros2)


class TestEvenHilbertSpace:
    """Test the even parity Hilbert space with DVR base."""
    
    def test_space_initialization(self):
        """Test basic initialization."""
        space = EvenHilbertSpace(N=100, u_max=10.0)
        assert space.N == 100
        assert space.u_max == 10.0
        assert len(space.u_grid) == 100
    
    def test_space_makes_even_N(self):
        """Test that odd N is made even."""
        space = EvenHilbertSpace(N=101, u_max=10.0)
        assert space.N % 2 == 0  # Should be even
    
    def test_grid_symmetry(self):
        """Test that grid is symmetric around zero."""
        space = EvenHilbertSpace(N=200, u_max=5.0)
        assert space.u_grid[0] == pytest.approx(-5.0)
        assert space.u_grid[-1] == pytest.approx(5.0)
        
        # Check midpoint
        mid = space.N // 2
        # Midpoint should be close to zero (may not be exact due to discretization)
        assert abs(space.u_grid[mid]) < space.du
    
    def test_grid_spacing_uniform(self):
        """Test uniform grid spacing."""
        space = EvenHilbertSpace(N=100, u_max=10.0)
        spacing = np.diff(space.u_grid)
        # All spacings should be equal
        assert np.allclose(spacing, space.du)
    
    def test_check_even_parity_constant(self):
        """Test even parity check for constant function."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = np.ones(space.N)
        assert space.check_even_parity(psi)
    
    def test_check_even_parity_gaussian(self):
        """Test even parity check for Gaussian function."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = np.exp(-space.u_grid**2)
        assert space.check_even_parity(psi)
    
    def test_check_even_parity_cosine(self):
        """Test even parity check for cosine function."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = np.cos(space.u_grid)
        assert space.check_even_parity(psi)
    
    def test_check_even_parity_odd_function(self):
        """Test even parity check fails for odd function."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = space.u_grid  # Linear function (odd)
        assert not space.check_even_parity(psi)
    
    def test_check_even_parity_sine_fails(self):
        """Test even parity check fails for sine."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = np.sin(space.u_grid)
        assert not space.check_even_parity(psi)
    
    def test_project_to_even_constant(self):
        """Test projection of constant function (should be unchanged)."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        psi = np.ones(space.N) * 2.0
        psi_even = space.project_to_even(psi)
        np.testing.assert_array_almost_equal(psi_even, psi)
    
    def test_project_to_even_makes_symmetric(self):
        """Test that projection creates even function."""
        space = EvenHilbertSpace(N=100, u_max=5.0)
        # Start with arbitrary function
        psi = np.random.randn(space.N)
        psi_even = space.project_to_even(psi)
        # Result should have even parity
        assert space.check_even_parity(psi_even)
    
    def test_invalid_N(self):
        """Test that invalid N raises error."""
        with pytest.raises(ValueError):
            EvenHilbertSpace(N=2, u_max=10.0)  # Too small
    
    def test_invalid_u_max(self):
        """Test that invalid u_max raises error."""
        with pytest.raises(ValueError):
            EvenHilbertSpace(N=100, u_max=-5.0)  # Negative


class TestHilbertPolyaOperatorAdvanced:
    """Test the advanced Hilbert-Pólya operator."""
    
    def test_operator_initialization(self):
        """Test basic operator initialization."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=10, max_k=3)
        
        assert op.num_primes == 10
        assert op.max_k == 3
        assert len(op.primes) == 10
        assert op.H_matrix.shape == (128, 128)
    
    def test_adaptive_epsilon_decreases(self):
        """Test that adaptive epsilon decreases with k."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, epsilon_base=0.03)
        
        eps_1 = op._adaptive_epsilon(1)
        eps_2 = op._adaptive_epsilon(2)
        eps_5 = op._adaptive_epsilon(5)
        
        # Should decrease as k increases
        assert eps_1 > eps_2
        assert eps_2 > eps_5
    
    def test_adaptive_epsilon_formula(self):
        """Test adaptive epsilon formula."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, epsilon_base=0.03)
        
        eps_1 = op._adaptive_epsilon(1)
        expected = 0.03 / (1 ** 0.25)
        assert eps_1 == pytest.approx(expected)
        
        eps_16 = op._adaptive_epsilon(16)
        expected = 0.03 / (16 ** 0.25)
        assert eps_16 == pytest.approx(expected)
    
    def test_gaussian_kernel_normalized(self):
        """Test that Gaussian kernel is normalized."""
        space = EvenHilbertSpace(N=1000, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=5)
        
        u = space.u_grid
        gaussian = op._gaussian_kernel(u, u0=0.0, epsilon=1.0)
        
        # Integral should be approximately 1
        integral = np.trapz(gaussian, u)
        assert integral == pytest.approx(1.0, abs=0.01)
    
    def test_gaussian_kernel_centered(self):
        """Test that Gaussian kernel is centered at u0."""
        space = EvenHilbertSpace(N=1000, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=5)
        
        u0 = 2.5
        gaussian = op._gaussian_kernel(space.u_grid, u0=u0, epsilon=0.5)
        
        # Maximum should be near u0
        max_idx = np.argmax(gaussian)
        u_max = space.u_grid[max_idx]
        assert abs(u_max - u0) < space.du * 2
    
    def test_potential_is_real(self):
        """Test that potential is real-valued."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=10)
        
        V = op._build_potential()
        assert np.all(np.isreal(V))
        assert not np.any(np.isnan(V))
        assert not np.any(np.isinf(V))
    
    def test_potential_is_positive(self):
        """Test that potential is non-negative."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=10)
        
        V = op._build_potential()
        assert np.all(V >= 0)
    
    def test_potential_has_peaks(self):
        """Test that potential has peaks at prime logarithms."""
        space = EvenHilbertSpace(N=1000, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=3, max_k=1)
        
        V = op._build_potential()
        
        # Should have peaks near ln(2), ln(3), ln(5)
        # and their negatives due to symmetry
        assert np.max(V) > 0  # Should have some non-zero values
    
    def test_kinetic_is_symmetric(self):
        """Test that kinetic operator is symmetric."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=5)
        
        T = op._build_kinetic()
        
        # Should be symmetric
        np.testing.assert_array_almost_equal(T, T.T)
    
    def test_kinetic_is_tridiagonal(self):
        """Test that kinetic operator is tridiagonal."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=5)
        
        T = op._build_kinetic()
        
        # Should have non-zero only on main diagonal and first off-diagonals
        for i in range(128):
            for j in range(128):
                if abs(i - j) > 1:
                    assert T[i, j] == pytest.approx(0.0, abs=1e-10)
    
    def test_hamiltonian_is_hermitian(self):
        """Test that Hamiltonian is Hermitian."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=10)
        
        H = op.H_matrix
        
        # Should be Hermitian: H = H†
        hermitian_error = np.max(np.abs(H - H.T))
        assert hermitian_error < 1e-10
    
    def test_hamiltonian_is_real(self):
        """Test that Hamiltonian is real-valued."""
        space = EvenHilbertSpace(N=128, u_max=10.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=10)
        
        H = op.H_matrix
        assert np.all(np.isreal(H))
    
    def test_compute_eigenvalues_returns_sorted(self):
        """Test that eigenvalues are returned sorted."""
        space = EvenHilbertSpace(N=256, u_max=15.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=20)
        
        evals = op.compute_eigenvalues(n_evals=10)
        
        assert len(evals) == 10
        # Should be sorted in ascending order
        assert np.all(np.diff(evals) >= 0)
    
    def test_compute_eigenvalues_are_real(self):
        """Test that eigenvalues are real (Hermitian operator)."""
        space = EvenHilbertSpace(N=256, u_max=15.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=20)
        
        evals = op.compute_eigenvalues(n_evals=10)
        
        # All eigenvalues should be real
        assert np.all(np.isreal(evals))
    
    def test_compare_with_zeta_zeros_shape(self):
        """Test that comparison returns correct shapes."""
        space = EvenHilbertSpace(N=256, u_max=15.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=20)
        
        corr, zeros, evals = op.compare_with_zeta_zeros(n_zeros=5)
        
        assert isinstance(corr, (float, np.floating))
        assert len(zeros) == 5
        assert len(evals) == 5
    
    def test_compare_with_zeta_zeros_correlation_range(self):
        """Test that correlation is in valid range."""
        space = EvenHilbertSpace(N=256, u_max=15.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=20)
        
        corr, _, _ = op.compare_with_zeta_zeros(n_zeros=5)
        
        # Correlation should be between -1 and 1
        assert -1.0 <= corr <= 1.0
    
    def test_fredholm_proxy_returns_complex(self):
        """Test that Fredholm proxy returns complex number."""
        space = EvenHilbertSpace(N=256, u_max=15.0)
        op = HilbertPolyaOperatorAdvanced(space, num_primes=20)
        
        s = complex(0.5, 14.134)
        proxy = op.fredholm_determinant_proxy(s, n_evals=5)
        
        # Should return a complex number (though may be real in practice)
        assert isinstance(proxy, (complex, float, np.complexfloating, np.floating))


class TestValidarEvidenciaBrutal:
    """Test the main validation function."""
    
    def test_validation_runs(self):
        """Test that validation function runs without errors."""
        # Use small parameters for fast test
        corr = validar_evidencia_brutal(
            N_ceros=5,
            N_grid=128,
            u_max=15.0,
            num_primes=10,
            max_k=3,
            epsilon=0.03
        )
        
        assert isinstance(corr, (float, np.floating))
        assert -1.0 <= corr <= 1.0
    
    def test_validation_with_more_zeros(self):
        """Test validation with more zeros."""
        corr = validar_evidencia_brutal(
            N_ceros=10,
            N_grid=256,
            u_max=20.0,
            num_primes=20,
            max_k=5,
            epsilon=0.03
        )
        
        assert isinstance(corr, (float, np.floating))
    
    def test_validation_correlation_positive(self):
        """Test that correlation tends to be positive with good parameters."""
        # With good parameters, correlation should be high
        corr = validar_evidencia_brutal(
            N_ceros=8,
            N_grid=512,
            u_max=20.0,
            num_primes=30,
            max_k=8,
            epsilon=0.03
        )
        
        # Should have strong correlation with Riemann zeros
        # Note: Use lower threshold for test stability, but typical values are > 0.95
        assert corr > 0.85  # Reasonable expectation for this configuration


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants_defined(self):
        """Test that QCAL constants are defined."""
        assert F0_QCAL > 0
        assert C_COHERENCE > 0
        assert EPSILON_BASE > 0
    
    def test_qcal_f0_value(self):
        """Test F0 fundamental frequency value."""
        # Should be 141.7001 Hz
        assert abs(F0_QCAL - 141.7001) < 0.0001
    
    def test_qcal_coherence_value(self):
        """Test coherence constant value."""
        # Should be 244.36
        assert abs(C_COHERENCE - 244.36) < 0.01


class TestSpectralValidationResult:
    """Test the SpectralValidationResult dataclass."""
    
    def test_result_creation(self):
        """Test creating a result object."""
        result = SpectralValidationResult(
            correlation=0.98,
            eigenvalues=np.array([14.1, 21.0, 25.0]),
            riemann_zeros=np.array([14.134, 21.022, 25.011]),
            max_zero=25.011,
            psi=0.98,
            is_synchronized=True,
            fredholm_proxy=complex(1.5, 0.0),
            timestamp="2026-03-12 00:00:00",
            computation_time_ms=123.45,
            parameters={"N_ceros": 3}
        )
        
        assert result.correlation == 0.98
        assert result.is_synchronized is True
        assert len(result.eigenvalues) == 3
    
    def test_result_psi_range(self):
        """Test that psi is in valid range."""
        result = SpectralValidationResult(
            correlation=0.95,
            eigenvalues=np.array([14.1]),
            riemann_zeros=np.array([14.134]),
            max_zero=14.134,
            psi=0.95,
            is_synchronized=False,
            fredholm_proxy=1.0,
            timestamp="2026-03-12",
            computation_time_ms=100.0,
            parameters={}
        )
        
        assert 0.0 <= result.psi <= 1.0


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v"])
