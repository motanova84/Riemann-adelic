#!/usr/bin/env python3
"""
Tests for Berry-Keating Modular Surface Operator
================================================

Comprehensive test suite for the Berry-Keating operator on modular surface
with Vortex 8 confinement.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import sys
import pytest
import numpy as np
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from berry_keating_modular_surface import (
    ModularSurfaceHilbertSpace,
    DilationOperator,
    GeodesicPotential,
    ModularSurfaceOperator,
    is_prime_power,
    sieve_of_eratosthenes,
    F0_QCAL,
    C_QCAL
)


class TestHelperFunctions:
    """Test helper functions."""
    
    def test_is_prime_power(self):
        """Test prime power detection."""
        assert is_prime_power(2) == (True, 2, 1)
        assert is_prime_power(3) == (True, 3, 1)
        assert is_prime_power(4) == (True, 2, 2)
        assert is_prime_power(8) == (True, 2, 3)
        assert is_prime_power(9) == (True, 3, 2)
        assert is_prime_power(6) == (False, 0, 0)
        assert is_prime_power(10) == (False, 0, 0)
    
    def test_sieve_of_eratosthenes(self):
        """Test prime sieve."""
        primes = sieve_of_eratosthenes(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected


class TestModularSurfaceHilbertSpace:
    """Test modular surface Hilbert space."""
    
    def test_initialization(self):
        """Test Hilbert space initialization."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=50)
        
        assert len(hs.u_grid) == 50
        assert hs.u_grid[0] == -2.0
        assert hs.u_grid[-1] == 2.0
        assert len(hs.x_grid) == 50
        assert np.allclose(hs.x_grid, np.exp(hs.u_grid))
    
    def test_inner_product(self):
        """Test inner product."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=100)
        
        # Orthogonal states
        psi1 = np.exp(-hs.u_grid**2)
        psi2 = hs.u_grid * np.exp(-hs.u_grid**2)
        
        inner = hs.inner_product(psi1, psi2)
        assert abs(inner) < 0.1  # Nearly orthogonal
        
        # Self inner product
        self_inner = hs.inner_product(psi1, psi1)
        assert self_inner.real > 0
    
    def test_norm(self):
        """Test norm computation."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=100)
        
        psi = np.exp(-hs.u_grid**2)
        norm_psi = hs.norm(psi)
        
        assert norm_psi > 0
        
        # Normalized state
        psi_normalized = psi / norm_psi
        assert np.isclose(hs.norm(psi_normalized), 1.0, rtol=1e-2)
    
    def test_enforce_inversion_symmetry(self):
        """Test inversion symmetry enforcement."""
        hs = ModularSurfaceHilbertSpace(u_min=-3, u_max=3, n_grid=100)
        
        # Asymmetric function
        psi = np.exp(-hs.u_grid**2) * (1 + hs.u_grid)
        
        # Enforce symmetry
        psi_sym = hs.enforce_inversion_symmetry(psi)
        
        # Check ψ(u) ≈ ψ(-u)
        mid = len(psi_sym) // 2
        left = psi_sym[:mid]
        right = psi_sym[-mid:][::-1]
        
        error = np.linalg.norm(left - right) / np.linalg.norm(psi_sym)
        assert error < 0.15
    
    def test_measure_vortex_8(self):
        """Test Vortex 8 measure."""
        hs = ModularSurfaceHilbertSpace(u_min=-3, u_max=3, n_grid=100)
        
        # Perfect symmetric state with node at u=0
        psi = hs.u_grid * np.exp(-hs.u_grid**2)
        measure = hs.measure_vortex_8(psi)
        
        assert 0 <= measure <= 1
        # This should have good Vortex 8 character
        assert measure > 0.1


class TestDilationOperator:
    """Test dilation operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=50)
        dilation_op = DilationOperator(hs)
        
        assert dilation_op.hilbert_space is hs
        assert dilation_op.H_matrix is None
    
    def test_construct_matrix(self):
        """Test matrix construction."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=50)
        dilation_op = DilationOperator(hs)
        
        H = dilation_op.construct_matrix()
        
        assert H.shape == (50, 50)
        assert np.allclose(H, np.conj(H.T))  # Hermitian
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=80)
        dilation_op = DilationOperator(hs)
        
        result = dilation_op.compute_spectrum()
        
        assert len(result.eigenvalues) == 80
        assert len(result.eigenvectors) == 80
        assert result.hermiticity_error < 1e-8
        assert result.psi > 0.99
        assert all(np.isreal(result.eigenvalues))


class TestGeodesicPotential:
    """Test geodesic potential."""
    
    def test_initialization(self):
        """Test potential initialization."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=5, n_grid=100)
        primes = [2, 3, 5]
        geodesic_pot = GeodesicPotential(hs, primes=primes, max_power=2)
        
        assert len(geodesic_pot.primes) == 3
        assert geodesic_pot.max_power == 2
        assert len(geodesic_pot.geodesic_data) == 6  # 3 primes * 2 powers
    
    def test_geodesic_lengths(self):
        """Test geodesic length computation."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=5, n_grid=100)
        primes = [2, 3, 5, 7]
        geodesic_pot = GeodesicPotential(hs, primes=primes, max_power=2)
        
        # Check lengths
        for geo in geodesic_pot.geodesic_data:
            expected_length = geo['k'] * np.log(geo['p'])
            assert np.isclose(geo['length'], expected_length)
            assert geo['weight'] > 0
    
    def test_construct_matrix(self):
        """Test potential matrix construction."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=5, n_grid=100)
        primes = [2, 3, 5]
        geodesic_pot = GeodesicPotential(hs, primes=primes, max_power=2)
        
        V = geodesic_pot.construct_matrix()
        
        assert V.shape == (100, 100)
        # Should be diagonal
        assert np.allclose(V, np.diag(np.diag(V)))
        # Should be real
        assert np.allclose(V.imag, 0)
    
    def test_compute_characteristics(self):
        """Test characteristic computation."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=5, n_grid=100)
        primes = [2, 3, 5, 7, 11]
        geodesic_pot = GeodesicPotential(hs, primes=primes, max_power=2)
        
        result = geodesic_pot.compute_characteristics()
        
        assert len(result.geodesic_lengths) == 10  # 5 primes * 2 powers
        assert len(result.prime_powers) == 10
        assert result.total_strength > 0
        assert 0 < result.psi <= 1


class TestModularSurfaceOperator:
    """Test complete modular surface operator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        operator = ModularSurfaceOperator(
            u_min=-3,
            u_max=3,
            n_grid=100,
            primes=[2, 3, 5],
            max_power=2
        )
        
        assert operator.hilbert_space.n_grid == 100
        assert operator.dilation_op is not None
        assert operator.geodesic_pot is not None
        assert operator.H_total is None
    
    def test_construct_hamiltonian(self):
        """Test Hamiltonian construction."""
        operator = ModularSurfaceOperator(
            u_min=-3,
            u_max=3,
            n_grid=80,
            primes=[2, 3, 5],
            max_power=2
        )
        
        H = operator.construct_hamiltonian()
        
        assert H.shape == (80, 80)
        assert np.allclose(H, np.conj(H.T))  # Hermitian
        assert operator.H_total is not None
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        operator = ModularSurfaceOperator(
            u_min=-4,
            u_max=4,
            n_grid=150,
            primes=[2, 3, 5, 7],
            max_power=2
        )
        
        result = operator.compute_spectrum(n_riemann=20)
        
        assert len(result.eigenvalues) == 150
        assert result.hermiticity_error < 1e-8
        assert all(np.isreal(result.eigenvalues))
        assert -1 <= result.riemann_zeros_correlation <= 1
        assert 0 <= result.vortex_8_measure <= 1
        assert 0 <= result.psi <= 1
    
    def test_riemann_correlation_positive(self):
        """Test that correlation with Riemann zeros is positive."""
        operator = ModularSurfaceOperator(
            u_min=-5,
            u_max=5,
            n_grid=200,
            primes=[2, 3, 5, 7, 11],
            max_power=2
        )
        
        result = operator.compute_spectrum(n_riemann=30)
        
        # Should have positive correlation
        assert result.riemann_zeros_correlation > 0.0
    
    def test_visualize_vortex_8(self):
        """Test Vortex 8 visualization."""
        operator = ModularSurfaceOperator(
            u_min=-3,
            u_max=3,
            n_grid=100,
            primes=[2, 3, 5],
            max_power=2
        )
        
        viz = operator.visualize_vortex_8(state_index=0)
        
        assert 'u_grid' in viz
        assert 'x_grid' in viz
        assert 'psi' in viz
        assert 'eigenvalue' in viz
        assert 'vortex_8_measure' in viz
        assert len(viz['psi']) == 100


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test QCAL constants are used."""
        assert F0_QCAL == 141.7001
        assert C_QCAL == 244.36
    
    def test_result_dataclass_has_psi(self):
        """Test that all result dataclasses have psi field."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=2, n_grid=50)
        
        # Test dilation operator
        dilation_op = DilationOperator(hs)
        result_dilation = dilation_op.compute_spectrum()
        assert hasattr(result_dilation, 'psi')
        assert 0 <= result_dilation.psi <= 1
        
        # Test geodesic potential
        geodesic_pot = GeodesicPotential(hs, primes=[2, 3, 5], max_power=2)
        result_geodesic = geodesic_pot.compute_characteristics()
        assert hasattr(result_geodesic, 'psi')
        assert 0 <= result_geodesic.psi <= 1
        
        # Test complete operator
        operator = ModularSurfaceOperator(u_min=-2, u_max=2, n_grid=50, primes=[2, 3], max_power=2)
        result_complete = operator.compute_spectrum(n_riemann=10)
        assert hasattr(result_complete, 'psi')
        assert 0 <= result_complete.psi <= 1


class TestMathematicalProperties:
    """Test mathematical properties of the operator."""
    
    def test_operator_is_hermitian(self):
        """Test that operator is Hermitian."""
        operator = ModularSurfaceOperator(
            u_min=-3,
            u_max=3,
            n_grid=100,
            primes=[2, 3, 5],
            max_power=2
        )
        
        H = operator.construct_hamiltonian()
        hermiticity_error = np.linalg.norm(H - np.conj(H.T)) / np.linalg.norm(H)
        
        assert hermiticity_error < 1e-10
    
    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real."""
        operator = ModularSurfaceOperator(
            u_min=-3,
            u_max=3,
            n_grid=80,
            primes=[2, 3, 5],
            max_power=2
        )
        
        result = operator.compute_spectrum(n_riemann=10)
        
        assert all(np.isreal(result.eigenvalues))
        assert all(np.abs(result.eigenvalues.imag) < 1e-10)
    
    def test_geodesic_lengths_are_log_primes(self):
        """Test that geodesic lengths are logarithms of prime powers."""
        hs = ModularSurfaceHilbertSpace(u_min=-2, u_max=5, n_grid=100)
        primes = [2, 3, 5, 7, 11, 13]
        geodesic_pot = GeodesicPotential(hs, primes=primes, max_power=3)
        
        result = geodesic_pot.compute_characteristics()
        
        for i, (p, k) in enumerate(result.prime_powers):
            expected = k * np.log(p)
            actual = result.geodesic_lengths[i]
            assert np.isclose(actual, expected, rtol=1e-10)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
