#!/usr/bin/env python3
"""
Tests for Berry-Keating Omega-8 Operator
=========================================

Comprehensive test suite for the Vortex 8 confinement mechanism.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · f₀ = 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from berry_keating_omega8_operator import (
    DilationOperator,
    PrimePotential,
    Omega8Operator,
    Omega8HilbertSpace,
    sieve_of_eratosthenes,
    von_mangoldt,
    mellin_transform,
    validate_omega8_operator
)


class TestPrimeUtilities:
    """Test prime number generation and von Mangoldt function."""
    
    def test_sieve_of_eratosthenes(self):
        """Test prime sieve."""
        primes = sieve_of_eratosthenes(30)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected
    
    def test_sieve_empty(self):
        """Test sieve with limit < 2."""
        primes = sieve_of_eratosthenes(1)
        assert primes == []
    
    def test_von_mangoldt_prime(self):
        """Test von Mangoldt for primes."""
        # Λ(2) = ln(2)
        assert np.isclose(von_mangoldt(2), np.log(2))
        # Λ(3) = ln(3)
        assert np.isclose(von_mangoldt(3), np.log(3))
    
    def test_von_mangoldt_prime_power(self):
        """Test von Mangoldt for prime powers."""
        # Λ(4) = Λ(2²) = ln(2)
        assert np.isclose(von_mangoldt(4), np.log(2))
        # Λ(8) = Λ(2³) = ln(2)
        assert np.isclose(von_mangoldt(8), np.log(2))
        # Λ(9) = Λ(3²) = ln(3)
        assert np.isclose(von_mangoldt(9), np.log(3))
    
    def test_von_mangoldt_composite(self):
        """Test von Mangoldt for non-prime-powers."""
        # Λ(6) = 0 (not a prime power)
        assert von_mangoldt(6) == 0.0
        # Λ(12) = 0
        assert von_mangoldt(12) == 0.0


class TestOmega8HilbertSpace:
    """Test Vortex 8 Hilbert space construction."""
    
    def test_symmetric_gaussian_creation(self):
        """Test creation of symmetric Gaussian state."""
        hilbert = Omega8HilbertSpace.create_symmetric_gaussian(N=64)
        
        assert len(hilbert.x_grid) == 64
        assert hilbert.is_symmetric
        assert np.isclose(hilbert.norm, 1.0, atol=0.01)
    
    def test_inversion_symmetry(self):
        """Test that ψ(x) = ψ(1/x)."""
        hilbert = Omega8HilbertSpace.create_symmetric_gaussian(N=128)
        
        # For symmetric function on log grid, should be mirror symmetric
        psi = hilbert.psi_values
        assert np.allclose(psi, psi[::-1], rtol=0.01)
    
    def test_normalization(self):
        """Test that wavefunction is normalized."""
        hilbert = Omega8HilbertSpace.create_symmetric_gaussian(N=128)
        
        # Compute norm with measure dx/x
        log_x = np.log(hilbert.x_grid)
        dx_over_x = np.gradient(log_x)
        norm_sq = np.sum(np.abs(hilbert.psi_values)**2 * dx_over_x)
        
        assert np.isclose(norm_sq, 1.0, atol=0.01)


class TestDilationOperator:
    """Test the dilation operator H₀ = -i(x·∂_x + 1/2)."""
    
    def test_operator_creation(self):
        """Test operator initialization."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        dilation = DilationOperator(x_grid)
        
        assert dilation.N == 64
        assert len(dilation.log_x) == 64
    
    def test_apply_to_eigenfunction(self):
        """Test application to eigenfunction."""
        x_grid = np.exp(np.linspace(-3, 3, 128))
        dilation = DilationOperator(x_grid)
        
        # Eigenfunction: ψ_E(x) = x^(-1/2 + iE)
        E = 5.0
        psi = x_grid**(-0.5 + 1j*E)
        
        # Apply operator
        H_psi = dilation.apply(psi)
        
        # Should be approximately E·ψ
        # Note: numerical derivatives introduce errors
        expected = E * psi
        
        # Check correlation rather than exact match
        # EIGENVALUE_CORRELATION_THRESHOLD = 0.8 from constants
        # This threshold is based on numerical analysis showing that
        # correlation > 0.8 indicates good agreement between numerical
        # finite difference approximations and analytical eigenfunctions
        correlation = np.abs(np.vdot(H_psi, expected)) / (np.linalg.norm(H_psi) * np.linalg.norm(expected))
        assert correlation > 0.8  # Reasonable agreement with finite differences
    
    def test_matrix_hermiticity(self):
        """Test that H₀ matrix is Hermitian."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        dilation = DilationOperator(x_grid)
        H0 = dilation.construct_matrix()
        
        # Check Hermiticity: H = H†
        diff = np.max(np.abs(H0 - H0.conj().T))
        assert diff < 1e-10


class TestPrimePotential:
    """Test the prime-based confining potential."""
    
    def test_potential_creation(self):
        """Test potential initialization."""
        potential = PrimePotential(coupling_g=1.0, p_max=20, m_max=2)
        
        assert potential.coupling_g == 1.0
        assert potential.p_max == 20
        assert potential.m_max == 2
        assert len(potential.primes) > 0
    
    def test_potential_evaluation(self):
        """Test potential evaluation on grid."""
        potential = PrimePotential(coupling_g=0.5, p_max=30, m_max=2)
        x_grid = np.exp(np.linspace(0, 4, 100))
        
        result = potential.evaluate(x_grid, delta_width=0.1)
        
        assert len(result.V_values) == len(x_grid)
        assert result.coupling_g == 0.5
        assert len(result.primes_used) > 0
    
    def test_potential_peaks_at_primes(self):
        """Test that potential has peaks near prime powers."""
        potential = PrimePotential(coupling_g=1.0, p_max=20, m_max=1)
        
        # Grid around p=2, p=3
        x_grid = np.linspace(1.5, 3.5, 200)
        result = potential.evaluate(x_grid, delta_width=0.05)
        
        # Should have peaks near x=2 and x=3
        # Find local maxima
        V = result.V_values
        peaks = []
        for i in range(1, len(V)-1):
            if V[i] > V[i-1] and V[i] > V[i+1]:
                peaks.append(x_grid[i])
        
        # Should have peaks near 2 and 3
        assert any(abs(p - 2.0) < 0.2 for p in peaks)
        assert any(abs(p - 3.0) < 0.2 for p in peaks)
    
    def test_matrix_is_diagonal(self):
        """Test that potential matrix is diagonal."""
        potential = PrimePotential(coupling_g=0.5, p_max=20, m_max=2)
        x_grid = np.exp(np.linspace(-1, 3, 50))
        V_matrix = potential.construct_matrix(x_grid)
        
        # Check it's diagonal
        off_diagonal = V_matrix - np.diag(np.diag(V_matrix))
        assert np.max(np.abs(off_diagonal)) < 1e-10


class TestOmega8Operator:
    """Test the full Omega-8 operator."""
    
    def test_operator_creation(self):
        """Test operator initialization."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        omega8 = Omega8Operator(
            x_grid=x_grid,
            coupling_g=0.5,
            p_max=20,
            m_max=2
        )
        
        assert omega8.H_matrix.shape == (64, 64)
        assert len(omega8.potential.primes) > 0
    
    def test_hamiltonian_hermiticity(self):
        """Test that full Hamiltonian is Hermitian."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        omega8 = Omega8Operator(
            x_grid=x_grid,
            coupling_g=0.5,
            p_max=20,
            m_max=2
        )
        
        H = omega8.H_matrix
        diff = np.max(np.abs(H - H.conj().T))
        assert diff < 0.1  # Reasonable for numerical operator
    
    def test_spectrum_computation(self):
        """Test spectrum computation."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        omega8 = Omega8Operator(
            x_grid=x_grid,
            coupling_g=0.5,
            p_max=30,
            m_max=2
        )
        
        spectrum = omega8.compute_spectrum(n_zeros=10, use_mpmath=False)
        
        assert len(spectrum.eigenvalues) == 64
        assert len(spectrum.eigenvectors) == 64
        assert len(spectrum.riemann_zeros_imaginary) == 10
        assert 0.0 <= spectrum.coherence_psi <= 1.0
        assert 0.0 <= spectrum.gue_p_value <= 1.0
    
    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real (within numerical precision)."""
        x_grid = np.exp(np.linspace(-2, 2, 64))
        omega8 = Omega8Operator(
            x_grid=x_grid,
            coupling_g=0.5,
            p_max=20,
            m_max=2
        )
        
        spectrum = omega8.compute_spectrum(n_zeros=5, use_mpmath=False)
        
        # Eigenvalues should be real (imaginary part ~ 0)
        assert np.all(np.abs(spectrum.eigenvalues.imag) < 1e-10)


class TestMellinTransform:
    """Test Mellin transform utilities."""
    
    def test_mellin_of_power_function(self):
        """Test Mellin transform of x^a."""
        # M{x^a}(s) = 1/(s+a+1) for suitable s
        a = 2.0
        s = 3.0 + 0j
        
        f = lambda x: x**a
        result = mellin_transform(f, s, x_min=0.01, x_max=10.0, N=500)
        
        # This integral diverges for real s > -a-1, but we can check behavior
        # For bounded domain, result should be finite
        assert np.isfinite(result)
    
    def test_mellin_of_gaussian(self):
        """Test Mellin transform of Gaussian."""
        # M{exp(-x²)}(s) involves Gamma function
        s = 1.0 + 0j
        f = lambda x: np.exp(-x**2)
        
        result = mellin_transform(f, s, x_min=0.01, x_max=5.0, N=500)
        
        # Should be finite and positive
        assert np.isfinite(result)
        assert np.real(result) > 0


class TestValidation:
    """Test validation function."""
    
    def test_validate_omega8_operator(self):
        """Test comprehensive validation."""
        certificate = validate_omega8_operator(
            N=64,
            coupling_g=0.5,
            n_zeros=10
        )
        
        # Check certificate structure
        assert "timestamp" in certificate
        assert "operator" in certificate
        assert "eigenvalues_computed" in certificate
        assert "coherence_psi" in certificate
        assert "qcal" in certificate
        assert "status" in certificate
        
        # Check values
        assert certificate["operator"] == "Berry-Keating Omega-8"
        assert certificate["grid_size"] == 64
        assert certificate["coupling_constant"] == 0.5
        assert 0.0 <= certificate["coherence_psi"] <= 1.0
        
        # Check QCAL constants
        assert certificate["qcal"]["frequency_f0"] == 141.7001
        assert certificate["signature"] == "∴𓂀Ω∞³Φ @ 141.7001 Hz"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
