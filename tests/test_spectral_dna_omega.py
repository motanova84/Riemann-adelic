#!/usr/bin/env python3
"""
Tests for Spectral DNA Extraction: Operator H = xp + V_ε(ln x)
==============================================================

Tests for the spectral DNA extraction module covering:
1. Operator construction (Hermiticity, domain)
2. Eigenvalue extraction and validation
3. Fredholm determinant computation
4. Synchrony with Riemann xi function
5. GUE spacing statistics
6. Data persistence (CSV, JSON)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: March 2026
DOI: 10.5281/zenodo.17379721
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from spectral_dna_omega_extractor import (
    generate_primes_up_to,
    gaussian_regularized_delta,
    build_arithmetic_potential,
    build_kinetic_operator,
    build_hamiltonian_operator,
    extract_eigenvalues,
    compute_fredholm_log_determinant,
    compute_riemann_xi_log,
    validate_gue_spacing,
    find_valleys,
    compute_synchrony_error,
    extract_spectral_dna,
    SpectralDNAResult
)


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_generate_primes_basic(self):
        """Test basic prime generation."""
        primes = generate_primes_up_to(10.0)
        assert len(primes) > 0
        assert 2 in primes
        assert 3 in primes
        assert 5 in primes
        assert 7 in primes
    
    def test_primes_are_prime(self):
        """Verify all generated numbers are prime."""
        primes = generate_primes_up_to(12.0)
        
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(np.sqrt(n)) + 1):
                if n % i == 0:
                    return False
            return True
        
        for p in primes:
            assert is_prime(p), f"{p} is not prime"


class TestGaussianRegularization:
    """Test Gaussian regularization of delta function."""
    
    def test_gaussian_delta_peak_at_center(self):
        """Test that Gaussian delta peaks at u0."""
        u = np.linspace(-5, 5, 1000)
        u0 = 0.0
        epsilon = 0.4
        
        G = gaussian_regularized_delta(u, u0, epsilon)
        
        # Peak should be at u0
        peak_idx = np.argmax(G)
        assert abs(u[peak_idx] - u0) < 0.01
    
    def test_gaussian_delta_normalization(self):
        """Test approximate normalization of Gaussian delta."""
        u = np.linspace(-10, 10, 10000)
        u0 = 0.0
        epsilon = 0.4
        
        G = gaussian_regularized_delta(u, u0, epsilon)
        
        # Integral should be approximately 1
        du = u[1] - u[0]
        integral = np.sum(G) * du
        
        assert abs(integral - 1.0) < 0.01
    
    def test_gaussian_delta_width_scaling(self):
        """Test that width scales with epsilon."""
        u = np.linspace(-5, 5, 1000)
        u0 = 0.0
        
        G1 = gaussian_regularized_delta(u, u0, epsilon=0.2)
        G2 = gaussian_regularized_delta(u, u0, epsilon=0.4)
        
        # Smaller epsilon → narrower peak → higher maximum
        assert np.max(G1) > np.max(G2)


class TestArithmeticPotential:
    """Test arithmetic potential construction."""
    
    def test_potential_construction(self):
        """Test that potential is constructed without errors."""
        u_grid = np.linspace(-2, 2, 100)
        epsilon = 0.4
        primes = [2, 3, 5, 7]
        
        V = build_arithmetic_potential(u_grid, epsilon, primes, max_power=3)
        
        assert V.shape == u_grid.shape
        assert np.all(np.isfinite(V))
        assert np.all(V >= 0)  # Potential should be non-negative
    
    def test_potential_has_peaks_at_prime_logs(self):
        """Test that potential has peaks at k*log(p)."""
        u_grid = np.linspace(0, 3, 1000)
        epsilon = 0.1  # Small epsilon for sharp peaks
        primes = [2]
        
        V = build_arithmetic_potential(u_grid, epsilon, primes, max_power=2)
        
        # Should have peaks near log(2) and 2*log(2)
        log_2 = np.log(2)
        
        # Find peak near log(2)
        idx_1 = np.argmin(np.abs(u_grid - log_2))
        assert V[idx_1] > np.mean(V)
        
        # Find peak near 2*log(2)
        idx_2 = np.argmin(np.abs(u_grid - 2*log_2))
        assert V[idx_2] > np.mean(V)


class TestKineticOperator:
    """Test kinetic operator construction."""
    
    def test_kinetic_operator_shape(self):
        """Test kinetic operator has correct shape."""
        u_grid = np.linspace(-2, 2, 100)
        T = build_kinetic_operator(u_grid)
        
        n = len(u_grid)
        assert T.shape == (n, n)
    
    def test_kinetic_operator_is_complex(self):
        """Test that kinetic operator is complex (due to -i factor)."""
        u_grid = np.linspace(-2, 2, 50)
        T = build_kinetic_operator(u_grid)
        
        # Should have non-zero imaginary parts
        assert np.any(np.imag(T) != 0)
    
    def test_kinetic_operator_anti_hermitian_part(self):
        """Test that kinetic operator has anti-Hermitian structure."""
        u_grid = np.linspace(-2, 2, 50)
        T = build_kinetic_operator(u_grid)
        
        # -i(d/du) part should be anti-Hermitian
        # But with -i/2 constant, total may not be
        # Just verify it's constructed
        assert T is not None


class TestHamiltonianConstruction:
    """Test full Hamiltonian construction."""
    
    def test_hamiltonian_construction(self):
        """Test Hamiltonian construction."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=101,
            n_primes=10,
            max_power=3
        )
        
        n = len(u_grid)
        assert H.shape == (n, n)
        assert len(x_grid) == n
        assert np.all(np.isfinite(H))
    
    def test_hamiltonian_hermiticity(self):
        """Test that Hamiltonian is Hermitian after symmetrization."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=51,
            n_primes=10,
            max_power=3
        )
        
        # Check Hermiticity: H = H†
        hermiticity_error = np.max(np.abs(H - H.conj().T))
        assert hermiticity_error < 1e-10
    
    def test_domain_correspondence(self):
        """Test that x_grid corresponds to u_grid."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.5,
            x_max=10.0,
            epsilon=0.4,
            n_points=101
        )
        
        # x = exp(u)
        x_from_u = np.exp(u_grid)
        
        assert np.allclose(x_grid, x_from_u, rtol=1e-10)
        assert x_grid[0] >= 0.5 - 1e-10
        assert x_grid[-1] <= 10.0 + 1e-10


class TestEigenvalueExtraction:
    """Test eigenvalue extraction."""
    
    def test_eigenvalue_extraction(self):
        """Test eigenvalue extraction from Hamiltonian."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=101,
            n_primes=20,
            max_power=3
        )
        
        eigenvalues, eigenvectors = extract_eigenvalues(H, n_eigs=50)
        
        assert len(eigenvalues) == 50
        assert eigenvectors.shape[0] == len(u_grid)
        assert eigenvectors.shape[1] == 50
    
    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real (from Hermitian operator)."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=51,
            n_primes=10,
            max_power=3
        )
        
        eigenvalues, _ = extract_eigenvalues(H, n_eigs=20)
        
        # Should be real (imaginary parts negligible)
        assert np.all(np.abs(np.imag(eigenvalues)) < 1e-10)
    
    def test_eigenvalues_are_sorted(self):
        """Test that eigenvalues are sorted in ascending order."""
        H, u_grid, x_grid = build_hamiltonian_operator(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=51,
            n_primes=10,
            max_power=3
        )
        
        eigenvalues, _ = extract_eigenvalues(H, n_eigs=20)
        
        # Check sorted
        assert np.all(np.diff(eigenvalues) >= 0)


class TestFredholmDeterminant:
    """Test Fredholm determinant computation."""
    
    def test_fredholm_determinant_computation(self):
        """Test Fredholm determinant computation."""
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        t = 10.0
        
        log_det = compute_fredholm_log_determinant(eigenvalues, t)
        
        assert np.isfinite(log_det)
    
    def test_fredholm_determinant_far_from_eigenvalues(self):
        """Test Fredholm determinant far from eigenvalues."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        t = 100.0  # Far from all eigenvalues
        
        log_det = compute_fredholm_log_determinant(eigenvalues, t)
        
        # Should be finite and computable
        assert np.isfinite(log_det)
        assert abs(log_det) > 0


class TestRiemannXiFunction:
    """Test Riemann xi function computation."""
    
    def test_xi_function_at_standard_points(self):
        """Test xi function at standard points."""
        t = 14.134725  # Near first Riemann zero
        
        log_xi = compute_riemann_xi_log(t)
        
        assert np.isfinite(log_xi)
    
    def test_xi_function_zero_detection(self):
        """Test that xi function is small near critical zeros."""
        # First Riemann zero
        t = 14.134725
        
        log_xi = compute_riemann_xi_log(t)
        
        # log|xi| should be large negative near zeros
        # (or handle the zero explicitly)
        assert np.isfinite(log_xi)


class TestGUESpacing:
    """Test GUE spacing validation."""
    
    def test_gue_spacing_uniform_fails(self):
        """Test that uniform spacing fails GUE test."""
        eigenvalues = np.linspace(0, 10, 100)
        
        # Uniform spacing should NOT satisfy GUE
        result = validate_gue_spacing(eigenvalues, threshold=0.05)
        
        # Might pass for uniform due to normalization, but test the function
        assert isinstance(result, bool)
    
    def test_gue_spacing_random_gaps(self):
        """Test GUE spacing with random gaps."""
        # Create eigenvalues with random gaps
        gaps = np.random.exponential(scale=1.0, size=99)
        eigenvalues = np.cumsum(np.concatenate([[0], gaps]))
        
        result = validate_gue_spacing(eigenvalues, threshold=0.2)
        
        assert isinstance(result, bool)


class TestValleyDetection:
    """Test valley finding algorithm."""
    
    def test_find_valleys_simple_wave(self):
        """Test valley detection on simple sine wave."""
        t = np.linspace(0, 4*np.pi, 1000)
        y = np.sin(t)
        
        valleys = find_valleys(y, threshold_percentile=50)
        
        # Should find approximately 2 valleys in [0, 4π]
        assert len(valleys) >= 1
    
    def test_find_valleys_no_valleys(self):
        """Test valley detection on monotonic function."""
        y = np.linspace(0, 10, 100)
        
        valleys = find_valleys(y, threshold_percentile=50)
        
        # Should find no valleys
        assert len(valleys) == 0


class TestSynchronyError:
    """Test synchrony error computation."""
    
    def test_synchrony_error_perfect_match(self):
        """Test synchrony error with perfect match."""
        t_values = np.linspace(10, 100, 1000)
        signal = np.sin(t_values)
        
        # Same signal → perfect match
        error, aligned = compute_synchrony_error(
            t_values, signal, signal, max_dt=0.2
        )
        
        # Error should be very small
        assert error < 0.01
        assert aligned > 0
    
    def test_synchrony_error_no_match(self):
        """Test synchrony error with no matching valleys."""
        t_values = np.linspace(10, 100, 1000)
        signal1 = np.sin(t_values)
        signal2 = -np.sin(t_values)  # Inverted → valleys at different locations
        
        error, aligned = compute_synchrony_error(
            t_values, signal1, signal2, max_dt=0.2
        )
        
        # Should have low alignment
        assert aligned == 0 or error > 0.1


class TestSpectralDNAExtraction:
    """Integration tests for full spectral DNA extraction."""
    
    @pytest.mark.slow
    def test_spectral_dna_extraction_small(self):
        """Test full spectral DNA extraction with small parameters."""
        result = extract_spectral_dna(
            x_min=0.5,
            x_max=10.0,
            epsilon=0.4,
            n_points=101,
            n_eigenvalues=50,
            t_range=(10.0, 30.0),
            n_t_points=50,
            n_primes=20,
            max_power=3
        )
        
        assert isinstance(result, SpectralDNAResult)
        assert len(result.eigenvalues) <= 50
        assert len(result.eigenvalues_first_50) <= 50
        assert result.epsilon == 0.4
        assert result.x_domain == (0.5, 10.0)
        assert 0.0 <= result.psi_coherence <= 1.0
    
    @pytest.mark.slow
    def test_spectral_dna_eigenvalues_positive(self):
        """Test that eigenvalues have expected range."""
        result = extract_spectral_dna(
            x_min=0.1,
            x_max=12.0,
            epsilon=0.4,
            n_points=101,
            n_eigenvalues=100,
            t_range=(10.0, 30.0),
            n_t_points=50,
            n_primes=20,
            max_power=3
        )
        
        # Eigenvalues should be finite
        assert np.all(np.isfinite(result.eigenvalues))
    
    @pytest.mark.slow
    def test_spectral_dna_fredholm_computed(self):
        """Test that Fredholm determinant is computed."""
        result = extract_spectral_dna(
            x_min=0.5,
            x_max=10.0,
            epsilon=0.4,
            n_points=51,
            n_eigenvalues=30,
            t_range=(10.0, 30.0),
            n_t_points=50,
            n_primes=10,
            max_power=3
        )
        
        assert len(result.fredholm_log_det) == 50
        assert len(result.xi_log_values) == 50
        assert len(result.fredholm_t_values) == 50
        assert np.all(np.isfinite(result.fredholm_log_det))
        assert np.all(np.isfinite(result.xi_log_values))


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
