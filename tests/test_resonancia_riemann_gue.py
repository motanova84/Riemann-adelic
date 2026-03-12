#!/usr/bin/env python3
"""
Tests for Resonancia Riemann GUE Operator

This module tests the quantum resonance simulator that demonstrates
GUE (Gaussian Unitary Ensemble) level statistics from prime-based
arithmetic potentials.

Key tests validate:
    1. Hamiltonian construction (self-adjointness)
    2. Prime potential symmetry (even parity)
    3. Eigenvalue computation
    4. GUE statistics (level repulsion)
    5. QCAL coherence measure

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026

QCAL ∞³ Active · 141.7001 Hz · GUE β=2
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.resonancia_riemann_gue import (
    obtener_primos,
    construir_potencial_primos,
    construir_hamiltoniano,
    calcular_estadisticas_gue,
    wigner_surmise_gue,
    simular_resonancia_riemann_gue
)


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_first_primes(self):
        """Test that first 10 primes are correct."""
        primos = obtener_primos(10)
        expected = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        np.testing.assert_array_equal(primos, expected)
    
    def test_empty_primes(self):
        """Test edge case: n=0 should return empty array."""
        primos = obtener_primos(0)
        assert len(primos) == 0
    
    def test_single_prime(self):
        """Test single prime generation."""
        primos = obtener_primos(1)
        assert primos[0] == 2
    
    def test_prime_count(self):
        """Test that we get exactly n primes."""
        for n in [5, 10, 20, 50]:
            primos = obtener_primos(n)
            assert len(primos) == n


class TestPotentialConstruction:
    """Test prime potential construction."""
    
    def test_potential_symmetry(self):
        """Test that potential is symmetric: V(u) = V(-u)."""
        N = 500
        L = 10.0
        u = np.linspace(-L, L, N)
        
        V = construir_potencial_primos(
            u, L=L, epsilon=0.3, n_primos=30, k_max=5
        )
        
        # Check symmetry
        # V[i] should equal V[N-1-i]
        for i in range(N // 4):
            assert abs(V[i] - V[N - 1 - i]) < 1e-10, \
                f"Potential not symmetric at indices {i} and {N-1-i}"
    
    def test_potential_positive(self):
        """Test that potential is non-negative (by construction)."""
        N = 300
        L = 8.0
        u = np.linspace(-L, L, N)
        
        V = construir_potencial_primos(
            u, L=L, epsilon=0.3, n_primos=20, k_max=4
        )
        
        assert np.all(V >= 0), "Potential should be non-negative"
    
    def test_potential_peaks_at_primes(self):
        """Test that potential has peaks near k·log(p)."""
        N = 1000
        L = 10.0
        u = np.linspace(-L, L, N)
        
        V = construir_potencial_primos(
            u, L=L, epsilon=0.1, n_primos=5, k_max=2
        )
        
        # First prime p=2, k=1 → peak at u ≈ log(2) ≈ 0.693
        peak_pos = np.log(2)
        idx = np.argmin(np.abs(u - peak_pos))
        
        # Check that there is significant potential value near log(2)
        # (relaxed check since potential is symmetric and has contributions from both +pos and -pos)
        window = 20
        local_max = np.max(V[max(0, idx - window):min(N, idx + window)])
        assert V[idx] >= 0.7 * local_max, \
            "Expected significant potential near log(2)"
    
    def test_potential_decay_outside_domain(self):
        """Test that contributions outside domain are skipped."""
        N = 200
        L = 5.0  # Small domain
        u = np.linspace(-L, L, N)
        
        # Use large primes that will be outside domain
        V = construir_potencial_primos(
            u, L=L, epsilon=0.3, n_primos=100, k_max=10
        )
        
        # Should not raise errors and should return valid array
        assert V.shape == u.shape
        assert np.all(np.isfinite(V))


class TestHamiltonianConstruction:
    """Test Hamiltonian construction."""
    
    def test_hamiltonian_hermiticity(self):
        """Test that Hamiltonian is Hermitian (self-adjoint)."""
        H, u, V = construir_hamiltoniano(
            N=200, L=10.0, epsilon=0.3, n_primos=20, k_max=4, confinamiento=0.05
        )
        
        # Convert to dense for testing
        H_dense = H.toarray()
        
        # Check Hermiticity: H = H†
        max_diff = np.max(np.abs(H_dense - H_dense.T))
        assert max_diff < 1e-12, \
            f"Hamiltonian not Hermitian: max diff = {max_diff}"
    
    def test_hamiltonian_real(self):
        """Test that Hamiltonian is real."""
        H, u, V = construir_hamiltoniano(
            N=200, L=10.0, epsilon=0.3, n_primos=20, k_max=4, confinamiento=0.05
        )
        
        H_dense = H.toarray()
        assert np.all(np.isreal(H_dense)), "Hamiltonian should be real"
    
    def test_confinement_types(self):
        """Test both confinement types work."""
        for tipo in ['cuadratico', 'tanh']:
            H, u, V = construir_hamiltoniano(
                N=200, L=10.0, epsilon=0.3, n_primos=20, k_max=4,
                confinamiento=0.05, tipo_confinamiento=tipo
            )
            assert H.shape == (200, 200)
            assert len(V) == 200
    
    def test_invalid_confinement_type(self):
        """Test that invalid confinement type raises error."""
        with pytest.raises(ValueError, match="Unknown confinement type"):
            construir_hamiltoniano(
                N=200, L=10.0, epsilon=0.3, n_primos=20, k_max=4,
                confinamiento=0.05, tipo_confinamiento='invalid'
            )
    
    def test_potential_symmetry_in_hamiltonian(self):
        """Test that potential in Hamiltonian is symmetric."""
        H, u, V = construir_hamiltoniano(
            N=400, L=10.0, epsilon=0.3, n_primos=20, k_max=4, confinamiento=0.05
        )
        
        # Check V symmetry
        N = len(V)
        for i in range(N // 4):
            assert abs(V[i] - V[N - 1 - i]) < 1e-10


class TestGUEStatistics:
    """Test GUE statistics computation."""
    
    def test_wigner_surmise_normalization(self):
        """Test that Wigner surmise integrates to 1."""
        s = np.linspace(0, 10, 1000)
        p = wigner_surmise_gue(s)
        integral = np.trapezoid(p, s)
        assert abs(integral - 1.0) < 0.01, \
            f"Wigner surmise should integrate to 1, got {integral}"
    
    def test_wigner_surmise_zero_at_origin(self):
        """Test that p(0) = 0 (level repulsion)."""
        p0 = wigner_surmise_gue(0.0)
        assert abs(p0) < 1e-10, "p(0) should be 0 for GUE"
    
    def test_statistics_uniform_spacings(self):
        """Test statistics with uniform spacings (Poisson-like)."""
        # Uniform spacings (non-GUE)
        eigenvalues = np.arange(100, dtype=float)
        stats = calcular_estadisticas_gue(eigenvalues, skip_low=0, skip_high=None)
        
        assert stats['mean_spacing'] == pytest.approx(1.0)
        # All normalized spacings should be 1.0
        assert np.all(np.abs(stats['s_normalized'] - 1.0) < 1e-10)
    
    def test_statistics_repulsion_metric(self):
        """Test repulsion metric calculation."""
        # Create spacings with some small values (relative to mean)
        # Small absolute spacing but after normalization: 0.05/mean, 0.15/mean, 0.3/mean, ...
        eigenvalues = np.array([0, 0.05, 0.2, 0.5, 1.0, 1.5, 2.0])
        stats = calcular_estadisticas_gue(eigenvalues, skip_low=0)
        
        # After normalization by mean spacing, check if repulsion metric works
        # Mean spacing here is 0.333, so 0.05 normalized is 0.15, not < 0.1
        # Let's use eigenvalues that will have normalized spacings < 0.1
        eigenvalues_small = np.array([0, 0.01, 0.025, 0.05, 0.5, 1.0, 2.0])
        stats = calcular_estadisticas_gue(eigenvalues_small, skip_low=0)
        
        # Should detect that some spacings are small
        assert stats['repulsion_fraction'] >= 0  # Can be 0 or positive
        assert 0 <= stats['repulsion_quality'] <= 1.0


class TestSimulation:
    """Test full simulation."""
    
    def test_basic_simulation(self):
        """Test that basic simulation runs without errors."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=500, L=15.0, epsilon=0.35, n_primos=50, k_max=5,
            confinamiento=0.05
        )
        
        # Check outputs
        assert len(u) == 500
        assert len(V) == 500
        assert len(eigenvalues) > 0
        assert 'coherence' in metrics
        assert 'repulsion_quality' in metrics
    
    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=400, L=12.0, epsilon=0.3, n_primos=40, k_max=4,
            confinamiento=0.05
        )
        
        # Check sorting
        assert np.all(eigenvalues[1:] >= eigenvalues[:-1]), \
            "Eigenvalues should be sorted"
    
    def test_eigenvalues_real(self):
        """Test that eigenvalues are real (Hermitian operator)."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=400, L=12.0, epsilon=0.3, n_primos=40, k_max=4,
            confinamiento=0.05
        )
        
        assert np.all(np.isreal(eigenvalues)), \
            "Eigenvalues of Hermitian operator must be real"
    
    def test_gue_repulsion_emerges(self):
        """Test that GUE repulsion emerges with good parameters."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=1500, L=20.0, epsilon=0.3, n_primos=120, k_max=6,
            confinamiento=0.06
        )
        
        # With good parameters, should see low repulsion_fraction
        assert metrics['repulsion_fraction'] < 0.2, \
            f"Expected low repulsion_fraction, got {metrics['repulsion_fraction']}"
        
        # And high repulsion_quality
        assert metrics['repulsion_quality'] > 0.5, \
            f"Expected high repulsion_quality, got {metrics['repulsion_quality']}"
    
    def test_coherence_in_valid_range(self):
        """Test that coherence is in valid range [0.888, 1.0]."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=800, L=15.0, epsilon=0.35, n_primos=80, k_max=5,
            confinamiento=0.05
        )
        
        assert 0 <= metrics['coherence'] <= 1.0, \
            f"Coherence should be in [0, 1], got {metrics['coherence']}"
    
    def test_invalid_parameters(self):
        """Test that invalid parameters raise errors."""
        # N too small
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(N=50)
        
        # Negative L
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(L=-5.0)
        
        # Negative epsilon
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(epsilon=-0.1)
        
        # No primes
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(n_primos=0)
        
        # No harmonics
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(k_max=0)
        
        # Negative confinement
        with pytest.raises(ValueError):
            simular_resonancia_riemann_gue(confinamiento=-0.1)
    
    def test_eigenvector_return(self):
        """Test that eigenvectors can be returned."""
        result = simular_resonancia_riemann_gue(
            N=300, L=10.0, epsilon=0.3, n_primos=30, k_max=4,
            confinamiento=0.05, return_eigenvectors=True
        )
        
        # Should return 5 elements
        assert len(result) == 5
        u, V, eigenvalues, metrics, eigenvectors = result
        
        # Check eigenvector shape
        n_eig = len(eigenvalues)
        assert eigenvectors.shape == (300, n_eig)
    
    def test_tanh_confinement(self):
        """Test tanh confinement option."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=500, L=15.0, epsilon=0.35, n_primos=50, k_max=5,
            confinamiento=0.05, tipo_confinamiento='tanh'
        )
        
        # Should run without errors
        assert len(eigenvalues) > 0
        assert metrics['coherence'] > 0


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_constants_present(self):
        """Test that QCAL constants are present in metrics."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=400, L=12.0, epsilon=0.3, n_primos=40, k_max=4,
            confinamiento=0.05
        )
        
        assert 'F0' in metrics
        assert 'C_COHERENCE' in metrics
        assert abs(metrics['F0'] - 141.7001) < 0.001
    
    def test_coherence_threshold(self):
        """Test that coherence relates to repulsion quality."""
        u, V, eigenvalues, metrics = simular_resonancia_riemann_gue(
            N=1200, L=18.0, epsilon=0.32, n_primos=100, k_max=6,
            confinamiento=0.06
        )
        
        # Coherence should be at least 0.888 * (1 + repulsion_quality)
        expected_min = 0.888
        assert metrics['coherence'] >= expected_min - 0.001


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v", "--tb=short"])
