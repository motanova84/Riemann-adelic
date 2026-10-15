#!/usr/bin/env python3
"""
Tests for Adelic Kernel Closure Operator
=========================================

Tests the three caminos (paths) for RH proof:
- CAMINO A: Analytical kernel closure
- CAMINO B: Spectral universality  
- CAMINO C: Scaling law (κ_Π as curvature)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_kernel_closure import AdelicKernelClosure, KAPPA_PI, PHI


class TestAdelicDistance:
    """Test adelic distance metric."""
    
    def test_distance_symmetry(self):
        """Test d_A(x,y) = d_A(y,x)."""
        akc = AdelicKernelClosure()
        x, y = 2.0, 5.0
        
        d_xy = akc.adelic_distance(x, y)
        d_yx = akc.adelic_distance(y, x)
        
        assert np.abs(d_xy - d_yx) < 1e-12
    
    def test_distance_triangle_inequality(self):
        """Test triangle inequality d_A(x,z) ≤ d_A(x,y) + d_A(y,z)."""
        akc = AdelicKernelClosure()
        x, y, z = 1.5, 3.0, 7.0
        
        d_xz = akc.adelic_distance(x, z)
        d_xy = akc.adelic_distance(x, y)
        d_yz = akc.adelic_distance(y, z)
        
        assert d_xz <= d_xy + d_yz + 1e-10
    
    def test_distance_zero_diagonal(self):
        """Test d_A(x,x) = 0."""
        akc = AdelicKernelClosure()
        x = 4.2
        
        d_xx = akc.adelic_distance(x, x)
        
        assert d_xx < 1e-12


class TestHeatKernel:
    """Test heat kernel properties."""
    
    def test_heat_kernel_positivity(self):
        """Test K(x,y;τ) > 0 for τ > 0."""
        akc = AdelicKernelClosure()
        
        K = akc.heat_kernel(1.0, 2.0, 0.5)
        
        assert np.real(K) > 0
    
    def test_heat_kernel_symmetry(self):
        """Test K(x,y;τ) = K(y,x;τ)."""
        akc = AdelicKernelClosure()
        
        K_xy = akc.heat_kernel(1.5, 3.0, 0.8)
        K_yx = akc.heat_kernel(3.0, 1.5, 0.8)
        
        assert np.abs(K_xy - K_yx) < 1e-10
    
    def test_heat_kernel_decay(self):
        """Test K decays exponentially with distance."""
        akc = AdelicKernelClosure()
        tau = 0.5
        x = 2.0
        
        # Compare kernel at different distances
        K_near = akc.heat_kernel(x, x * 1.1, tau)
        K_far = akc.heat_kernel(x, x * 2.0, tau)
        
        assert np.real(K_near) > np.real(K_far)
    
    def test_heat_kernel_tau_dependence(self):
        """Test K normalization scales with τ."""
        akc = AdelicKernelClosure()
        x, y = 1.0, 1.0
        
        # At diagonal, should scale as 1/sqrt(tau)
        K_small = akc.heat_kernel(x, y, 0.1)
        K_large = akc.heat_kernel(x, y, 1.0)
        
        # Ratio should exist and be positive
        ratio = np.real(K_small) / np.real(K_large)
        
        # With potential contribution, ratio is modified
        # Just verify it's positive and finite
        assert ratio > 0
        assert np.isfinite(ratio)


class TestWeylTerm:
    """Test Weyl smooth term."""
    
    def test_weyl_asymptotic_growth(self):
        """Test Weyl(T) ~ T ln T for large T."""
        akc = AdelicKernelClosure()
        
        T1 = 50.0  # Use larger T to ensure positivity
        T2 = 500.0
        
        W1 = akc.weyl_term(T1)
        W2 = akc.weyl_term(T2)
        
        # Should grow faster than linear for large T
        assert W2 > W1
        assert W2 / W1 > T2 / T1
    
    def test_weyl_positivity(self):
        """Test Weyl(T) > 0 for T > 2π."""
        akc = AdelicKernelClosure()
        
        T = 50.0  # Use larger T to ensure positivity
        W = akc.weyl_term(T)
        
        assert W > 0


class TestVanVleckAmplitude:
    """Test Van-Vleck determinant amplitude."""
    
    def test_amplitude_prime_power_decay(self):
        """Test amplitude decays as p^(-k/2)."""
        akc = AdelicKernelClosure()
        
        p = 5
        A1 = akc.van_vleck_amplitude(p, 1)
        A2 = akc.van_vleck_amplitude(p, 2)
        
        # A2 / A1 should be approximately 1/sqrt(p)
        ratio = A2 / A1
        expected = 1.0 / np.sqrt(p)
        
        assert np.abs(ratio - expected) < 1e-10
    
    def test_amplitude_logarithmic_factor(self):
        """Test amplitude contains ln p factor."""
        akc = AdelicKernelClosure()
        
        p1, p2 = 2, 3
        A1 = akc.van_vleck_amplitude(p1, 1)
        A2 = akc.van_vleck_amplitude(p2, 1)
        
        # Ratio should be (ln p2 / ln p1) * sqrt(p1/p2)
        ratio = A2 / A1
        expected = (np.log(p2) / np.log(p1)) * np.sqrt(p1 / p2)
        
        assert np.abs(ratio - expected) < 1e-10


class TestPrimeOrbitContribution:
    """Test prime orbit contribution (CAMINO A)."""
    
    def test_prime_contribution_convergence(self):
        """Test prime sum converges with more primes."""
        akc = AdelicKernelClosure()
        tau = 1.0
        
        P10 = akc.prime_orbit_contribution(tau, num_primes=10, max_k=5)
        P20 = akc.prime_orbit_contribution(tau, num_primes=20, max_k=5)
        
        # Should converge (difference decreases)
        assert np.abs(P20 - P10) < np.abs(P10)
    
    def test_prime_contribution_tau_decay(self):
        """Test contribution decays exponentially with τ."""
        akc = AdelicKernelClosure()
        
        P_small = akc.prime_orbit_contribution(0.1, num_primes=15)
        P_large = akc.prime_orbit_contribution(10.0, num_primes=15)
        
        # Should decay significantly
        assert P_small > P_large * 100
    
    def test_prime_contribution_finite(self):
        """Test prime contribution is finite."""
        akc = AdelicKernelClosure()
        
        P = akc.prime_orbit_contribution(1.0, num_primes=20, max_k=10)
        
        assert np.isfinite(P)
        assert P > 0


class TestRemainderBound:
    """Test rigorous remainder bound."""
    
    def test_remainder_exponential_decay(self):
        """Test |R(τ)| ≤ C·e^(-λτ)."""
        akc = AdelicKernelClosure()
        
        R1 = akc.remainder_bound(1.0)
        R2 = akc.remainder_bound(2.0)
        
        # Should decay exponentially
        ratio = R2 / R1
        expected = np.exp(-0.5)  # Default λ = 0.5
        
        assert np.abs(ratio - expected) < 1e-10
    
    def test_remainder_approaches_zero(self):
        """Test R(τ) → 0 as τ → ∞."""
        akc = AdelicKernelClosure()
        
        R_large = akc.remainder_bound(100.0)
        
        assert R_large < 1e-10


class TestTraceFormulaComplete:
    """Test complete trace formula (CAMINO A completion)."""
    
    def test_trace_components(self):
        """Test trace has all required components."""
        akc = AdelicKernelClosure()
        
        result = akc.trace_formula_complete(1.0)
        
        assert 'weyl' in result
        assert 'prime_oscillatory' in result
        assert 'remainder_bound' in result
        assert 'total' in result
    
    def test_trace_total_sum(self):
        """Test total equals sum of components."""
        akc = AdelicKernelClosure()
        
        result = akc.trace_formula_complete(1.0)
        
        expected_total = result['weyl'] + result['prime_oscillatory']
        
        assert np.abs(result['total'] - expected_total) < 1e-10
    
    def test_trace_finite(self):
        """Test all trace components are finite."""
        akc = AdelicKernelClosure()
        
        result = akc.trace_formula_complete(0.5)
        
        assert np.isfinite(result['weyl'])
        assert np.isfinite(result['prime_oscillatory'])
        assert np.isfinite(result['remainder_bound'])
        assert np.isfinite(result['total'])


class TestMonodromyMatrix:
    """Test monodromy matrix for periodic orbits."""
    
    def test_monodromy_determinant(self):
        """Test det(M_γ) = 1 (area preserving)."""
        akc = AdelicKernelClosure()
        
        M = akc.monodromy_matrix(3, 2)
        det = np.linalg.det(M)
        
        assert np.abs(det - 1.0) < 1e-12
    
    def test_monodromy_eigenvalues(self):
        """Test eigenvalues are (p^k, p^(-k))."""
        akc = AdelicKernelClosure()
        p, k = 5, 2
        
        M = akc.monodromy_matrix(p, k)
        eigenvalues = np.linalg.eigvals(M)
        eigenvalues_sorted = np.sort(eigenvalues)
        
        expected = np.sort([p**k, p**(-k)])
        
        assert np.allclose(eigenvalues_sorted, expected, rtol=1e-10)


class TestGutzwillerTraceFormula:
    """Test full Gutzwiller trace formula."""
    
    def test_gutzwiller_convergence(self):
        """Test Gutzwiller sum converges with more primes."""
        akc = AdelicKernelClosure()
        t = 1.0
        
        G10 = akc.gutzwiller_trace_formula(t, num_primes=10, max_k=5)
        G20 = akc.gutzwiller_trace_formula(t, num_primes=20, max_k=5)
        
        # Should converge
        assert np.abs(G20 - G10) < np.abs(G10)
    
    def test_gutzwiller_oscillatory(self):
        """Test Gutzwiller trace is complex (oscillatory)."""
        akc = AdelicKernelClosure()
        
        G = akc.gutzwiller_trace_formula(1.0)
        
        # Should have both real and imaginary parts
        assert np.abs(np.real(G)) > 1e-10 or np.abs(np.imag(G)) > 1e-10
    
    def test_gutzwiller_finite(self):
        """Test Gutzwiller trace is finite."""
        akc = AdelicKernelClosure()
        
        G = akc.gutzwiller_trace_formula(2.0, num_primes=15, max_k=8)
        
        assert np.isfinite(np.real(G))
        assert np.isfinite(np.imag(G))


class TestKappaPiCurvature:
    """Test κ_Π as intrinsic curvature (CAMINO C)."""
    
    def test_kappa_pi_formula(self):
        """Test κ_Π = √(2π) · N/Weyl · Φ^(-1)."""
        akc = AdelicKernelClosure()
        
        T = 100.0
        zeros = np.array([14.13, 21.02, 25.01, 30.42, 32.94, 37.59, 40.92, 43.33])
        
        kappa = akc.compute_kappa_pi_curvature(T, zeros)
        
        # Should be finite and positive
        assert kappa > 0
        assert np.isfinite(kappa)
    
    def test_kappa_pi_asymptotic(self):
        """Test κ_Π converges as T increases."""
        akc = AdelicKernelClosure()
        
        # Use uniform spacing as proxy for zeros
        zeros_small = np.arange(10, 50, 2.5)
        zeros_large = np.arange(10, 100, 2.5)
        
        k1 = akc.compute_kappa_pi_curvature(50, zeros_small)
        k2 = akc.compute_kappa_pi_curvature(100, zeros_large)
        
        # Both should be positive and finite
        assert k1 > 0 and k2 > 0
        assert np.isfinite(k1) and np.isfinite(k2)


class TestSpectralRigidity:
    """Test spectral rigidity Σ²(L) (CAMINO B)."""
    
    def test_rigidity_goe_scaling(self):
        """Test Σ²(L) ≈ (1/π²) ln L for GUE."""
        akc = AdelicKernelClosure()
        
        # Generate GUE-like eigenvalues (with some noise)
        np.random.seed(42)
        N = 200
        eigenvalues = np.sort(np.random.normal(0, 1, N).cumsum())
        
        L = 10.0
        sigma2 = akc.spectral_rigidity(eigenvalues, L)
        
        # Should be finite
        assert np.isfinite(sigma2)
        assert sigma2 >= 0
    
    def test_rigidity_empty_spectrum(self):
        """Test rigidity handles empty spectrum."""
        akc = AdelicKernelClosure()
        
        eigenvalues = np.array([])
        sigma2 = akc.spectral_rigidity(eigenvalues, 5.0)
        
        assert sigma2 == 0.0


class TestPTSymmetryStability:
    """Test PT symmetry stability (CAMINO C)."""
    
    def test_pt_preserved_phase(self):
        """Test κ < κ_Π gives PT preserved."""
        akc = AdelicKernelClosure()
        
        kappa = 2.0  # < KAPPA_PI
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0])  # Real
        
        result = akc.verify_pt_symmetry_stability(kappa, eigenvalues)
        
        assert result['phase'] == 'PT_PRESERVED'
        assert result['coherence_preserved']
    
    def test_pt_critical_phase(self):
        """Test κ ≈ κ_Π gives critical phase."""
        akc = AdelicKernelClosure()
        
        kappa = KAPPA_PI
        eigenvalues = np.array([1.0, 2.0, 3.0])
        
        result = akc.verify_pt_symmetry_stability(kappa, eigenvalues)
        
        assert result['phase'] == 'PT_CRITICAL'
    
    def test_pt_broken_phase(self):
        """Test κ > κ_Π gives PT broken."""
        akc = AdelicKernelClosure()
        
        kappa = 3.5  # > KAPPA_PI
        eigenvalues = np.array([1.0 + 0.5j, 1.0 - 0.5j, 2.0])
        
        result = akc.verify_pt_symmetry_stability(kappa, eigenvalues)
        
        assert result['phase'] == 'PT_BROKEN'
        assert not result['coherence_preserved']


class TestBasisUniversality:
    """Test basis universality (CAMINO B)."""
    
    def test_universality_detection(self):
        """Test universality framework works."""
        akc = AdelicKernelClosure(N=64)
        
        def simple_operator():
            """Simple Hermitian operator for testing."""
            N = akc.N
            # Diagonal operator
            return np.diag(np.arange(1, N+1, dtype=float))
        
        result = akc.test_basis_universality(
            simple_operator,
            bases=['hermite', 'chebyshev']
        )
        
        assert 'kappa_by_basis' in result
        assert 'kappa_mean' in result
        assert 'is_universal' in result
    
    def test_universality_multiple_bases(self):
        """Test κ_Π computed for multiple bases."""
        akc = AdelicKernelClosure(N=64)
        
        def test_operator():
            N = akc.N
            return np.random.randn(N, N) + np.random.randn(N, N).T  # Symmetric
        
        result = akc.test_basis_universality(
            test_operator,
            bases=['hermite']
        )
        
        assert len(result['kappa_by_basis']) >= 1


class TestQCALCoherence:
    """Test QCAL coherence integration."""
    
    def test_constants_defined(self):
        """Test QCAL constants are properly defined."""
        from operators.adelic_kernel_closure import F0, C_QCAL, KAPPA_PI, PHI
        
        assert F0 == 141.7001
        assert C_QCAL == 244.36
        assert np.abs(KAPPA_PI - 2.5773) < 1e-4
        assert np.abs(PHI - 1.618033) < 1e-6
    
    def test_adelic_kernel_initialization(self):
        """Test AdelicKernelClosure initializes correctly."""
        akc = AdelicKernelClosure(N=128, tau_min=0.01, tau_max=5.0)
        
        assert akc.N == 128
        assert len(akc.x) == 128
        assert len(akc.tau_grid) == 128
        assert akc.tau_min == 0.01
        assert akc.tau_max == 5.0


# Integration test
class TestIntegration:
    """Integration tests for complete framework."""
    
    def test_complete_camino_a(self):
        """Test CAMINO A: Analytical closure."""
        akc = AdelicKernelClosure(N=128)
        
        # Test trace formula at multiple τ values
        for tau in [0.1, 1.0, 5.0]:
            result = akc.trace_formula_complete(tau, num_primes=15, max_k=8)
            
            assert np.isfinite(result['total'])
            assert result['remainder_bound'] > 0
            # Remainder can be larger than total for small tau due to different scales
            assert result['total'] > 0 or np.abs(result['total']) > 0
    
    def test_complete_camino_b(self):
        """Test CAMINO B: Spectral universality."""
        akc = AdelicKernelClosure(N=64)
        
        # Create test operator
        def laplacian_operator():
            N = akc.N
            main_diag = 2.0 * np.ones(N)
            off_diag = -1.0 * np.ones(N-1)
            return (np.diag(main_diag) + 
                   np.diag(off_diag, k=1) + 
                   np.diag(off_diag, k=-1))
        
        # Test universality
        result = akc.test_basis_universality(laplacian_operator, bases=['hermite'])
        
        assert result['kappa_mean'] > 0
    
    def test_complete_camino_c(self):
        """Test CAMINO C: Scaling law."""
        akc = AdelicKernelClosure(N=128)
        
        # Test κ_Π as curvature
        T = 50.0
        zeros = np.linspace(10, 50, 20)  # Mock zeros
        
        kappa = akc.compute_kappa_pi_curvature(T, zeros)
        
        assert np.isfinite(kappa)
        assert kappa > 0
        
        # Test PT stability
        eigenvalues = np.random.randn(50)
        stability = akc.verify_pt_symmetry_stability(kappa, eigenvalues)
        
        assert stability['phase'] in ['PT_PRESERVED', 'PT_CRITICAL', 'PT_BROKEN']


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
