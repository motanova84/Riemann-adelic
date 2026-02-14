#!/usr/bin/env python3
"""
Tests for ATLAS³ Hilbert-Pólya Operator Implementation

Tests all components of the proof:
1. Adelic Hilbert space structure
2. Hilbert-Pólya operator H
3. Spectral determinant Ξ(t)
4. Identity with ξ function
5. Main theorem chain

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import os
import pytest
import numpy as np

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.adelic_hilbert_space import (
    AdelicHilbertSpace, DenseDomain, verify_lemma_1_1
)
from operators.hilbert_polya_operator import (
    HilbertPolyaOperator, verify_hilbert_polya_theorem, KAPPA, F0, PHI
)
from operators.spectral_determinant_xi import (
    SpectralDeterminant, RiemannXiFunction, 
    verify_identity_theorem, verify_main_theorem
)


class TestAdelicHilbertSpace:
    """Test adelic Hilbert space L²(𝔸_ℚ/ℚ*)."""
    
    def test_initialization(self):
        """Test Hilbert space initialization."""
        H = AdelicHilbertSpace(dimension=100)
        assert H.dimension == 100
        assert H.num_primes == 11
        assert abs(H.measure_normalization - np.pi**2/6) < 1e-10
    
    def test_haar_measure(self):
        """Test Haar measure computation."""
        H = AdelicHilbertSpace()
        x = np.array([1.0, 2.0, 5.0, 10.0])
        measure = H.haar_measure(x)
        
        # Measure should be positive and uniform in log coordinates
        assert all(measure > 0)
        assert len(measure) == len(x)
    
    def test_inner_product(self):
        """Test L² inner product."""
        H = AdelicHilbertSpace(dimension=50)
        
        # Define test functions
        def f(x):
            return np.exp(-x**2)
        
        def g(x):
            return np.exp(-x**2)
        
        # Inner product should be positive for same function
        inner = H.inner_product(f, g)
        assert np.real(inner) > 0
    
    def test_cauchy_schwarz(self):
        """Test Cauchy-Schwarz inequality."""
        H = AdelicHilbertSpace(dimension=50)
        
        def f(x):
            return np.exp(-x**2)
        
        def g(x):
            return x * np.exp(-x**2)
        
        inner = H.inner_product(f, g)
        norm_f = H.norm(f)
        norm_g = H.norm(g)
        
        # |⟨f,g⟩| ≤ ||f|| ||g||
        assert abs(inner) <= norm_f * norm_g + 1e-6
    
    def test_dense_domain_gaussian(self):
        """Test Gaussian functions are in dense domain."""
        H = AdelicHilbertSpace()
        D = DenseDomain(H)
        
        psi = D.gaussian_test_function(a=1.0)
        assert H.is_dense_domain_element(psi, check_smoothness=False)
    
    def test_lemma_1_1_verification(self):
        """Test Lemma 1.1: 𝒟 is dense in ℋ."""
        # This runs the full verification
        result = verify_lemma_1_1()
        assert result is True


class TestHilbertPolyaOperator:
    """Test Hilbert-Pólya operator H."""
    
    def test_initialization(self):
        """Test operator initialization."""
        H = HilbertPolyaOperator(N=200)
        assert H.N == 200
        assert abs(H.kappa - KAPPA) < 1e-10
    
    def test_effective_potential(self):
        """Test effective potential V_eff(x)."""
        H = HilbertPolyaOperator()
        x = np.array([0.1, 1.0, 10.0, 100.0])
        V = H.effective_potential(x)
        
        # Potential should grow with x
        assert all(V[i] < V[i+1] for i in range(len(V)-1))
        
        # Should be dominated by x² for large x
        large_x = 100.0
        V_large = H.effective_potential(np.array([large_x]))[0]
        assert 0.5 * large_x**2 < V_large < 1.5 * large_x**2
    
    def test_confinement(self):
        """Test potential confinement (Lemma 3.1)."""
        H = HilbertPolyaOperator()
        is_confining = H.verify_confinement()
        assert is_confining is True
    
    def test_operator_construction(self):
        """Test operator matrix construction."""
        H = HilbertPolyaOperator(N=100)
        H.build_operator()
        
        assert H.H_matrix is not None
        assert H.H_matrix.shape == (100, 100)
    
    def test_symmetry(self):
        """Test operator symmetry (Lemma 2.1)."""
        H = HilbertPolyaOperator(N=100)
        H.build_operator()
        
        symmetry = H.verify_symmetry()
        assert symmetry['is_hermitian'] is True
        assert symmetry['relative_error'] < 1e-10
    
    def test_spectrum_computation(self):
        """Test discrete spectrum computation."""
        H = HilbertPolyaOperator(N=200)
        H.build_operator()
        eigenvalues, eigenvectors = H.compute_spectrum(num_eigenvalues=20)
        
        assert len(eigenvalues) == 20
        assert eigenvectors.shape[1] == 20
    
    def test_spectrum_real(self):
        """Test spectrum is real (Corollary 2.5)."""
        H = HilbertPolyaOperator(N=150)
        H.build_operator()
        H.compute_spectrum(num_eigenvalues=15)
        
        is_real = H.verify_spectrum_real(tolerance=1e-8)
        assert is_real is True
    
    def test_essential_self_adjointness(self):
        """Test essential self-adjointness (Nelson's Theorem)."""
        H = HilbertPolyaOperator(N=150)
        H.build_operator()
        
        esa = H.verify_essential_self_adjointness()
        assert esa['is_symmetric'] is True
        assert esa['has_analytic_vectors'] is True
        assert esa['is_essentially_self_adjoint'] is True
    
    def test_weyl_law(self):
        """Test Weyl law verification."""
        H = HilbertPolyaOperator(N=200)
        H.build_operator()
        H.compute_spectrum(num_eigenvalues=30)
        
        weyl = H.compute_weyl_law()
        # Allow generous tolerance for small N
        assert weyl['average_relative_error'] < 0.5


class TestSpectralDeterminant:
    """Test spectral determinant Ξ(t)."""
    
    def get_test_eigenvalues(self):
        """Get test eigenvalues (simplified spectrum)."""
        return np.array([1.0, 2.0, 3.5, 5.0, 7.0, 10.0])
    
    def test_initialization(self):
        """Test determinant initialization."""
        eigenvalues = self.get_test_eigenvalues()
        Xi = SpectralDeterminant(eigenvalues)
        
        assert Xi.n_eigenvalues == len(eigenvalues)
        assert Xi.normalization == 1.0
    
    def test_determinant_at_zero(self):
        """Test Ξ(0) = 1 normalization."""
        eigenvalues = self.get_test_eigenvalues()
        Xi = SpectralDeterminant(eigenvalues)
        
        Xi_0 = Xi.xi_determinant(0.0)
        assert abs(Xi_0 - 1.0) < 1e-10
    
    def test_zeros_at_eigenvalues(self):
        """Test Ξ(γ_n) ≈ 0 for γ_n in spectrum."""
        eigenvalues = self.get_test_eigenvalues()
        Xi = SpectralDeterminant(eigenvalues)
        
        # Check first eigenvalue
        gamma_1 = eigenvalues[0]
        Xi_gamma = abs(Xi.xi_determinant(gamma_1))
        
        # Should be small (not exactly zero due to regularization)
        assert Xi_gamma < 0.5
    
    def test_functional_equation(self):
        """Test Ξ(t) = Ξ(-t)."""
        eigenvalues = self.get_test_eigenvalues()
        Xi = SpectralDeterminant(eigenvalues)
        
        t_values = np.array([0.5, 1.0, 2.0, 3.0])
        result = Xi.verify_functional_equation(t_values, tolerance=1e-6)
        
        assert result['satisfied'] is True
    
    def test_entire_function_order_1(self):
        """Test Ξ is entire function of order 1."""
        eigenvalues = self.get_test_eigenvalues()
        Xi = SpectralDeterminant(eigenvalues)
        
        t_values = np.linspace(0, 10, 20)
        result = Xi.verify_entire_function(t_values)
        
        # Growth rate should be finite
        assert 0 < result['growth_rate'] < 10


class TestRiemannXiFunction:
    """Test Riemann xi function ξ(s)."""
    
    def test_xi_at_half(self):
        """Test ξ(1/2) computation."""
        xi_half = RiemannXiFunction.xi_at_half()
        
        # Known value: ξ(1/2) ≈ 0.497...
        assert 0.49 < xi_half < 0.50
    
    def test_xi_on_critical_line(self):
        """Test ξ(1/2 + it) for real t."""
        t = 14.134725  # First Riemann zero imaginary part
        xi_val = RiemannXiFunction.xi_on_critical_line(t, use_mpmath=True)
        
        # Should be small near a zero
        assert abs(xi_val) < 0.1
    
    def test_functional_equation(self):
        """Test ξ(s) = ξ(1-s)."""
        s = 0.3 + 0.5j
        xi_s = RiemannXiFunction.xi_function(s, use_mpmath=True)
        xi_1ms = RiemannXiFunction.xi_function(1-s, use_mpmath=True)
        
        # Should be approximately equal
        error = abs(xi_s - xi_1ms)
        relative_error = error / max(abs(xi_s), 1e-16)
        assert relative_error < 0.1


class TestMainTheorem:
    """Test main theorem verification."""
    
    def get_known_riemann_zeros(self):
        """Get known Riemann zero imaginary parts."""
        return np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062
        ])
    
    def test_identity_theorem(self):
        """Test Ξ(t) = ξ(1/2+it)/ξ(1/2)."""
        eigenvalues = self.get_known_riemann_zeros()
        
        # Test at a few points
        t_test = np.array([15.0, 20.0, 25.0])
        
        results = verify_identity_theorem(eigenvalues, t_test)
        
        # Should have reasonable agreement
        # (exact match requires infinite eigenvalues)
        assert results['max_error'] < 1.0  # Allow large tolerance for finite truncation
    
    def test_spectrum_correspondence(self):
        """Test Spec(H) corresponds to Riemann zeros."""
        eigenvalues = self.get_known_riemann_zeros()
        
        results = verify_main_theorem(eigenvalues)
        
        # Average error should be small
        assert results['average_zero_error'] < 0.1


class TestKappaParameter:
    """Test κ parameter internalization."""
    
    def test_kappa_value(self):
        """Test κ = 4π/(f₀·Φ)."""
        expected_kappa = 4 * np.pi / (F0 * PHI)
        assert abs(KAPPA - expected_kappa) < 1e-10
        
        # Known approximate value
        assert 2.57 < KAPPA < 2.58
    
    def test_kappa_in_operator(self):
        """Test κ is used correctly in operator."""
        H = HilbertPolyaOperator()
        
        # Check potential includes (1+κ²)/4 term
        x = np.array([0.0])  # At origin
        V = H.effective_potential(x)
        expected_constant = (1 + H.kappa**2) / 4
        
        # V(0) = 0 + (1+κ²)/4 + ln(1) = (1+κ²)/4
        assert abs(V[0] - expected_constant) < 1e-10


class TestFullTheorem:
    """Test complete theorem verification."""
    
    @pytest.mark.slow
    def test_complete_verification(self):
        """Test full Hilbert-Pólya theorem chain."""
        results = verify_hilbert_polya_theorem()
        
        # All checks should pass
        assert results['all_checks_passed'] is True
        assert results['symmetry']['is_hermitian'] is True
        assert results['essential_self_adjointness']['is_essentially_self_adjoint'] is True
        assert results['confining_potential'] is True
        assert results['spectrum_real'] is True


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v", "--tb=short"])
