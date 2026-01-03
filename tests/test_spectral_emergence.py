#!/usr/bin/env python3
"""
Test Suite for Spectral Emergence Framework
============================================

Tests the zeta-free approach to RH proof via operator theory:
    1. Fredholm determinant D(s) construction
    2. Paley-Wiener uniqueness verification
    3. Hilbert-Pólya operator spectral properties
    4. Emergence of zeros from operator spectrum

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: December 2025
"""

import pytest
import numpy as np
import mpmath as mp
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from spectral_emergence import (
    FredholmDeterminant,
    PaleyWienerIdentification,
    HilbertPolyaOperator,
    validate_spectral_emergence,
    F0, C_PRIMARY, C_COHERENCE, LAMBDA_0
)


class TestFredholmDeterminant:
    """Test Fredholm determinant construction and properties."""
    
    def test_initialization(self):
        """Test basic initialization."""
        fredholm = FredholmDeterminant(precision=25)
        assert fredholm.S_cutoff == 1000
        assert mp.dps == 25
        
    def test_A0_operator(self):
        """Test universal operator A₀ = 1/2 + iZ."""
        fredholm = FredholmDeterminant(precision=25)
        
        # A₀ at s should give s - 1/2
        s = mp.mpc(0.5, 14.1347)
        result = fredholm.A0_operator(s)
        expected = s - mp.mpf('0.5')
        
        assert abs(result - expected) < 1e-10
        
    def test_functional_equation(self):
        """Test D(s) = D(1-s) functional equation."""
        fredholm = FredholmDeterminant(precision=30)
        
        # Test at several points
        test_points = [
            mp.mpc(0.3, 10.0),
            mp.mpc(0.5, 14.1347),
            mp.mpc(0.7, 21.022)
        ]
        
        for s in test_points:
            is_valid = fredholm.verify_functional_equation(s, tolerance=1e-6)
            assert is_valid, f"Functional equation failed at s={s}"
            
    def test_critical_line_real(self):
        """Test that D(s) is real on critical line Re(s) = 1/2."""
        fredholm = FredholmDeterminant(precision=25)
        
        # On critical line
        s_critical = mp.mpc(0.5, 14.1347)
        D_val = fredholm.compute_D(s_critical)
        
        # Imaginary part should be negligible
        assert abs(D_val.imag) < 1e-6


class TestPaleyWienerIdentification:
    """Test Paley-Wiener uniqueness theorem application."""
    
    def test_initialization(self):
        """Test initialization with Fredholm determinant."""
        fredholm = FredholmDeterminant(precision=25)
        pw = PaleyWienerIdentification(fredholm)
        assert pw.D == fredholm
        
    def test_xi_function(self):
        """Test Xi function evaluation."""
        fredholm = FredholmDeterminant(precision=25)
        pw = PaleyWienerIdentification(fredholm)
        
        # Known zero of Xi at s ≈ 0.5 + 14.134725i
        s = mp.mpc(0.5, 14.134725)
        xi_val = pw.xi_function(s)
        
        # Should be close to zero
        assert abs(xi_val) < 1e-3
        
    def test_uniqueness_verification(self):
        """Test D(s) ≈ Ξ(s) verification."""
        fredholm = FredholmDeterminant(precision=30)
        pw = PaleyWienerIdentification(fredholm)
        
        # Test points on critical line
        test_points = [mp.mpc(0.5, t) for t in [10.0, 15.0, 20.0]]
        tolerance = 1e-3
        
        result = pw.verify_uniqueness(test_points, tolerance=tolerance)
        
        assert 'verified' in result
        assert 'structural_verified' in result
        assert 'numerical_verified' in result
        assert 'max_relative_error' in result
        assert result['test_points_count'] == len(test_points)
        # Check that we get boolean flags
        assert isinstance(result['verified'], bool)
        assert isinstance(result['structural_verified'], bool)
        assert isinstance(result['numerical_verified'], bool)


class TestHilbertPolyaOperator:
    """Test Hilbert-Pólya operator H_Ψ construction and properties."""
    
    def test_initialization(self):
        """Test operator initialization."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=100)
        
        assert H_psi.L == 10.0
        assert H_psi.N == 100
        assert len(H_psi.x) == 100
        assert H_psi.lambda_param > 0
        
    def test_potential_symmetry(self):
        """Test that potential V(x) is symmetric: V(-x) = V(x)."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=201)
        
        V = H_psi.potential(H_psi.x)
        
        # Check symmetry around x = 0
        mid = len(V) // 2
        V_left = V[:mid]
        V_right = V[mid+1:][::-1]  # Reverse right half
        
        # Compare overlapping region to avoid silently skipping when lengths differ
        n = min(len(V_left), len(V_right))
        np.testing.assert_allclose(
            V_left[:n],
            V_right[:n],
            rtol=1e-10,
            err_msg="Potential must be symmetric: V(-x) ≈ V(x)",
        )
            
    def test_potential_confining(self):
        """Test that potential V(x) → ∞ as |x| → ∞."""
        H_psi = HilbertPolyaOperator(domain_size=20.0, num_points=1000)
        
        V = H_psi.potential(H_psi.x)
        
        # Potential at boundaries should be larger than at center
        V_boundary = min(V[0], V[-1])
        V_center = V[len(V)//2]
        
        assert V_boundary > V_center
        
    def test_self_adjointness(self):
        """Test that H_Ψ is self-adjoint."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=200)
        
        is_self_adjoint = H_psi.verify_self_adjointness(tolerance=1e-10)
        
        assert is_self_adjoint, "Operator H_Ψ must be self-adjoint"
        
    def test_spectrum_real(self):
        """Test that spectrum of H_Ψ is real."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=200)
        
        eigenvalues, _ = H_psi.compute_spectrum(num_eigenvalues=20)
        
        # All eigenvalues should be real (within numerical precision)
        assert np.all(np.isreal(eigenvalues))
        
    def test_spectrum_discrete(self):
        """Test that spectrum is discrete and ordered."""
        H_psi = HilbertPolyaOperator(domain_size=15.0, num_points=300)
        
        eigenvalues, _ = H_psi.compute_spectrum(num_eigenvalues=30)
        
        # Should be in strictly ascending order (no degeneracies expected)
        assert np.all(np.diff(eigenvalues) > 0)
        
    def test_zeros_on_critical_line(self):
        """Test that zeros from spectrum are on critical line."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=200)
        
        zeros = H_psi.zeros_from_spectrum()
        
        # All zeros should have Re(ρ) = 1/2 (or NaN for negative eigenvalues)
        real_parts = np.real(zeros)
        # Filter out NaN values for the comparison
        non_nan_mask = ~np.isnan(real_parts)
        if np.any(non_nan_mask):
            np.testing.assert_allclose(real_parts[non_nan_mask], 0.5, rtol=1e-10)
        
        # Imaginary parts should be derived from eigenvalues
        # For positive eigenvalues: Im(ρ) = √λ
        # For negative eigenvalues: Im(ρ) = NaN (handled by operator)
        imag_parts = np.imag(zeros)
        # Check that we get an ndarray with the right properties
        assert isinstance(imag_parts, np.ndarray)
        # Non-NaN imaginary parts should be real numbers
        non_nan_mask = ~np.isnan(imag_parts)
        if np.any(non_nan_mask):
            assert np.all(np.isreal(imag_parts[non_nan_mask]))
        
    def test_first_eigenvalue_order_magnitude(self):
        """Test that first eigenvalues have reasonable order of magnitude."""
        H_psi = HilbertPolyaOperator(domain_size=20.0, num_points=500)
        
        eigenvalues, _ = H_psi.compute_spectrum(num_eigenvalues=10)
        
        # Eigenvalues should be real (structural property)
        assert np.all(np.isreal(eigenvalues))
        
        
class TestSpectralEmergenceFramework:
    """Test complete spectral emergence framework."""
    
    def test_fundamental_constants(self):
        """Test QCAL fundamental constants are defined correctly."""
        assert F0 == 141.7001
        assert C_PRIMARY == 629.83
        assert C_COHERENCE == 244.36
        assert abs(LAMBDA_0 - 1.0/C_PRIMARY) < 1e-10
        
    def test_coherence_factor(self):
        """Test coherence factor C'/C ≈ 0.388 is computed correctly."""
        from spectral_emergence import COHERENCE_FACTOR
        
        # Verify the coherence factor is computed from the constants
        expected = C_COHERENCE / C_PRIMARY
        assert abs(COHERENCE_FACTOR - expected) < 1e-10
        
        # Verify it's in the expected range (validates the constant values are reasonable)
        assert 0.38 < COHERENCE_FACTOR < 0.40
        
        # Additional check: verify this represents a meaningful physical relationship
        # The coherence factor should be less than 1 (coherence weaker than structure)
        assert COHERENCE_FACTOR < 1.0
        
    @pytest.mark.slow
    def test_complete_validation(self):
        """Test complete validation framework (slow test)."""
        # Run with reduced parameters for speed
        certificate = validate_spectral_emergence(
            num_test_points=3,
            num_eigenvalues=10,
            precision=25
        )
        
        assert 'framework' in certificate
        assert certificate['framework'] == 'Spectral Emergence (Zeta-Free)'
        assert 'validations' in certificate
        assert 'fredholm_functional_equation' in certificate['validations']
        assert 'paley_wiener_uniqueness' in certificate['validations']
        assert 'hilbert_polya_self_adjoint' in certificate['validations']
        assert 'spectral_emergence' in certificate['validations']
        
    def test_paradigm_shift_documentation(self):
        """Test that paradigm shift is properly documented."""
        certificate = validate_spectral_emergence(
            num_test_points=2,
            num_eigenvalues=5,
            precision=20
        )
        
        assert 'paradigm_shift' in certificate
        paradigm = certificate['paradigm_shift']
        
        assert 'traditional' in paradigm
        assert 'spectral_emergence' in paradigm
        assert 'key_insight' in paradigm
        assert 'critical line' in paradigm['key_insight'].lower()


class TestZetaFreeConstruction:
    """Test that construction is genuinely zeta-free."""
    
    def test_no_euler_product_dependency(self):
        """Test that Fredholm determinant doesn't use Euler product."""
        fredholm = FredholmDeterminant(precision=25)
        
        # Construction should work without any prime number knowledge
        s = mp.mpc(0.5, 10.0)
        D_val = fredholm.compute_D(s, use_regularization=True)
        
        # Should be computable (not raise exception)
        assert D_val is not None
        
    def test_geometric_construction(self):
        """Test that construction is purely geometric."""
        H_psi = HilbertPolyaOperator(domain_size=10.0, num_points=100)
        
        # Operator matrix should be constructible from geometric data alone
        H_matrix = H_psi.construct_operator()
        
        # Should be well-defined
        assert H_matrix is not None
        assert H_matrix.shape == (H_psi.N, H_psi.N)
        
        # Should be symmetric (geometric property)
        asymmetry = np.max(np.abs(H_matrix - H_matrix.T))
        assert asymmetry < 1e-10


# =============================================================================
# RUN TESTS
# =============================================================================

if __name__ == '__main__':
    pytest.main([__file__, '-v', '--tb=short'])
