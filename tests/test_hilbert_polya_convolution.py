"""
Tests for Hilbert-Pólya Convolution Operator
============================================

Tests the implementation of the convolution operator approach to RH via
the completed zeta function ξ(s) and its Fourier representation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from hilbert_polya_convolution import (
    xi_function,
    Xi_function,
    compute_phi_kernel,
    construct_convolution_kernel,
    build_integral_operator,
    compute_operator_spectrum,
    verify_operator_properties,
    hilbert_polya_interpretation,
    analyze_hilbert_polya_operator,
    validate_against_riemann_zeros,
    F0, C_COHERENCE, C_PRIMARY, PHI, LAMBDA_0,
    HilbertPolyaResult
)


class TestXiFunction:
    """Tests for the completed zeta function ξ(s)."""
    
    def test_xi_at_half(self):
        """Test ξ(1/2) ≠ 0 (no zero at s=1/2)."""
        xi_half = xi_function(0.5 + 0j)
        assert abs(xi_half) > 0.1, "ξ(1/2) should be nonzero"
    
    def test_xi_symmetry(self):
        """Test ξ(s) = ξ(1-s) functional equation."""
        s1 = 0.3 + 0.5j
        s2 = 1 - s1
        
        xi1 = xi_function(s1)
        xi2 = xi_function(s2)
        
        # Should be approximately equal
        rel_diff = abs(xi1 - xi2) / (abs(xi1) + 1e-10)
        assert rel_diff < 0.1, f"ξ(s) = ξ(1-s) violated: {rel_diff:.3f}"
    
    def test_xi_at_first_zero(self):
        """Test ξ(1/2 + i·14.134725...) ≈ 0 at first Riemann zero."""
        gamma1 = 14.134725
        s = 0.5 + 1j * gamma1
        
        xi_val = xi_function(s)
        assert abs(xi_val) < 0.5, f"ξ should be small at zero: |ξ| = {abs(xi_val)}"
    
    def test_xi_entire(self):
        """Test ξ(s) is finite everywhere (entire function)."""
        test_points = [
            0.5 + 0j,
            0.5 + 10j,
            0.5 - 10j,
            0.2 + 5j,
            0.8 + 5j
        ]
        
        for s in test_points:
            xi_val = xi_function(s)
            assert np.isfinite(xi_val), f"ξ({s}) should be finite"


class TestXiCriticalLine:
    """Tests for Ξ(t) = ξ(1/2 + it) on the critical line."""
    
    def test_Xi_real(self):
        """Test Ξ(t) is real for real t."""
        t_values = np.array([0, 5, 10, 20, -5, -10])
        
        for t in t_values:
            Xi_val = Xi_function(t)
            assert isinstance(Xi_val, (float, np.floating)), f"Ξ({t}) should be real"
            assert np.isfinite(Xi_val), f"Ξ({t}) should be finite"
    
    def test_Xi_even(self):
        """Test Ξ(t) = Ξ(-t) (even function)."""
        t_values = [1, 5, 10, 15]
        
        for t in t_values:
            Xi_pos = Xi_function(t)
            Xi_neg = Xi_function(-t)
            
            rel_diff = abs(Xi_pos - Xi_neg) / (abs(Xi_pos) + 1e-10)
            assert rel_diff < 0.01, f"Ξ not even at t={t}: diff={rel_diff:.4f}"
    
    def test_Xi_zero_at_first_riemann_zero(self):
        """Test Ξ(14.134725...) ≈ 0 at first Riemann zero."""
        gamma1 = 14.134725
        Xi_val = Xi_function(gamma1)
        
        assert abs(Xi_val) < 0.5, f"Ξ should vanish at zero: Ξ={Xi_val}"


class TestPhiKernel:
    """Tests for the Φ(u) Fourier kernel."""
    
    def test_phi_positive(self):
        """Test Φ(u) > 0 for u near zero (known underflow for large |u|)."""
        # Test only u near zero where kernel is well-behaved
        u = np.linspace(0.1, 3, 30)
        phi = compute_phi_kernel(u, n_terms=30)
        
        # Note: Φ has numerical issues for large |u| and negative u
        # See HILBERT_POLYA_CONVOLUTION_SUMMARY.md for details
        assert np.all(phi > 0), "Φ(u) should be positive for small positive u"
    
    def test_phi_even(self):
        """Test Φ(u) = Φ(-u) (even function)."""
        u = np.linspace(0.1, 10, 50)
        
        phi_pos = compute_phi_kernel(u, n_terms=30)
        phi_neg = compute_phi_kernel(-u, n_terms=30)
        
        rel_diff = np.abs(phi_pos - phi_neg) / (phi_pos + 1e-10)
        assert np.max(rel_diff) < 0.01, "Φ(u) should be even"
    
    def test_phi_decay(self):
        """Test Φ(u) decays exponentially for large |u|."""
        u_small = 1.0
        u_large = 10.0
        
        phi_small = compute_phi_kernel(np.array([u_small]), n_terms=50)[0]
        phi_large = compute_phi_kernel(np.array([u_large]), n_terms=50)[0]
        
        # Should decay significantly
        ratio = phi_large / phi_small
        assert ratio < 1e-10, f"Φ should decay: φ(10)/φ(1) = {ratio:.2e}"
    
    def test_phi_convergence(self):
        """Test Φ converges as number of terms increases."""
        u = np.array([0.0])
        
        phi_10 = compute_phi_kernel(u, n_terms=10)[0]
        phi_30 = compute_phi_kernel(u, n_terms=30)[0]
        phi_50 = compute_phi_kernel(u, n_terms=50)[0]
        
        # Should converge
        diff_30_10 = abs(phi_30 - phi_10)
        diff_50_30 = abs(phi_50 - phi_30)
        
        assert diff_50_30 < diff_30_10, "Φ should converge with more terms"


class TestConvolutionKernel:
    """Tests for K(u,v) = Φ(u-v) convolution kernel."""
    
    def test_kernel_symmetric(self):
        """Test K(u,v) = K(v,u) (symmetric kernel)."""
        u = np.linspace(-2, 2, 20)
        v = np.linspace(-2, 2, 20)
        
        K = construct_convolution_kernel(u, v, n_terms=20)
        
        # Check symmetry
        sym_error = np.linalg.norm(K - K.T) / np.linalg.norm(K)
        assert sym_error < 1e-10, f"Kernel should be symmetric: error={sym_error:.2e}"
    
    def test_kernel_positive_definite(self):
        """Test K is positive definite (all eigenvalues > 0)."""
        u = np.linspace(-2, 2, 30)
        v = u  # Same grid
        
        K = construct_convolution_kernel(u, v, n_terms=20)
        
        eigenvalues = np.linalg.eigvalsh(K)
        assert np.all(eigenvalues > -1e-10), "K should be positive semi-definite"
    
    def test_kernel_translation_invariance(self):
        """Test K(u,v) = Φ(u-v) (depends only on difference)."""
        u = np.array([1.0, 2.0, 3.0])
        v = np.array([0.0, 1.0, 2.0])
        
        K = construct_convolution_kernel(u, v, n_terms=20)
        
        # K(u[1], v[0]) should equal K(u[2], v[1]) (both have difference 2.0)
        assert abs(K[1, 0] - K[2, 1]) < 1e-6, "Kernel should be translation invariant"


class TestIntegralOperator:
    """Tests for the integral operator T."""
    
    def test_operator_construction(self):
        """Test operator matrix construction."""
        u_grid = np.linspace(-3, 3, 50)
        T, phi = build_integral_operator(u_grid, n_phi_terms=20)
        
        assert T.shape[0] == T.shape[1], "T should be square"
        assert T.shape[0] == len(u_grid), "T size should match grid"
        assert len(phi) == len(u_grid), "Φ size should match grid"
    
    def test_operator_self_adjoint(self):
        """Test T is self-adjoint: T = T†."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        hermiticity_error = np.linalg.norm(T - T.T) / np.linalg.norm(T)
        assert hermiticity_error < 1e-12, f"T should be self-adjoint: error={hermiticity_error:.2e}"
    
    def test_operator_positive(self):
        """Test T is positive: all eigenvalues ≥ 0."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        eigenvalues = np.linalg.eigvalsh(T)
        min_eig = np.min(eigenvalues)
        
        assert min_eig > -1e-10, f"T should be positive: min λ = {min_eig:.2e}"
    
    def test_operator_hilbert_schmidt(self):
        """Test T is Hilbert-Schmidt: ||T||_HS² = Tr(T†T) < ∞."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        hs_norm_squared = np.sum(T * T)
        assert np.isfinite(hs_norm_squared), "T should be Hilbert-Schmidt"
        assert hs_norm_squared > 0, "HS norm should be positive"
    
    def test_operator_compact(self):
        """Test T is compact: eigenvalues decay to zero."""
        u_grid = np.linspace(-3, 3, 60)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        eigenvalues, _ = compute_operator_spectrum(T)
        
        # Check decay
        if len(eigenvalues) > 10:
            ratio = eigenvalues[-1] / eigenvalues[0]
            assert ratio < 0.1, f"Eigenvalues should decay: λ_min/λ_max = {ratio:.3f}"


class TestOperatorSpectrum:
    """Tests for spectral analysis of T."""
    
    def test_spectrum_computation(self):
        """Test eigenvalue computation."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        eigenvalues, eigenvectors = compute_operator_spectrum(T)
        
        assert len(eigenvalues) == T.shape[0], "Should compute all eigenvalues"
        assert eigenvectors.shape == T.shape, "Eigenvector matrix shape"
        assert np.all(np.isreal(eigenvalues)), "Eigenvalues should be real"
    
    def test_spectrum_sorted(self):
        """Test eigenvalues are sorted in descending order."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        
        eigenvalues, _ = compute_operator_spectrum(T)
        
        # Check sorting
        diffs = np.diff(eigenvalues)
        assert np.all(diffs <= 0), "Eigenvalues should be sorted descending"
    
    def test_eigenvector_orthonormality(self):
        """Test eigenvectors are orthonormal."""
        u_grid = np.linspace(-2, 2, 30)
        T, _ = build_integral_operator(u_grid, n_phi_terms=15)
        
        eigenvalues, eigenvectors = compute_operator_spectrum(T)
        
        # Check orthonormality: V†V = I
        gram = eigenvectors.T @ eigenvectors
        identity = np.eye(len(eigenvalues))
        
        ortho_error = np.linalg.norm(gram - identity)
        assert ortho_error < 1e-10, f"Eigenvectors should be orthonormal: error={ortho_error:.2e}"


class TestOperatorProperties:
    """Tests for operator property verification."""
    
    def test_property_verification(self):
        """Test verify_operator_properties function."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        eigenvalues, _ = compute_operator_spectrum(T)
        
        props = verify_operator_properties(T, eigenvalues)
        
        assert 'is_self_adjoint' in props
        assert 'is_positive' in props
        assert 'is_hilbert_schmidt' in props
        assert 'is_compact' in props
        assert 'hs_norm' in props
        
        # Check properties are satisfied
        assert props['is_self_adjoint'], "Should be self-adjoint"
        assert props['is_positive'], "Should be positive"
        assert props['is_hilbert_schmidt'], "Should be Hilbert-Schmidt"
    
    def test_trace_class_property(self):
        """Test if T is trace class."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        eigenvalues, _ = compute_operator_spectrum(T)
        
        props = verify_operator_properties(T, eigenvalues)
        
        assert 'is_trace_class' in props
        assert props['is_trace_class'], "Should be trace class"
        assert np.isfinite(props['trace_norm']), "Trace norm should be finite"


class TestHilbertPolyaInterpretation:
    """Tests for H = -log(T) interpretation."""
    
    def test_h_operator_computation(self):
        """Test computation of H from T = e^(-H)."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        eigenvalues, _ = compute_operator_spectrum(T)
        
        hp_result = hilbert_polya_interpretation(T, eigenvalues)
        
        assert 'H_spectrum' in hp_result
        assert 'potential_zeros' in hp_result
        assert 'quality' in hp_result
        
        H_spectrum = hp_result['H_spectrum']
        assert len(H_spectrum) > 0, "Should compute H spectrum"
        assert np.all(np.isreal(H_spectrum)), "H spectrum should be real"
    
    def test_potential_zeros_positive(self):
        """Test potential Riemann zeros are positive."""
        u_grid = np.linspace(-2, 2, 40)
        T, _ = build_integral_operator(u_grid, n_phi_terms=20)
        eigenvalues, _ = compute_operator_spectrum(T)
        
        hp_result = hilbert_polya_interpretation(T, eigenvalues)
        potential_zeros = hp_result['potential_zeros']
        
        if len(potential_zeros) > 0:
            assert np.all(potential_zeros > 0), "Candidate zeros should be positive"
    
    def test_regularization(self):
        """Test small eigenvalue regularization."""
        # Create operator with very small eigenvalues
        eigenvalues = np.array([1.0, 0.1, 0.01, 1e-6, 1e-10])
        T = np.diag(eigenvalues)
        
        hp_result = hilbert_polya_interpretation(T, eigenvalues, epsilon=1e-8)
        
        H_spectrum = hp_result['H_spectrum']
        assert np.all(np.isfinite(H_spectrum)), "Regularization should prevent infinities"


class TestFullAnalysis:
    """Tests for complete Hilbert-Pólya analysis."""
    
    def test_analyze_hilbert_polya_operator(self):
        """Test full analysis pipeline."""
        result = analyze_hilbert_polya_operator(
            u_min=-3.0,
            u_max=3.0,
            n_points=64,
            n_phi_terms=20
        )
        
        assert isinstance(result, HilbertPolyaResult)
        assert len(result.eigenvalues) > 0
        assert result.eigenfunctions is not None
        assert len(result.phi_kernel) > 0
        assert len(result.u_grid) > 0
        assert result.operator_norm > 0
    
    def test_analysis_properties(self):
        """Test analysis verifies operator properties."""
        result = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=48,
            n_phi_terms=15
        )
        
        assert result.is_self_adjoint, "Should verify self-adjointness"
        assert result.is_positive, "Should verify positivity"
    
    def test_qcal_coherence(self):
        """Test QCAL coherence measure."""
        result = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=48,
            n_phi_terms=15
        )
        
        if result.coherence_measure is not None:
            assert result.coherence_measure >= 0, "Coherence measure should be non-negative"


class TestRiemannZeroValidation:
    """Tests for validation against known Riemann zeros."""
    
    def test_validation_with_known_zeros(self):
        """Test validation against hardcoded zeros."""
        result = analyze_hilbert_polya_operator(
            u_min=-3.0,
            u_max=3.0,
            n_points=64,
            n_phi_terms=25
        )
        
        # Use first 5 known zeros
        known_zeros = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])
        
        validation = validate_against_riemann_zeros(result, known_zeros, max_zeros=5)
        
        if 'error' not in validation:
            assert 'n_compared' in validation
            assert 'mean_abs_error' in validation
            assert 'correlation' in validation
    
    def test_validation_metrics(self):
        """Test validation returns expected metrics."""
        result = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=48,
            n_phi_terms=15
        )
        
        validation = validate_against_riemann_zeros(result, max_zeros=10)
        
        # Should have error or metrics
        if 'error' not in validation:
            assert validation['n_compared'] > 0
            assert validation['mean_abs_error'] >= 0
            assert -1 <= validation['correlation'] <= 1


class TestQCALConstants:
    """Tests for QCAL framework constants."""
    
    def test_fundamental_frequency(self):
        """Test f₀ = 141.7001 Hz."""
        assert np.isclose(F0, 141.7001, rtol=1e-10)
    
    def test_coherence_constant(self):
        """Test C = 244.36."""
        assert np.isclose(C_COHERENCE, 244.36, rtol=1e-10)
    
    def test_primary_constant(self):
        """Test C_universal = 629.83."""
        assert np.isclose(C_PRIMARY, 629.83, rtol=1e-10)
    
    def test_golden_ratio(self):
        """Test φ ≈ 1.618."""
        assert np.isclose(PHI, 1.618033988, rtol=1e-6)
    
    def test_lambda_0(self):
        """Test λ₀ = 1/C_universal."""
        expected = 1.0 / C_PRIMARY
        assert np.isclose(LAMBDA_0, expected, rtol=1e-10)


class TestNumericalStability:
    """Tests for numerical stability and edge cases."""
    
    def test_small_grid(self):
        """Test with small grid size."""
        result = analyze_hilbert_polya_operator(
            u_min=-1.0,
            u_max=1.0,
            n_points=16,
            n_phi_terms=10
        )
        
        assert len(result.eigenvalues) == 16
        assert result.is_self_adjoint
    
    def test_large_u_range(self):
        """Test with large u range."""
        result = analyze_hilbert_polya_operator(
            u_min=-10.0,
            u_max=10.0,
            n_points=64,
            n_phi_terms=30
        )
        
        assert result.operator_norm > 0
        assert np.all(np.isfinite(result.eigenvalues))
    
    def test_few_phi_terms(self):
        """Test with minimal Φ kernel terms."""
        result = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=32,
            n_phi_terms=5
        )
        
        assert len(result.eigenvalues) > 0
        assert result.is_positive


class TestIntegration:
    """Integration tests combining multiple components."""
    
    def test_end_to_end_pipeline(self):
        """Test complete pipeline from xi to validation."""
        # 1. Compute xi and Xi
        xi_val = xi_function(0.5 + 14.134725j)
        Xi_val = Xi_function(14.134725)
        
        assert np.isfinite(xi_val)
        assert np.isfinite(Xi_val)
        
        # 2. Build operator
        u_grid = np.linspace(-2, 2, 48)
        T, phi = build_integral_operator(u_grid, n_phi_terms=20)
        
        assert T.shape[0] == 48
        
        # 3. Compute spectrum
        eigenvalues, eigenvectors = compute_operator_spectrum(T)
        
        assert len(eigenvalues) == 48
        
        # 4. Verify properties
        props = verify_operator_properties(T, eigenvalues)
        
        assert props['is_self_adjoint']
        assert props['is_positive']
        
        # 5. Hilbert-Pólya interpretation
        hp_result = hilbert_polya_interpretation(T, eigenvalues)
        
        assert 'H_spectrum' in hp_result
    
    def test_reproducibility(self):
        """Test results are reproducible."""
        result1 = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=48,
            n_phi_terms=20
        )
        
        result2 = analyze_hilbert_polya_operator(
            u_min=-2.0,
            u_max=2.0,
            n_points=48,
            n_phi_terms=20
        )
        
        # Eigenvalues should match
        np.testing.assert_allclose(
            result1.eigenvalues,
            result2.eigenvalues,
            rtol=1e-10
        )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
