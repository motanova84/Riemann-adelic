#!/usr/bin/env python3
"""
Tests for Hermetic Trace Operator T_∞³ and Noetic Spectral Identity

This module tests the implementation of the Hermetic Trace Formula ∞³:
    1. Dirac spectral operator D_s construction
    2. Hermetic Noetic operator T_∞³ = √(1 + D_s²)
    3. Spectral identity: ζ(s) = Tr(T_∞³^(-s))
    4. Hermetic trace formula (Gutzwiller-type)

Mathematical Framework (PHASE VI):
    D_s ψ_n = γ_n ψ_n where ζ(1/2 + iγ_n) = 0
    T_∞³ = √(1 + D_s²) with eigenvalues λ_n = √(1 + γ_n²)
    ζ(s) = Σ_n (1 + γ_n²)^(-s/2) = Tr(T_∞³^(-s))

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.hermetic_trace_operator import (
    # Functions
    build_dirac_spectral_operator,
    build_hermetic_noetic_operator,
    compute_trace_zeta_regularized,
    compute_hermetic_trace_formula,
    verify_spectral_identity,
    demonstrate_hermetic_trace_identity,
    # Constants
    F0_QCAL,
    C_PRIMARY,
    C_COHERENCE,
)


# Known Riemann zeros for testing
RIEMANN_ZEROS_TEST = np.array([
    14.134725,
    21.022040,
    25.010858,
    30.424876,
    32.935062
])


class TestDiracSpectralOperator:
    """Test the Dirac spectral operator D_s construction."""
    
    def test_dirac_operator_shape(self):
        """D_s should have correct shape."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        assert D_s.shape == (3, 3)
    
    def test_dirac_operator_diagonal(self):
        """D_s should be diagonal with zeros as eigenvalues."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        
        # Should be diagonal
        off_diagonal = D_s - np.diag(np.diag(D_s))
        assert np.allclose(off_diagonal, 0)
        
        # Diagonal elements should be Riemann zeros
        diag_elements = np.diag(D_s)
        assert np.allclose(diag_elements, gamma)
    
    def test_dirac_operator_eigenvalues(self):
        """D_s eigenvalues should match Riemann zeros."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        
        eigenvalues = np.linalg.eigvalsh(D_s)
        eigenvalues_sorted = np.sort(eigenvalues)
        gamma_sorted = np.sort(gamma)
        
        assert np.allclose(eigenvalues_sorted, gamma_sorted, rtol=1e-10)
    
    def test_dirac_operator_self_adjoint(self):
        """D_s should be self-adjoint (Hermitian)."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        
        # Check D_s = D_s^T (real symmetric)
        assert np.allclose(D_s, D_s.T)


class TestHermeticNoeticOperator:
    """Test the Hermetic Noetic operator T_∞³."""
    
    def test_hermetic_operator_shape(self):
        """T_∞³ should have same shape as D_s."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        assert T_inf3.shape == D_s.shape
    
    def test_hermetic_operator_eigenvalues(self):
        """T_∞³ eigenvalues should be λ_n = √(1 + γ_n²)."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # Expected eigenvalues
        expected_lambda = np.sqrt(1 + gamma**2)
        
        # Computed eigenvalues
        eigenvalues = np.linalg.eigvalsh(T_inf3)
        eigenvalues_sorted = np.sort(eigenvalues)
        expected_sorted = np.sort(expected_lambda)
        
        assert np.allclose(eigenvalues_sorted, expected_sorted, rtol=1e-8)
    
    def test_hermetic_operator_positive_eigenvalues(self):
        """All eigenvalues of T_∞³ should be positive."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        eigenvalues = np.linalg.eigvalsh(T_inf3)
        assert np.all(eigenvalues > 0)
    
    def test_hermetic_operator_self_adjoint(self):
        """T_∞³ should be self-adjoint."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # Check T_∞³ = T_∞³^T
        assert np.allclose(T_inf3, T_inf3.T, rtol=1e-10)
    
    def test_hermetic_operator_definition(self):
        """Verify T_∞³² = 1 + D_s² mathematically."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # Compute T_∞³²
        T_squared = T_inf3 @ T_inf3
        
        # Compute 1 + D_s²
        I = np.eye(D_s.shape[0])
        expected = I + D_s @ D_s
        
        assert np.allclose(T_squared, expected, rtol=1e-8)


class TestTraceZetaRegularized:
    """Test the regularized trace computation."""
    
    def test_trace_zeta_at_s2(self):
        """Test Tr(T_∞³^(-s)) at s=2."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        s = 2.0 + 0.0j
        trace = compute_trace_zeta_regularized(T_inf3, s)
        
        # Should match partial sum: Σ (1 + γ_n²)^(-1)
        expected = np.sum((1 + gamma**2) ** (-1))
        
        assert np.abs(trace - expected) / np.abs(expected) < 1e-6
    
    def test_trace_zeta_methods_agree(self):
        """Both methods should give same result."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        s = 2.0 + 0.0j
        trace_eig = compute_trace_zeta_regularized(T_inf3, s, method='eigenvalue')
        trace_pow = compute_trace_zeta_regularized(T_inf3, s, method='power')
        
        assert np.abs(trace_eig - trace_pow) < 1e-8
    
    def test_trace_zeta_positive(self):
        """Trace should be positive for real s > 0."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        for s_val in [1.5, 2.0, 3.0]:
            trace = compute_trace_zeta_regularized(T_inf3, s_val)
            assert trace.real > 0


class TestHermeticTraceFormula:
    """Test the Hermetic Trace Formula (Gutzwiller-type)."""
    
    def test_trace_formula_shape(self):
        """Trace formula should return correct number of components."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        t = 0.1
        trace, oscillatory = compute_hermetic_trace_formula(T_inf3, t, n_terms=5)
        
        assert isinstance(trace, float)
        assert len(oscillatory) == 5
    
    def test_trace_formula_positive(self):
        """Trace of heat kernel should be positive."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        for t in [0.01, 0.1, 1.0]:
            trace, _ = compute_hermetic_trace_formula(T_inf3, t)
            assert trace > 0
    
    def test_trace_formula_decay(self):
        """Trace should decay with increasing t."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        t_values = [0.01, 0.1, 0.5, 1.0]
        traces = []
        
        for t in t_values:
            trace, _ = compute_hermetic_trace_formula(T_inf3, t)
            traces.append(trace)
        
        # Trace should decrease with t (heat kernel decay)
        for i in range(len(traces) - 1):
            assert traces[i] > traces[i+1]
    
    def test_trace_formula_matches_exact(self):
        """Trace formula should match exact computation."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        t = 0.1
        trace_formula, _ = compute_hermetic_trace_formula(T_inf3, t)
        
        # Exact: Tr(e^(-t·T_∞³)) = Σ e^(-t·λ_n)
        eigenvalues = np.linalg.eigvalsh(T_inf3)
        trace_exact = np.sum(np.exp(-t * eigenvalues))
        
        assert np.abs(trace_formula - trace_exact) < 1e-10


class TestSpectralIdentityVerification:
    """Test the verification of the Noetic Spectral Identity."""
    
    def test_verify_at_s2(self):
        """Verify identity at s=2."""
        gamma = RIEMANN_ZEROS_TEST[:10]
        result = verify_spectral_identity(gamma, s=2.0)
        
        assert 'verified' in result
        assert 'trace_spectral' in result
        assert 'zeta_partial_sum' in result
        
        # Should verify successfully
        assert result['verified'] == True
    
    def test_verify_trace_matches_partial(self):
        """Trace should match partial sum exactly."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        result = verify_spectral_identity(gamma, s=2.0)
        
        # Error between trace and partial sum should be tiny
        assert result['error_trace_vs_partial'] < 1e-6
    
    def test_verify_multiple_s_values(self):
        """Test verification at multiple s values."""
        gamma = RIEMANN_ZEROS_TEST[:8]
        
        s_values = [1.5, 2.0, 3.0, 2.0 + 1.0j]
        for s in s_values:
            result = verify_spectral_identity(gamma, s=s)
            
            # Should always verify for trace vs partial sum
            assert result['verified'] == True
    
    def test_verify_result_structure(self):
        """Result should have expected structure."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        result = verify_spectral_identity(gamma, s=2.0)
        
        expected_keys = [
            's', 'n_zeros', 'zeta_standard', 'trace_spectral',
            'zeta_partial_sum', 'error_trace_vs_partial',
            'verified', 'interpretation', 'note'
        ]
        
        for key in expected_keys:
            assert key in result


class TestDemonstration:
    """Test the full demonstration function."""
    
    def test_demonstrate_runs(self):
        """Demonstration should run without errors."""
        result = demonstrate_hermetic_trace_identity(n_zeros=10, verbose=False)
        
        assert result is not None
        assert 'n_zeros' in result
        assert 'riemann_zeros' in result
    
    def test_demonstrate_structure(self):
        """Result should have complete structure."""
        result = demonstrate_hermetic_trace_identity(n_zeros=5, verbose=False)
        
        expected_keys = [
            'n_zeros', 'riemann_zeros', 'D_s_eigenvalues',
            'T_inf3_eigenvalues', 'spectral_identity_verification',
            'trace_heat_kernel', 'framework'
        ]
        
        for key in expected_keys:
            assert key in result
    
    def test_demonstrate_verification_passes(self):
        """Spectral identity verification should pass."""
        result = demonstrate_hermetic_trace_identity(n_zeros=10, verbose=False)
        
        verification = result['spectral_identity_verification']
        assert verification['verified'] == True
    
    def test_demonstrate_framework_info(self):
        """Framework info should be complete."""
        result = demonstrate_hermetic_trace_identity(n_zeros=5, verbose=False)
        
        framework = result['framework']
        assert 'operator_Ds' in framework
        assert 'operator_Tinf3' in framework
        assert 'identity' in framework
        assert 'trace_formula' in framework
        assert 'ankh_symbol' in framework
        assert 'phase' in framework


class TestConstants:
    """Test QCAL constants."""
    
    def test_f0_qcal_value(self):
        """QCAL fundamental frequency should be correct."""
        assert abs(F0_QCAL - 141.7001) < 1e-4
    
    def test_c_primary_value(self):
        """Primary spectral constant should be correct."""
        assert abs(C_PRIMARY - 629.83) < 0.01
    
    def test_c_coherence_value(self):
        """Coherence constant should be correct."""
        assert abs(C_COHERENCE - 244.36) < 0.01


class TestMathematicalConsistency:
    """Test mathematical consistency of the framework."""
    
    def test_operator_relationship(self):
        """Verify T_∞³² = 1 + D_s² holds exactly."""
        gamma = RIEMANN_ZEROS_TEST[:4]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # LHS: T_∞³²
        lhs = T_inf3 @ T_inf3
        
        # RHS: 1 + D_s²
        I = np.eye(D_s.shape[0])
        rhs = I + D_s @ D_s
        
        # Should be equal
        assert np.allclose(lhs, rhs, rtol=1e-8, atol=1e-10)
    
    def test_eigenvalue_relationship(self):
        """Verify λ_n = √(1 + γ_n²) for all eigenvalues."""
        gamma = RIEMANN_ZEROS_TEST
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # Get eigenvalues
        lambda_n = np.linalg.eigvalsh(T_inf3)
        
        # Expected from formula
        expected = np.sqrt(1 + gamma**2)
        
        # Sort both
        lambda_sorted = np.sort(lambda_n)
        expected_sorted = np.sort(expected)
        
        assert np.allclose(lambda_sorted, expected_sorted, rtol=1e-8)
    
    def test_trace_identity_consistency(self):
        """Verify trace identity is consistent across methods."""
        gamma = RIEMANN_ZEROS_TEST[:6]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        s = 2.5 + 0.5j
        
        # Method 1: Via eigenvalues
        trace1 = compute_trace_zeta_regularized(T_inf3, s, method='eigenvalue')
        
        # Method 2: Via matrix power
        trace2 = compute_trace_zeta_regularized(T_inf3, s, method='power')
        
        # Method 3: Direct from formula
        lambda_n = np.sqrt(1 + gamma**2)
        trace3 = np.sum(lambda_n ** (-s))
        
        # All should agree
        assert np.abs(trace1 - trace2) < 1e-8
        assert np.abs(trace1 - trace3) < 1e-8


class TestNumericalStability:
    """Test numerical stability of implementations."""
    
    def test_stability_large_zeros(self):
        """Should handle larger Riemann zeros stably."""
        gamma = np.array([14.134725, 21.022040, 25.010858, 
                         30.424876, 77.144840])  # Including larger zero
        
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        # Should complete without errors
        assert T_inf3 is not None
        
        # Eigenvalues should be reasonable
        eigenvalues = np.linalg.eigvalsh(T_inf3)
        assert np.all(np.isfinite(eigenvalues))
        assert np.all(eigenvalues > 0)
    
    def test_stability_small_t(self):
        """Heat kernel should be stable for small t."""
        gamma = RIEMANN_ZEROS_TEST[:3]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        t_small = 0.001
        trace, _ = compute_hermetic_trace_formula(T_inf3, t_small)
        
        assert np.isfinite(trace)
        assert trace > 0
    
    def test_stability_complex_s(self):
        """Should handle complex s stably."""
        gamma = RIEMANN_ZEROS_TEST[:5]
        D_s = build_dirac_spectral_operator(gamma)
        T_inf3 = build_hermetic_noetic_operator(D_s)
        
        s_complex = 2.0 + 5.0j
        trace = compute_trace_zeta_regularized(T_inf3, s_complex)
        
        assert np.isfinite(trace)


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
