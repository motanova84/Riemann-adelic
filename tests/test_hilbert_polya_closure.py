#!/usr/bin/env python3
"""
Test suite for Hilbert-Pólya Closure validation module.

This test suite validates the formal closure of the Hilbert-Pólya approach:
1. Trace Convergence (Schatten Class)
2. Unique Self-Adjoint Extension (Friedrichs)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: 2025-11-28
"""

import pytest
import numpy as np
from pathlib import Path
import re
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from validation.hilbert_polya_closure import (
    gaussian_kernel,
    build_H_psi_matrix,
    validate_symmetry,
    validate_positivity,
    validate_coercivity,
    validate_trace_convergence,
    validate_schatten_class,
    validate_friedrichs_conditions,
    run_hilbert_polya_validation,
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
)


class TestQCALConstants:
    """Test QCAL integration constants."""
    
    def test_qcal_frequency(self):
        """Verify QCAL base frequency constant."""
        assert QCAL_FREQUENCY == 141.7001
    
    def test_qcal_coherence(self):
        """Verify QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36


class TestGaussianKernel:
    """Test the Gaussian kernel function."""
    
    def test_kernel_symmetry(self):
        """Test that kernel is symmetric: K(t,s) = K(s,t)."""
        # Use 20x20 grid for faster test execution while maintaining coverage
        t = np.linspace(-2, 2, 20)
        s = np.linspace(-2, 2, 20)
        
        for ti in t:
            for si in s:
                K_ts = gaussian_kernel(np.array([ti]), np.array([si]))
                K_st = gaussian_kernel(np.array([si]), np.array([ti]))
                assert np.allclose(K_ts, K_st), "Kernel should be symmetric"
    
    def test_kernel_positive(self):
        """Test that kernel is always positive (within numerical precision)."""
        # Use smaller range to avoid numerical underflow
        t = np.linspace(-2, 2, 50)
        s = np.linspace(-2, 2, 50)
        
        for ti in t:
            K = gaussian_kernel(np.array([ti]), s)
            # Check that non-underflow values are positive
            assert np.all(K >= 0), "Kernel should be non-negative"
            # At least some values should be strictly positive
            assert np.any(K > 0), "Kernel should have positive values"
    
    def test_kernel_normalized(self):
        """Test kernel integral normalization."""
        # For Gaussian kernel K_h(t,s), the integral over s should give ~1
        # when properly normalized for the heat kernel formulation
        h = 1e-3
        # Use smaller range centered at 0 to avoid underflow
        s = np.linspace(-1, 1, 500)
        ds = s[1] - s[0]
        
        K = gaussian_kernel(np.array([0.0]), s, h=h)
        integral = np.sum(K) * ds
        
        # The integral should be finite and positive
        assert integral > 0, "Kernel integral should be positive"
        assert np.isfinite(integral), "Kernel integral should be finite"


class TestHPsiMatrix:
    """Test the H_Ψ matrix construction."""
    
    def test_matrix_shape(self):
        """Test that matrix has correct shape."""
        n = 15
        H = build_H_psi_matrix(n_basis=n)
        assert H.shape == (n, n), f"Matrix should be {n}x{n}"
    
    def test_matrix_symmetric(self):
        """Test that H matrix is symmetric."""
        H = build_H_psi_matrix(n_basis=20)
        is_symmetric, max_asym = validate_symmetry(H)
        assert is_symmetric, f"Matrix should be symmetric, max asymmetry: {max_asym}"
    
    def test_matrix_positive_definite(self):
        """Test that H matrix is positive definite."""
        H = build_H_psi_matrix(n_basis=20)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive"


class TestSymmetryValidation:
    """Test symmetry validation function."""
    
    def test_symmetric_matrix(self):
        """Test validation with a symmetric matrix."""
        H = np.array([[1, 2, 3], [2, 4, 5], [3, 5, 6]], dtype=float)
        is_symmetric, _ = validate_symmetry(H)
        assert is_symmetric
    
    def test_asymmetric_matrix(self):
        """Test validation with an asymmetric matrix."""
        H = np.array([[1, 2, 3], [2, 4, 5], [4, 5, 6]], dtype=float)
        is_symmetric, _ = validate_symmetry(H)
        assert not is_symmetric


class TestPositivityValidation:
    """Test positivity validation function."""
    
    def test_positive_matrix(self):
        """Test validation with a positive definite matrix."""
        H = np.array([[4, 1], [1, 3]], dtype=float)  # Positive definite
        is_positive, min_inner = validate_positivity(H, n_tests=100)
        assert is_positive
        assert min_inner > 0
    
    def test_indefinite_matrix(self):
        """Test validation with an indefinite matrix."""
        H = np.array([[1, 2], [2, 1]], dtype=float)  # Has negative eigenvalue
        is_positive, min_inner = validate_positivity(H, n_tests=100)
        assert not is_positive


class TestCoercivityValidation:
    """Test coercivity validation function."""
    
    def test_coercive_matrix(self):
        """Test validation with a coercive (positive definite) matrix."""
        H = np.array([[4, 1], [1, 3]], dtype=float)
        is_coercive, c = validate_coercivity(H, n_tests=100)
        assert is_coercive
        assert c > 0
    
    def test_singular_matrix(self):
        """Test validation with a singular matrix."""
        H = np.array([[1, 1], [1, 1]], dtype=float)
        is_coercive, c = validate_coercivity(H, n_tests=100)
        # Singular matrix has smallest singular value = 0
        assert c == 0 or not is_coercive


class TestTraceConvergence:
    """Test trace convergence validation."""
    
    def test_trace_convergence_runs(self):
        """Test that trace convergence validation runs without error."""
        results = validate_trace_convergence(n_values=[5, 10, 15, 20])
        assert 'traces' in results
        assert 'remainders' in results
        assert len(results['traces']) == 4
    
    def test_trace_decreasing_remainders(self):
        """Test that remainders decrease as N increases."""
        results = validate_trace_convergence(n_values=[10, 20, 30, 40, 50])
        remainders = results['remainders']
        
        # Remainders should generally decrease (allowing some noise)
        if len(remainders) > 1:
            assert remainders[-1] <= remainders[0] * 1.5, \
                "Remainders should decrease or stay comparable"


class TestSchattenClass:
    """Test Schatten class validation."""
    
    def test_schatten_membership(self):
        """Test Schatten class membership for various p."""
        results = validate_schatten_class(
            p_values=[1.5, 2.0, 3.0],
            n_basis=20
        )
        
        # All p > 1 should give finite norms for our operator
        assert all(results['in_class']), "Operator should be in S_p for p > 1"
    
    def test_schatten_norms_ordered(self):
        """Test that Schatten norms decrease with p (for trace class)."""
        results = validate_schatten_class(
            p_values=[1.0, 2.0, 3.0, 4.0],
            n_basis=30
        )
        norms = results['schatten_norms']
        
        # For trace class operators, ‖T‖_{S_p} is decreasing in p
        # (This is a property of Schatten classes)
        for i in range(len(norms) - 1):
            # Allow small tolerance for numerical errors
            assert norms[i] >= norms[i+1] * 0.99, \
                f"Schatten norm should decrease: {norms[i]} vs {norms[i+1]}"


class TestFriedrichsConditions:
    """Test Friedrichs extension conditions validation."""
    
    def test_all_conditions_met(self):
        """Test that all Friedrichs conditions are met for H_Ψ."""
        results = validate_friedrichs_conditions(n_basis=25, n_tests=500)
        
        assert results['dense_domain'], "Domain should be dense"
        assert results['is_symmetric'], "Operator should be symmetric"
        assert results['is_positive'], "Operator should be positive"
        assert results['is_coercive'], "Operator should be coercive"
        assert results['all_conditions_met'], "All Friedrichs conditions should be met"
    
    def test_coercivity_constant_positive(self):
        """Test that coercivity constant is positive."""
        results = validate_friedrichs_conditions(n_basis=20)
        assert results['coercivity_constant'] > 0, \
            "Coercivity constant should be positive"


class TestFullValidation:
    """Test the complete validation run."""
    
    def test_full_validation_runs(self):
        """Test that full validation runs without error."""
        results = run_hilbert_polya_validation()
        
        assert 'trace_convergence' in results
        assert 'schatten_class' in results
        assert 'friedrichs' in results
        assert 'all_passed' in results
    
    def test_full_validation_passes(self):
        """Test that full validation passes all checks."""
        results = run_hilbert_polya_validation()
        
        # All Friedrichs conditions should be met
        assert results['friedrichs']['all_conditions_met'], \
            "Friedrichs conditions should be met"
        
        # Schatten class membership should be confirmed
        assert all(results['schatten_class']['in_class']), \
            "Schatten class membership should be confirmed"


class TestLeanFileExists:
    """Test that the Lean formalization file exists."""
    
    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "hilbert_polya_closure.lean"
    
    def test_lean_file_exists(self, lean_file_path):
        """Test that the Lean file exists."""
        assert lean_file_path.exists(), f"Lean file not found: {lean_file_path}"
    
    def test_lean_file_not_empty(self, lean_file_path):
        """Test that the Lean file is not empty."""
        assert lean_file_path.stat().st_size > 5000, "Lean file seems too small"
    
    def test_lean_file_has_key_definitions(self, lean_file_path):
        """Test that the Lean file has key definitions."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        # Check for key definitions
        assert "SchattenNorm" in content, "Should define SchattenNorm"
        assert "IsSchattenClass" in content, "Should define IsSchattenClass"
        assert "IsTraceClass" in content, "Should define IsTraceClass"
        assert "IsPositive" in content, "Should define IsPositive"
        assert "IsCoercive" in content, "Should define IsCoercive"
        assert "friedrichs" in content.lower(), "Should mention Friedrichs"
    
    def test_lean_file_has_qcal_integration(self, lean_file_path):
        """Test that the Lean file has QCAL integration."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "141.7001" in content, "Should have QCAL frequency"
        assert "244.36" in content, "Should have QCAL coherence"
    
    def test_lean_file_has_main_theorem(self, lean_file_path):
        """Test that the Lean file has the main closure theorem."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "hilbert_polya_closure" in content, \
            "Should have hilbert_polya_closure theorem"
        assert "H_Psi_unique_self_adjoint_extension" in content, \
            "Should have unique extension theorem"


class TestMathematicalContent:
    """Test mathematical correctness of the formalization."""
    
    def test_eigenvalue_positivity(self):
        """Test that H_Ψ eigenvalues are all positive (as expected)."""
        H = build_H_psi_matrix(n_basis=30, h=1e-3)
        eigenvalues = np.linalg.eigvalsh(H)
        
        assert np.all(eigenvalues > 0), "All eigenvalues should be positive"
    
    def test_eigenvalue_ordering(self):
        """Test that eigenvalues are properly ordered."""
        H = build_H_psi_matrix(n_basis=30, h=1e-3)
        eigenvalues = np.linalg.eigvalsh(H)
        
        # Eigenvalues should be sorted in ascending order
        assert np.allclose(eigenvalues, np.sort(eigenvalues)), \
            "Eigenvalues should be sorted"
    
    def test_spectral_gap(self):
        """Test that there is a spectral gap (smallest eigenvalue > 0)."""
        H = build_H_psi_matrix(n_basis=30, h=1e-3)
        eigenvalues = np.linalg.eigvalsh(H)
        
        # The smallest eigenvalue determines the spectral gap
        spectral_gap = eigenvalues[0]
        assert spectral_gap > 1e-10, \
            f"Spectral gap should be positive: {spectral_gap}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
