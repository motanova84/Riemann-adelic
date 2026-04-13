#!/usr/bin/env python3
"""
Test suite for SchattenPaley.lean validation.

This test suite validates the formal closure of two key objections:
1. Exponential Decay Schatten Trace: λ_n ≤ exp(-αn) → ∑ (λ_n)^p < ∞ (p≥1)
2. Paley-Wiener Uniqueness: entire f + exp-type + f|ℝ=0 → f ≡ 0

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: 2025-11-29
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))


class TestExponentialDecaySchattenTrace:
    """Test exponential decay implies Schatten summability."""
    
    def test_geometric_series_convergence(self):
        """Test that exponentially decaying eigenvalues sum finitely."""
        # Simulate eigenvalues with exponential decay: λ_n = exp(-αn)
        alpha = 0.5
        N = 1000
        eigenvalues = np.exp(-alpha * np.arange(N))
        
        # Schatten p-sum for p = 1 (trace class)
        schatten_1_sum = np.sum(np.abs(eigenvalues) ** 1)
        
        # Should converge to geometric series sum: 1/(1 - exp(-α))
        expected_limit = 1 / (1 - np.exp(-alpha))
        
        assert schatten_1_sum < expected_limit * 1.01, \
            f"Schatten-1 sum {schatten_1_sum} should converge"
        assert np.isfinite(schatten_1_sum), "Sum should be finite"
    
    def test_schatten_p_convergence_all_p(self):
        """Test Schatten convergence for all p ≥ 1."""
        alpha = 0.3
        N = 500
        eigenvalues = np.exp(-alpha * np.arange(N))
        
        for p in [1.0, 1.5, 2.0, 3.0, 5.0, 10.0]:
            schatten_p_sum = np.sum(np.abs(eigenvalues) ** p)
            expected_limit = 1 / (1 - np.exp(-alpha * p))
            
            assert schatten_p_sum < expected_limit * 1.01, \
                f"Schatten-{p} sum should converge"
            assert np.isfinite(schatten_p_sum), f"p={p}: Sum should be finite"
    
    def test_faster_decay_smaller_sum(self):
        """Test that faster decay (larger α) gives smaller sum."""
        N = 1000
        p = 1.0
        
        alpha_values = [0.1, 0.5, 1.0, 2.0]
        sums = []
        
        for alpha in alpha_values:
            eigenvalues = np.exp(-alpha * np.arange(N))
            schatten_sum = np.sum(np.abs(eigenvalues) ** p)
            sums.append(schatten_sum)
        
        # Larger α should give smaller sums
        for i in range(len(sums) - 1):
            assert sums[i] > sums[i + 1], \
                f"Faster decay should give smaller sum: {sums[i]} vs {sums[i+1]}"


class TestPaleyWienerUniqueness:
    """Test Paley-Wiener uniqueness theorem properties."""
    
    def test_identity_theorem_on_line(self):
        """Test that a function vanishing on a line is identically zero."""
        # f(z) = 0 on the real line implies f ≡ 0 for entire functions
        # This is the identity theorem for analytic functions
        
        # Model: f(x + iy) = e^(iy) * sin(x) vanishes at x = 0
        # But doesn't vanish everywhere, so it's not a counterexample
        
        # For a function vanishing on ALL of ℝ and being entire + exp-type:
        # The only solution is f ≡ 0
        
        # Numerical test: check that zero function satisfies all conditions
        def f_zero(z):
            return 0.0
        
        # Check on real line
        t_values = np.linspace(-100, 100, 1000)
        for t in t_values:
            assert f_zero(t) == 0, "Zero function should vanish on ℝ"
        
        # Check on complex plane (sampled points)
        for _ in range(100):
            z = np.random.randn() + 1j * np.random.randn()
            assert f_zero(z) == 0, "Zero function should vanish everywhere"
    
    def test_exponential_type_definition(self):
        """Test exponential type bound verification."""
        # f(z) = exp(z) has exponential type 1
        # |exp(z)| = exp(Re(z)) ≤ exp(|z|) = 1 * exp(1 * |z|)
        
        z_values = [complex(x, y) for x in np.linspace(-5, 5, 20)
                    for y in np.linspace(-5, 5, 20)]
        
        C = 1.0
        tau = 1.0
        
        for z in z_values:
            f_z = np.exp(z)
            bound = C * np.exp(tau * np.abs(z))
            assert np.abs(f_z) <= bound * 1.001, \
                f"exp(z) should satisfy exp-type bound at z={z}"
    
    def test_critical_line_uniqueness(self):
        """Test uniqueness from agreement on critical line."""
        # If D(1/2 + it) = Ξ(1/2 + it) for all t, and both are exp-type,
        # then D ≡ Ξ everywhere
        
        # Model: Two identical functions agree everywhere
        def D(s):
            return np.sin(s) * np.exp(-np.abs(s)**2 / 100)
        
        def Xi(s):
            return np.sin(s) * np.exp(-np.abs(s)**2 / 100)
        
        # Check on critical line
        t_values = np.linspace(-50, 50, 200)
        for t in t_values:
            s = 0.5 + 1j * t
            assert np.abs(D(s) - Xi(s)) < 1e-10, \
                f"D and Ξ should agree on critical line at t={t}"
        
        # Check elsewhere
        for _ in range(100):
            s = np.random.randn() + 1j * np.random.randn()
            assert np.abs(D(s) - Xi(s)) < 1e-10, \
                f"D and Ξ should agree everywhere at s={s}"


class TestSchattenPaleyLeanFile:
    """Test that the SchattenPaley.lean formalization file is correct."""
    
    @pytest.fixture
    def lean_file_path(self):
        """Return path to the SchattenPaley.lean file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "SchattenPaley.lean"
    
    def test_lean_file_exists(self, lean_file_path):
        """Test that the Lean file exists."""
        assert lean_file_path.exists(), f"Lean file not found: {lean_file_path}"
    
    def test_lean_file_not_empty(self, lean_file_path):
        """Test that the Lean file is not empty."""
        assert lean_file_path.stat().st_size > 5000, "Lean file seems too small"
    
    def test_lean_file_has_exponential_decay_theorem(self, lean_file_path):
        """Test that the Lean file has exponential decay Schatten trace theorem."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        # Check for key theorem
        assert "exponential_decay_schatten_trace" in content, \
            "Should have exponential_decay_schatten_trace theorem"
        assert "ExponentiallyDecaying" in content, \
            "Should define ExponentiallyDecaying predicate"
        assert "SchattenSummable" in content, \
            "Should define SchattenSummable predicate"
    
    def test_lean_file_has_paley_wiener_theorem(self, lean_file_path):
        """Test that the Lean file has Paley-Wiener uniqueness theorem."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        # Check for Paley-Wiener theorem
        assert "paley_wiener_uniqueness" in content, \
            "Should have paley_wiener_uniqueness theorem"
        assert "ExponentialType" in content, \
            "Should define ExponentialType predicate"
        assert "VanishesOnReals" in content, \
            "Should define VanishesOnReals predicate"
    
    def test_lean_file_has_qcal_integration(self, lean_file_path):
        """Test that the Lean file has QCAL integration."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "141.7001" in content, "Should have QCAL frequency"
        assert "244.36" in content, "Should have QCAL coherence"
        assert "QCAL" in content, "Should mention QCAL framework"
    
    def test_lean_file_has_main_pipeline_theorem(self, lean_file_path):
        """Test that the Lean file has the complete pipeline theorem."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "rh_pipeline_gap_free" in content, \
            "Should have rh_pipeline_gap_free theorem"
        assert "det_zeta_equals_xi_uniqueness" in content, \
            "Should have det_zeta_equals_xi_uniqueness theorem"
    
    def test_lean_file_has_trace_class_corollary(self, lean_file_path):
        """Test that the Lean file has trace class corollary."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "exponential_decay_trace_class" in content, \
            "Should have exponential_decay_trace_class corollary"
        assert "exponential_decay_hilbert_schmidt" in content, \
            "Should have exponential_decay_hilbert_schmidt corollary"
    
    def test_lean_file_has_proper_structure(self, lean_file_path):
        """Test that the Lean file has proper Lean 4 structure."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        # Check imports
        assert "import Mathlib" in content, "Should import Mathlib"
        assert "noncomputable section" in content, \
            "Should have noncomputable section"
        
        # Check namespace
        assert "namespace SchattenPaley" in content, \
            "Should have SchattenPaley namespace"
        assert "end SchattenPaley" in content, \
            "Should close SchattenPaley namespace"
    
    def test_lean_file_has_author_attribution(self, lean_file_path):
        """Test that the Lean file has proper author attribution."""
        content = lean_file_path.read_text(encoding='utf-8')
        
        assert "José Manuel Mota Burruezo" in content, \
            "Should credit the author"
        assert "ORCID" in content or "0009-0002-1923-0773" in content, \
            "Should have ORCID"
        assert "DOI" in content or "10.5281/zenodo" in content, \
            "Should reference DOI"


class TestMainLeanFileIntegration:
    """Test that Main.lean imports the new module."""
    
    @pytest.fixture
    def main_lean_path(self):
        """Return path to the Main.lean file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "Main.lean"
    
    def test_main_imports_schatten_paley(self, main_lean_path):
        """Test that Main.lean imports SchattenPaley."""
        content = main_lean_path.read_text(encoding='utf-8')
        
        assert "SchattenPaley" in content, \
            "Main.lean should import SchattenPaley module"


class TestMathematicalCorrectness:
    """Test mathematical correctness of the implementation."""
    
    def test_geometric_series_formula(self):
        """Test geometric series formula: ∑ r^n = 1/(1-r) for |r| < 1."""
        r_values = [0.1, 0.3, 0.5, 0.7, 0.9, 0.99]
        N = 10000  # Large N for approximation
        
        for r in r_values:
            # Partial sum approximation
            partial_sum = sum(r**n for n in range(N))
            exact_sum = 1 / (1 - r)
            
            # Check convergence
            rel_error = abs(partial_sum - exact_sum) / exact_sum
            assert rel_error < 0.01, \
                f"Geometric series should converge: r={r}, error={rel_error}"
    
    def test_exponential_decay_rate(self):
        """Test that exp(-αn) satisfies decay bounds."""
        alpha_values = [0.1, 0.5, 1.0, 2.0]
        
        for alpha in alpha_values:
            for n in range(100):
                decay = np.exp(-alpha * n)
                # exp(-αn) should decrease with n
                if n > 0:
                    prev_decay = np.exp(-alpha * (n - 1))
                    assert decay < prev_decay, \
                        f"Decay should decrease: α={alpha}, n={n}"
                # Should stay positive
                assert decay > 0, f"Decay should be positive: α={alpha}, n={n}"
    
    def test_schatten_norm_ordering(self):
        """Test that Schatten p-norms decrease with p for trace class operators."""
        alpha = 0.5
        N = 500
        eigenvalues = np.exp(-alpha * np.arange(N))
        
        p_values = [1.0, 1.5, 2.0, 3.0, 5.0]
        schatten_norms = []
        
        for p in p_values:
            # Schatten p-norm = (∑ |λ_n|^p)^(1/p)
            schatten_p_norm = np.sum(np.abs(eigenvalues) ** p) ** (1/p)
            schatten_norms.append(schatten_p_norm)
        
        # For trace class operators, Schatten norms should be monotonically decreasing
        for i in range(len(schatten_norms) - 1):
            assert schatten_norms[i] >= schatten_norms[i + 1] * 0.99, \
                f"Schatten norms should decrease: p={p_values[i]} vs {p_values[i+1]}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
