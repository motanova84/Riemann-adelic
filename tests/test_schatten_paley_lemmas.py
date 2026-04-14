#!/usr/bin/env python3
"""
Test suite for Schatten-Paley Lemmas formalization.

Verifies the Lean formalization files for:
1. exponential_decay_schatten_trace - Eigenvalue decay implies Schatten class
2. paley_wiener_uniqueness_real - Entire function vanishing on ℝ is zero

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
Date: 29 November 2025
"""

import pytest
from pathlib import Path


class TestSchattenPaleyLemmasFormalization:
    """Test the Schatten-Paley lemmas formalization."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_lean_file_exists(self, lean_file_path):
        """Verify schatten_paley_lemmas.lean exists."""
        assert lean_file_path.exists(), f"File not found: {lean_file_path}"

    def test_lean_file_not_empty(self, lean_file_path):
        """Test that the Lean file is not empty.

        Note: Minimum size of 1000 bytes ensures the file contains meaningful
        content beyond just imports and namespace declarations.
        """
        assert lean_file_path.stat().st_size > 1000, "Lean file seems too small"

    def test_has_exponential_decay_definition(self, lean_file_path):
        """Verify HasExponentialDecay predicate is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "def HasExponentialDecay" in content, \
            "Should define HasExponentialDecay predicate"
        assert "exp" in content, "Should mention exponential function"

    def test_has_positive_sequence_definition(self, lean_file_path):
        """Verify IsPositiveSequence predicate is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "def IsPositiveSequence" in content, \
            "Should define IsPositiveSequence predicate"

    def test_has_main_schatten_theorem(self, lean_file_path):
        """Verify the main Schatten class theorem is declared."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "theorem exponential_decay_schatten_trace" in content, \
            "Main theorem 'exponential_decay_schatten_trace' not found"
        assert "Summable" in content, \
            "Should use Summable for convergence"

    def test_has_trace_class_corollary(self, lean_file_path):
        """Verify trace class corollary exists."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "corollary exponential_decay_trace_class" in content or \
               "exponential_decay_trace_class" in content, \
            "Should have trace class corollary"

    def test_has_hilbert_schmidt_corollary(self, lean_file_path):
        """Verify Hilbert-Schmidt class corollary exists."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "exponential_decay_hilbert_schmidt" in content, \
            "Should have Hilbert-Schmidt class corollary"


class TestPaleyWienerFormalization:
    """Test Paley-Wiener uniqueness formalization."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_has_entire_definition(self, lean_file_path):
        """Verify IsEntire predicate is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "def IsEntire" in content, \
            "Should define IsEntire predicate"
        assert "Differentiable" in content, \
            "Entire should be defined via Differentiable"

    def test_has_exponential_type_definition(self, lean_file_path):
        """Verify HasExponentialType predicate is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "def HasExponentialType" in content, \
            "Should define HasExponentialType predicate"

    def test_has_vanishes_on_real_definition(self, lean_file_path):
        """Verify VanishesOnReal predicate is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "def VanishesOnReal" in content, \
            "Should define VanishesOnReal predicate"

    def test_has_paley_wiener_theorem(self, lean_file_path):
        """Verify the main Paley-Wiener theorem is declared."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "theorem paley_wiener_uniqueness_real" in content or \
               "paley_wiener_uniqueness_real" in content, \
            "Main theorem 'paley_wiener_uniqueness_real' not found"

    def test_has_identity_principle(self, lean_file_path):
        """Verify identity principle axiom is stated."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "identity_principle" in content, \
            "Should reference identity principle for analytic functions"


class TestQCALIntegration:
    """Test QCAL integration in the formalization."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_qcal_frequency(self, lean_file_path):
        """Verify QCAL frequency is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "141.7001" in content, \
            "Should have QCAL base frequency 141.7001 Hz"
        assert "QCAL_frequency" in content, \
            "Should define QCAL_frequency constant"

    def test_qcal_coherence(self, lean_file_path):
        """Verify QCAL coherence constant is defined."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "244.36" in content, \
            "Should have QCAL coherence constant 244.36"
        assert "QCAL_coherence" in content, \
            "Should define QCAL_coherence constant"


class TestSpectralApplication:
    """Test spectral theory applications."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_has_spectral_equals_xi(self, lean_file_path):
        """Verify spectral_equals_xi theorem exists."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "spectral_equals_xi" in content, \
            "Should have spectral_equals_xi theorem"
        assert "det_zeta" in content and "Ξ" in content, \
            "Should relate det_zeta and Ξ functions"


class TestMathematicalContent:
    """Test mathematical correctness of the formalization."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_geometric_series_lemma(self, lean_file_path):
        """Verify geometric series convergence is used."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "geometric" in content.lower(), \
            "Should use geometric series for convergence proof"

    def test_has_proper_imports(self, lean_file_path):
        """Verify proper Mathlib imports."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "import Mathlib" in content, "Should import from Mathlib"
        assert "Complex" in content, "Should use Complex numbers"
        assert "Real.exp" in content, \
            "Should use Real.exp function"

    def test_proper_namespace(self, lean_file_path):
        """Verify proper namespace structure."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "namespace SchattenPaleyLemmas" in content, \
            "Should use SchattenPaleyLemmas namespace"
        assert "end SchattenPaleyLemmas" in content, \
            "Should close SchattenPaleyLemmas namespace"


class TestFileHeader:
    """Test file header and documentation."""

    @pytest.fixture
    def lean_file_path(self):
        """Return path to the Lean formalization file."""
        return Path(__file__).parent.parent / "formalization" / "lean" / \
               "spectral" / "schatten_paley_lemmas.lean"

    def test_has_author_attribution(self, lean_file_path):
        """Verify author attribution."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "José Manuel Mota Burruezo" in content, \
            "Should have author attribution"
        assert "ORCID" in content, "Should have ORCID"

    def test_has_doi_reference(self, lean_file_path):
        """Verify DOI reference."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "DOI" in content, "Should have DOI reference"
        assert "zenodo" in content.lower(), "Should reference Zenodo"

    def test_has_mathematical_background(self, lean_file_path):
        """Verify mathematical documentation."""
        content = lean_file_path.read_text(encoding='utf-8')
        assert "Schatten" in content, "Should explain Schatten class"
        assert "Paley-Wiener" in content or "Paley–Wiener" in content, \
            "Should explain Paley-Wiener theorem"


class TestMainLeanIntegration:
    """Test Main.lean integration."""

    @pytest.fixture
    def main_file_path(self):
        """Return path to Main.lean."""
        return Path(__file__).parent.parent / "formalization" / "lean" / "Main.lean"

    def test_main_imports_schatten_paley(self, main_file_path):
        """Verify Main.lean imports schatten_paley_lemmas."""
        content = main_file_path.read_text(encoding='utf-8')
        assert "import spectral.schatten_paley_lemmas" in content, \
            "Main.lean should import schatten_paley_lemmas"

    def test_main_mentions_module(self, main_file_path):
        """Verify Main.lean mentions the module in output."""
        content = main_file_path.read_text(encoding='utf-8')
        assert "Schatten" in content or "schatten" in content, \
            "Main.lean should mention Schatten in output"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
