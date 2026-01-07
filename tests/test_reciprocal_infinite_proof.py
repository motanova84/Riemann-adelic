"""
Test module for RECIPROCAL_INFINITE_PROOF.lean

This test verifies that the Reciprocal Infinite Proof module
is properly structured and documented.

Author: José Manuel Mota Burruezo Ψ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: January 7, 2026

QCAL Integration:
Base frequency: 141.7001 Hz
Coherence: C = 244.36
Equation: Ψ = I × A_eff² × C^∞
"""

import os
import re
import pytest
from pathlib import Path

# Repository root
REPO_ROOT = Path(__file__).parent.parent
LEAN_FILE = REPO_ROOT / "formalization/lean/spectral/RECIPROCAL_INFINITE_PROOF.lean"
README_FILE = REPO_ROOT / "formalization/lean/spectral/RECIPROCAL_INFINITE_PROOF_README.md"


class TestReciprocalInfiniteProofStructure:
    """Test the structure and content of the Reciprocal Infinite Proof module."""

    def test_lean_file_exists(self):
        """Verify that RECIPROCAL_INFINITE_PROOF.lean exists."""
        assert LEAN_FILE.exists(), f"Lean file not found at {LEAN_FILE}"
        
    def test_readme_file_exists(self):
        """Verify that RECIPROCAL_INFINITE_PROOF_README.md exists."""
        assert README_FILE.exists(), f"README not found at {README_FILE}"

    def test_lean_file_size(self):
        """Verify the Lean file has substantial content."""
        file_size = LEAN_FILE.stat().st_size
        # Should be at least 10KB
        assert file_size > 10000, f"Lean file too small: {file_size} bytes"

    def test_readme_file_size(self):
        """Verify the README has substantial content."""
        file_size = README_FILE.stat().st_size
        # Should be at least 5KB
        assert file_size > 5000, f"README too small: {file_size} bytes"


class TestReciprocalInfiniteProofContent:
    """Test the mathematical content of the module."""

    @pytest.fixture
    def lean_content(self):
        """Load the Lean file content."""
        with open(LEAN_FILE, 'r', encoding='utf-8') as f:
            return f.read()

    @pytest.fixture
    def readme_content(self):
        """Load the README content."""
        with open(README_FILE, 'r', encoding='utf-8') as f:
            return f.read()

    def test_has_author_info(self, lean_content):
        """Verify author information is present."""
        assert "José Manuel Mota Burruezo" in lean_content
        assert "0009-0002-1923-0773" in lean_content
        assert "10.5281/zenodo.17379721" in lean_content

    def test_has_qcal_integration(self, lean_content):
        """Verify QCAL integration information."""
        assert "141.7001 Hz" in lean_content or "141.7001Hz" in lean_content
        assert "C = 244.36" in lean_content or "244.36" in lean_content

    def test_has_main_strategies(self, lean_content):
        """Verify all 5 strategies are present."""
        strategies = [
            "ESTRATEGIA 1",
            "ESTRATEGIA 2", 
            "ESTRATEGIA 3",
            "ESTRATEGIA 4",
            "ESTRATEGIA 5"
        ]
        for strategy in strategies:
            assert strategy in lean_content, f"Missing {strategy}"

    def test_has_key_theorems(self, lean_content):
        """Verify key theorems are defined."""
        theorems = [
            "spectral_induction_step",
            "zeros_density_proven",
            "spectral_reciprocity",
            "cardinality_implies_equality",
            "transfinite_induction_on_zeros",
            "infinite_proof_by_reciprocity"
        ]
        for theorem in theorems:
            assert theorem in lean_content, f"Missing theorem: {theorem}"

    def test_has_proper_imports(self, lean_content):
        """Verify proper Mathlib imports."""
        required_imports = [
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.NumberTheory.ZetaFunction",
            "Mathlib.Topology.Instances.Real"
        ]
        for imp in required_imports:
            assert imp in lean_content, f"Missing import: {imp}"

    def test_has_namespace(self, lean_content):
        """Verify proper namespace definition."""
        assert "namespace SpectralReciprocity" in lean_content
        assert "end SpectralReciprocity" in lean_content

    def test_readme_has_strategies_explained(self, readme_content):
        """Verify README explains all 5 strategies."""
        strategy_markers = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣"]
        for marker in strategy_markers:
            assert marker in readme_content, f"Missing strategy marker: {marker}"

    def test_readme_has_flow_diagram(self, readme_content):
        """Verify README includes flow diagram."""
        assert "BASE (Verificado)" in readme_content or "BASE (Verified)" in readme_content
        assert "INFINITO" in readme_content

    def test_readme_has_references(self, readme_content):
        """Verify README includes mathematical references."""
        assert "Berry" in readme_content or "Keating" in readme_content
        assert "Riemann-von Mangoldt" in readme_content or "Riemann" in readme_content


class TestReciprocalInfiniteProofIntegration:
    """Test integration with the rest of the repository."""

    def test_implementation_summary_updated(self):
        """Verify IMPLEMENTATION_SUMMARY.md mentions the new module."""
        impl_summary = REPO_ROOT / "IMPLEMENTATION_SUMMARY.md"
        assert impl_summary.exists()
        
        with open(impl_summary, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "RECIPROCAL_INFINITE_PROOF" in content or "Reciprocidad Infinita" in content

    def test_spectral_directory_structure(self):
        """Verify the file is in the correct directory."""
        assert LEAN_FILE.parent.name == "spectral"
        assert README_FILE.parent.name == "spectral"

    def test_file_permissions(self):
        """Verify files are readable."""
        assert os.access(LEAN_FILE, os.R_OK), "Lean file not readable"
        assert os.access(README_FILE, os.R_OK), "README not readable"


class TestMathematicalConcepts:
    """Test that key mathematical concepts are properly documented."""

    @pytest.fixture
    def lean_content(self):
        """Load the Lean file content."""
        with open(LEAN_FILE, 'r', encoding='utf-8') as f:
            return f.read()

    def test_mentions_10_to_13_zeros(self, lean_content):
        """Verify the base of 10^13 zeros is mentioned."""
        assert "10^13" in lean_content or "10¹³" in lean_content

    def test_mentions_density(self, lean_content):
        """Verify density concepts are present."""
        assert "Dense" in lean_content or "density" in lean_content.lower()

    def test_mentions_continuity(self, lean_content):
        """Verify continuity concepts are present."""
        assert "Continuous" in lean_content or "continuity" in lean_content.lower()

    def test_mentions_cardinality(self, lean_content):
        """Verify cardinality concepts are present."""
        assert "Cardinal" in lean_content or "cardinality" in lean_content.lower()

    def test_mentions_spectrum(self, lean_content):
        """Verify spectral concepts are present."""
        assert "Spectrum" in lean_content or "spectrum" in lean_content.lower()
        assert "H_psi" in lean_content or "H_Ψ" in lean_content

    def test_mentions_reciprocity(self, lean_content):
        """Verify reciprocity is a central concept."""
        # Should appear multiple times
        count = lean_content.lower().count("reciproc")
        assert count >= 5, f"Reciprocity mentioned only {count} times, expected at least 5"


def test_lean_syntax_basic():
    """Basic syntax check for the Lean file."""
    with open(LEAN_FILE, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check for balanced delimiters
    assert content.count('/-') == content.count('-/'), "Unbalanced comment delimiters"
    
    # Check that file ends with 'end'
    lines = [line.strip() for line in content.split('\n') if line.strip()]
    assert lines[-1] == 'end', "File should end with 'end'"
    
    # Check namespace is properly opened and closed
    open_count = content.count('namespace SpectralReciprocity')
    close_count = content.count('end SpectralReciprocity')
    assert open_count == close_count == 1, "Namespace not properly balanced"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
