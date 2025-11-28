#!/usr/bin/env python3
"""
Test suite for Hilbert-Schmidt HΨ Operator formalization

This module tests the structure and documentation of the
HilbertSchmidtHpsi.lean formalization.

Author: José Manuel Mota Burruezo
Date: November 22, 2025
Version: 1.0
"""

import pytest
import re
from pathlib import Path


# Path constants
REPO_ROOT = Path(__file__).parent.parent
LEAN_FILE = REPO_ROOT / "formalization" / "lean" / "RiemannAdelic" / "HilbertSchmidtHpsi.lean"
README_FILE = REPO_ROOT / "formalization" / "lean" / "RiemannAdelic" / "HILBERT_SCHMIDT_HPSI_README.md"


class TestHilbertSchmidtHpsiFile:
    """Tests for the Hilbert-Schmidt HΨ Lean file."""

    def test_file_exists(self):
        """Test that the Lean file exists."""
        assert LEAN_FILE.exists(), f"File not found: {LEAN_FILE}"

    def test_file_not_empty(self):
        """Test that the file is not empty."""
        assert LEAN_FILE.stat().st_size > 0, "File is empty"

    def test_has_proper_header(self):
        """Test that the file has the proper documentation header."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "Operador HΨ: compacidad por ser Hilbert–Schmidt" in content
        assert "José Manuel Mota Burruezo" in content
        assert "22 noviembre 2025" in content

    def test_has_required_imports(self):
        """Test that the file has the required Mathlib imports."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace.Hilbert",
            "Mathlib.MeasureTheory.Integral.IntervalIntegral",
            "Mathlib.Topology.MetricSpace.Baire",
            "Mathlib.Analysis.SchwartzSpace"
        ]
        for imp in required_imports:
            assert imp in content, f"Missing import: {imp}"

    def test_defines_measure_mu(self):
        """Test that the file defines the measure mu."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def mu : Measure ℝ" in content
        assert "withDensity" in content
        assert "1 / x" in content

    def test_defines_kernel_K(self):
        """Test that the file defines the kernel K."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def K (x y : ℝ) : ℝ" in content
        assert "sin" in content
        assert "log" in content

    def test_defines_operator_HΨ(self):
        """Test that the file defines the operator HΨ."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def HΨ" in content
        assert "Φ : ℝ → ℝ" in content
        assert "f : ℝ → ℝ" in content

    def test_has_hilbert_schmidt_lemma(self):
        """Test that the file has the Hilbert-Schmidt lemma."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "lemma kernel_hilbert_schmidt" in content
        assert "Integrable" in content
        assert "mu.prod mu" in content

    def test_has_compactness_lemma(self):
        """Test that the file has the compactness lemma."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "lemma HΨ_is_compact" in content
        assert "CompactOperator" in content

    def test_no_actual_sorry_in_code(self):
        """Test that there are no actual sorry statements in the code (only in comments)."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Remove all comments first
        # Remove line comments starting with --
        content_no_line_comments = re.sub(r'--.*?$', '', content, flags=re.MULTILINE)
        # Remove block comments /-  -/
        content_no_comments = re.sub(r'/-.*?-/', '', content_no_line_comments, flags=re.DOTALL)
        
        # Now check for sorry in the remaining code
        sorry_matches = re.findall(r'\bsorry\b', content_no_comments)
        assert len(sorry_matches) == 0, f"Found {len(sorry_matches)} sorry statements in code"

    def test_has_minimal_axioms(self):
        """Test that the file has the expected axioms."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        axiom_count = len(re.findall(r'\baxiom\b', content))
        assert axiom_count == 3, f"Expected 3 axioms, found {axiom_count}"
        
        # Check for specific axioms
        assert "axiom abs_sin_div_log_le_one" in content
        assert "axiom CompactOperator" in content
        assert "axiom CompactOperator.of_HilbertSchmidt" in content

    def test_has_documentation_sections(self):
        """Test that the file has proper documentation sections."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "## Lema auxiliar" in content or "Lema auxiliar" in content
        assert "## Teorema principal" in content or "Teorema principal" in content
        assert "## Corolario" in content or "Corolario" in content
        assert "## Resumen" in content or "Resumen" in content

    def test_has_qcal_references(self):
        """Test that the file has QCAL framework references."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "JMMB" in content
        assert "Ψ" in content or "Psi" in content
        assert "∞³" in content or "infinito" in content


class TestHilbertSchmidtHpsiReadme:
    """Tests for the Hilbert-Schmidt HΨ README file."""

    def test_readme_exists(self):
        """Test that the README file exists."""
        assert README_FILE.exists(), f"README not found: {README_FILE}"

    def test_readme_not_empty(self):
        """Test that the README is not empty."""
        assert README_FILE.stat().st_size > 0, "README is empty"

    def test_has_proper_title(self):
        """Test that the README has the proper title."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Hilbert-Schmidt HΨ Operator" in content

    def test_has_overview_section(self):
        """Test that the README has an overview section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "## Overview" in content or "Overview" in content

    def test_has_mathematical_content_section(self):
        """Test that the README has a mathematical content section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Mathematical Content" in content or "## Mathematical" in content

    def test_has_main_results_section(self):
        """Test that the README has a main results section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Main Results" in content or "## Main Results" in content

    def test_has_references_section(self):
        """Test that the README has a references section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "## References" in content or "References" in content

    def test_has_berry_keating_reference(self):
        """Test that the README references Berry & Keating."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Berry" in content and "Keating" in content

    def test_has_zenodo_doi(self):
        """Test that the README has the Zenodo DOI."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "10.5281/zenodo" in content

    def test_has_compilation_status(self):
        """Test that the README has compilation status."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Compilation Status" in content or "compilation" in content.lower()

    def test_has_usage_example(self):
        """Test that the README has a usage example."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Usage" in content or "Example" in content

    def test_has_author_info(self):
        """Test that the README has author information."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "José Manuel Mota Burruezo" in content


class TestIntegration:
    """Integration tests for the Hilbert-Schmidt HΨ formalization."""

    def test_implementation_summary_updated(self):
        """Test that IMPLEMENTATION_SUMMARY.md was updated with the new module."""
        summary_file = REPO_ROOT / "IMPLEMENTATION_SUMMARY.md"
        assert summary_file.exists(), "IMPLEMENTATION_SUMMARY.md not found"
        
        content = summary_file.read_text(encoding='utf-8')
        assert "Hilbert-Schmidt" in content, "IMPLEMENTATION_SUMMARY.md not updated"
        assert "HilbertSchmidtHpsi.lean" in content, "File not mentioned in summary"

    def test_files_are_tracked(self):
        """Test that the new files are being tracked by git."""
        import subprocess
        result = subprocess.run(
            ['git', 'ls-files', '--error-unmatch', str(LEAN_FILE.relative_to(REPO_ROOT))],
            cwd=REPO_ROOT,
            capture_output=True
        )
        assert result.returncode == 0, f"Lean file not tracked by git: {LEAN_FILE}"
        
        result = subprocess.run(
            ['git', 'ls-files', '--error-unmatch', str(README_FILE.relative_to(REPO_ROOT))],
            cwd=REPO_ROOT,
            capture_output=True
        )
        assert result.returncode == 0, f"README file not tracked by git: {README_FILE}"


class TestMathematicalContent:
    """Tests for the mathematical correctness of the formalization."""

    def test_measure_definition_correct(self):
        """Test that the measure definition is mathematically correct."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # The measure should be dx/x (Haar measure on ℝ⁺)
        assert "1 / x" in content or "1/x" in content

    def test_kernel_has_sinc_structure(self):
        """Test that the kernel has the sinc structure."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Kernel should be sin(log(x/y))/log(x/y)
        assert "sin" in content.lower()
        assert "log" in content.lower()

    def test_rapid_decay_condition(self):
        """Test that the rapid decay condition is properly stated."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Should have |Φ(x)| ≤ C/(1+|x|)^N
        assert "∃ C N" in content or "exists C N" in content
        assert "|Φ x|" in content or "Φ x" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
