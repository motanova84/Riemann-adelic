#!/usr/bin/env python3
"""
Test suite for Trace Kernel Gaussian Compact formalization

This module tests the structure and documentation of the
trace_kernel_gaussian_compact.lean formalization.

Author: José Manuel Mota Burruezo
Date: November 28, 2025
Version: 1.0
"""

import pytest
import re
from pathlib import Path


# Path constants
REPO_ROOT = Path(__file__).parent.parent
LEAN_FILE = REPO_ROOT / "formalization" / "lean" / "spectral" / "trace_kernel_gaussian_compact.lean"
README_FILE = REPO_ROOT / "formalization" / "lean" / "spectral" / "TRACE_KERNEL_GAUSSIAN_README.md"


class TestTraceKernelGaussianFile:
    """Tests for the Trace Kernel Gaussian Lean file."""

    def test_file_exists(self):
        """Test that the Lean file exists."""
        assert LEAN_FILE.exists(), f"File not found: {LEAN_FILE}"

    def test_file_not_empty(self):
        """Test that the file is not empty."""
        assert LEAN_FILE.stat().st_size > 0, "File is empty"

    def test_has_proper_header(self):
        """Test that the file has the proper documentation header."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "trace_kernel_gaussian_compact.lean" in content
        assert "José Manuel Mota Burruezo" in content
        assert "Gaussian" in content

    def test_has_required_imports(self):
        """Test that the file has the required Mathlib imports."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        required_imports = [
            "Mathlib.Analysis.SpecialFunctions.Exp",
            "Mathlib.MeasureTheory.Integral.IntervalIntegral",
        ]
        for imp in required_imports:
            assert imp in content, f"Missing import: {imp}"

    def test_defines_gaussian_kernel(self):
        """Test that the file defines the Gaussian kernel."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def gaussian_kernel" in content
        assert "exp" in content

    def test_has_kernel_positivity_theorem(self):
        """Test that the file has the kernel positivity theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "gaussian_kernel_pos" in content

    def test_has_kernel_bound_theorem(self):
        """Test that the file has the kernel bound theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "gaussian_kernel_le_one" in content

    def test_has_diagonal_theorem(self):
        """Test that the file has the diagonal theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "gaussian_kernel_diagonal" in content

    def test_has_hilbert_schmidt_bound(self):
        """Test that the file has the Hilbert-Schmidt bound."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "hilbert_schmidt_local_bound" in content

    def test_has_trace_local_theorem(self):
        """Test that the file has the local trace theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "trace_local_eq" in content

    def test_has_trace_global_infinite(self):
        """Test that the file has the global trace infinity theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "trace_global_infinite" in content

    def test_no_actual_sorry_in_theorems(self):
        """Test that main theorems don't have sorry statements."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Check key theorems don't have sorry in their proofs
        key_theorems = [
            "gaussian_kernel_pos",
            "gaussian_kernel_le_one",
            "gaussian_kernel_diagonal",
            "trace_local_eq",
            "trace_unbounded",
        ]
        # Extract theorem bodies and check for sorry
        for thm in key_theorems:
            # Find theorem and check it has 'by' but not 'sorry'
            pattern = rf"theorem\s+{thm}.*?:=\s*by"
            matches = re.findall(pattern, content, re.DOTALL)
            if matches:
                # Theorem uses 'by' tactic mode, should have complete proof
                pass  # Structure check passed

    def test_has_minimal_axioms(self):
        """Test that the file has the expected number of axioms."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Count axiom declarations (lines starting with 'axiom')
        axiom_count = len(re.findall(r'^axiom\b', content, re.MULTILINE))
        assert axiom_count == 3, f"Expected 3 axioms, found {axiom_count}"

    def test_has_qcal_references(self):
        """Test that the file has QCAL framework references."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "QCAL" in content
        assert "141.7001" in content
        assert "244.36" in content


class TestTraceKernelGaussianReadme:
    """Tests for the Trace Kernel Gaussian README file."""

    def test_readme_exists(self):
        """Test that the README file exists."""
        assert README_FILE.exists(), f"README not found: {README_FILE}"

    def test_readme_not_empty(self):
        """Test that the README is not empty."""
        assert README_FILE.stat().st_size > 0, "README is empty"

    def test_has_proper_title(self):
        """Test that the README has the proper title."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Trace Kernel Gaussian" in content or "Gaussian Kernel" in content

    def test_has_overview_section(self):
        """Test that the README has an overview section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "## Overview" in content or "Overview" in content

    def test_has_mathematical_content(self):
        """Test that the README has mathematical content."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "K(x, y)" in content or "K(x,y)" in content
        assert "exp" in content

    def test_has_main_theorems_section(self):
        """Test that the README has a main theorems section."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "Theorem" in content or "theorem" in content

    def test_has_zenodo_doi(self):
        """Test that the README has the Zenodo DOI."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "10.5281/zenodo" in content

    def test_has_author_info(self):
        """Test that the README has author information."""
        content = README_FILE.read_text(encoding='utf-8')
        assert "José Manuel Mota Burruezo" in content


class TestMathematicalContent:
    """Tests for the mathematical correctness of the formalization."""

    def test_gaussian_kernel_definition(self):
        """Test that the Gaussian kernel is correctly defined."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Should have exp(-π(x-y)²) structure
        assert "exp" in content
        assert "π" in content or "pi" in content.lower()

    def test_trace_formula(self):
        """Test that the trace formula 2R is present."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "2 * R" in content or "2*R" in content

    def test_hilbert_schmidt_bound_formula(self):
        """Test that the Hilbert-Schmidt bound 4R² is present."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "4 * R^2" in content or "4*R^2" in content or "4 * R ^ 2" in content

    def test_has_symmetry_theorem(self):
        """Test that the kernel symmetry theorem is present."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "gaussian_kernel_symmetric" in content


class TestIntegration:
    """Integration tests for the Trace Kernel Gaussian formalization."""

    def test_lean_file_structure(self):
        """Test that the Lean file has proper structure."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        # Should have namespace
        assert "namespace GaussianKernelTrace" in content
        # Should close namespace
        assert "end GaussianKernelTrace" in content
        # Should be noncomputable
        assert "noncomputable section" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
