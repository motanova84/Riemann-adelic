#!/usr/bin/env python3
"""
Test suite for Hilbert-Pólya Formal Closure components.

This module tests the documentation, Lean formalization, and Streamlit
visualization components of the Hilbert-Pólya conjecture closure.

Author: José Manuel Mota Burruezo
Date: November 28, 2025
Version: 1.0
"""

import pytest
import re
from pathlib import Path


# Path constants
REPO_ROOT = Path(__file__).parent.parent
DOCS_DIR = REPO_ROOT / "docs" / "operators"
LEAN_DIR = REPO_ROOT / "formalization" / "lean" / "RiemannAdelic"
STREAMLIT_DIR = REPO_ROOT / "streamlit_app"
WORKFLOW_DIR = REPO_ROOT / ".github" / "workflows"


class TestDocumentation:
    """Tests for the hilbert_polyafinal.md documentation."""

    def test_docs_operators_directory_exists(self):
        """Test that docs/operators directory exists."""
        assert DOCS_DIR.exists(), f"Directory not found: {DOCS_DIR}"

    def test_hilbert_polyafinal_exists(self):
        """Test that hilbert_polyafinal.md exists."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        assert filepath.exists(), f"File not found: {filepath}"

    def test_hilbert_polyafinal_not_empty(self):
        """Test that the documentation file is not empty."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        assert filepath.stat().st_size > 0, "Documentation file is empty"

    def test_has_required_sections(self):
        """Test that the documentation has all required sections."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        
        required_sections = [
            "Firma Matemática",
            "Resumen Ejecutivo",
            "El Operador H_Ψ",
            "Confirmaciones Activas",
            "Propiedades Espectrales",
            "Formalización Lean 4",
            "Validación Numérica",
            "Referencias",
        ]
        
        for section in required_sections:
            assert section in content, f"Missing section: {section}"

    def test_has_zenodo_doi(self):
        """Test that the documentation references the Zenodo DOI."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        assert "10.5281/zenodo" in content, "Zenodo DOI reference missing"

    def test_has_qcal_coherence_values(self):
        """Test that QCAL coherence values are present."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        assert "244.36" in content, "QCAL coherence value C=244.36 missing"
        assert "141.7001" in content, "QCAL frequency f₀=141.7001 missing"

    def test_has_berry_keating_reference(self):
        """Test that Berry & Keating is referenced."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        assert "Berry" in content and "Keating" in content

    def test_has_author_info(self):
        """Test that author information is present."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        assert "José Manuel Mota Burruezo" in content or "JMMB" in content

    def test_has_latex_formulas(self):
        """Test that the documentation contains LaTeX formulas."""
        filepath = DOCS_DIR / "hilbert_polyafinal.md"
        content = filepath.read_text(encoding='utf-8')
        # Check for LaTeX math delimiters
        assert "$$" in content or "$" in content or "\\[" in content


class TestLeanFormalization:
    """Tests for the HilbertPolyaValidation.lean file."""

    def test_lean_file_exists(self):
        """Test that HilbertPolyaValidation.lean exists."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        assert filepath.exists(), f"File not found: {filepath}"

    def test_lean_file_not_empty(self):
        """Test that the Lean file is not empty."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        assert filepath.stat().st_size > 0, "Lean file is empty"

    def test_has_proper_header(self):
        """Test that the Lean file has proper documentation header."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "Hilbert-Pólya" in content or "Hilbert-Polya" in content
        assert "José Manuel Mota Burruezo" in content

    def test_has_mathlib_imports(self):
        """Test that the file imports required Mathlib modules."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        
        required_imports = [
            "Mathlib.Analysis",
            "Mathlib.MeasureTheory",
        ]
        
        for imp in required_imports:
            assert imp in content, f"Missing import: {imp}"

    def test_defines_h_psi(self):
        """Test that H_psi operator is defined."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "def H_psi" in content or "H_psi" in content

    def test_defines_is_eigenvalue(self):
        """Test that isEigenvalue is defined."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "isEigenvalue" in content or "is_eigenvalue" in content

    def test_has_main_theorem(self):
        """Test that the main theorem is stated."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "riemann_hypothesis" in content.lower()

    def test_has_hermitian_property(self):
        """Test that hermitian property is addressed."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "hermitian" in content.lower() or "autoadjunto" in content.lower()

    def test_has_pt_symmetry(self):
        """Test that PT symmetry is addressed."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "PT" in content or "parity" in content.lower()

    def test_has_qcal_constants(self):
        """Test that QCAL constants are defined."""
        filepath = LEAN_DIR / "HilbertPolyaValidation.lean"
        content = filepath.read_text(encoding='utf-8')
        assert "244.36" in content, "QCAL coherence constant missing"
        assert "141.7001" in content, "QCAL frequency constant missing"


class TestStreamlitApp:
    """Tests for the streamlit_app/hilbert.py file."""

    def test_streamlit_dir_exists(self):
        """Test that streamlit_app directory exists."""
        assert STREAMLIT_DIR.exists(), f"Directory not found: {STREAMLIT_DIR}"

    def test_hilbert_py_exists(self):
        """Test that hilbert.py exists."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        assert filepath.exists(), f"File not found: {filepath}"

    def test_hilbert_py_not_empty(self):
        """Test that hilbert.py is not empty."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        assert filepath.stat().st_size > 0, "hilbert.py is empty"

    def test_has_streamlit_import(self):
        """Test that streamlit is imported."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        assert "import streamlit" in content

    def test_has_main_function(self):
        """Test that main function exists."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        assert "def main" in content

    def test_has_visualization_functions(self):
        """Test that visualization functions exist."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        
        expected_functions = [
            "plot_eigenvalues",
            "plot_spectral_staircase",
            "plot_pt_symmetry",
        ]
        
        for func in expected_functions:
            assert func in content, f"Missing function: {func}"

    def test_has_h_psi_kernel(self):
        """Test that H_psi kernel function exists."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        assert "h_psi_kernel" in content or "H_psi" in content

    def test_has_qcal_constants(self):
        """Test that QCAL constants are defined."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        assert "QCAL_C" in content or "244.36" in content
        assert "QCAL_F0" in content or "141.7001" in content

    def test_syntax_valid(self):
        """Test that Python syntax is valid."""
        filepath = STREAMLIT_DIR / "hilbert.py"
        content = filepath.read_text(encoding='utf-8')
        try:
            compile(content, str(filepath), 'exec')
        except SyntaxError as e:
            pytest.fail(f"Syntax error in hilbert.py: {e}")


class TestWorkflow:
    """Tests for the CI workflow file."""

    def test_workflow_exists(self):
        """Test that the workflow file exists."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        assert filepath.exists(), f"Workflow file not found: {filepath}"

    def test_workflow_not_empty(self):
        """Test that the workflow file is not empty."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        assert filepath.stat().st_size > 0, "Workflow file is empty"

    def test_workflow_has_name(self):
        """Test that workflow has a name."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        content = filepath.read_text(encoding='utf-8')
        assert "name:" in content

    def test_workflow_has_jobs(self):
        """Test that workflow defines jobs."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        content = filepath.read_text(encoding='utf-8')
        assert "jobs:" in content

    def test_workflow_validates_documentation(self):
        """Test that workflow validates documentation."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        content = filepath.read_text(encoding='utf-8')
        assert "hilbert_polyafinal.md" in content

    def test_workflow_validates_lean(self):
        """Test that workflow validates Lean formalization."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        content = filepath.read_text(encoding='utf-8')
        assert "HilbertPolyaValidation.lean" in content or "lean" in content.lower()

    def test_workflow_validates_python(self):
        """Test that workflow validates Python components."""
        filepath = WORKFLOW_DIR / "test-hilbert-polya.yml"
        content = filepath.read_text(encoding='utf-8')
        assert "hilbert.py" in content or "python" in content.lower()


class TestIntegration:
    """Integration tests for all components."""

    def test_all_files_exist(self):
        """Test that all required files exist."""
        required_files = [
            DOCS_DIR / "hilbert_polyafinal.md",
            LEAN_DIR / "HilbertPolyaValidation.lean",
            STREAMLIT_DIR / "hilbert.py",
            WORKFLOW_DIR / "test-hilbert-polya.yml",
        ]
        
        for filepath in required_files:
            assert filepath.exists(), f"File not found: {filepath}"

    def test_consistent_qcal_values(self):
        """Test that QCAL values are consistent across files."""
        files_to_check = [
            DOCS_DIR / "hilbert_polyafinal.md",
            LEAN_DIR / "HilbertPolyaValidation.lean",
            STREAMLIT_DIR / "hilbert.py",
        ]
        
        qcal_c = "244.36"
        qcal_f0 = "141.7001"
        
        for filepath in files_to_check:
            content = filepath.read_text(encoding='utf-8')
            assert qcal_c in content, f"QCAL C value missing in {filepath.name}"
            assert qcal_f0 in content, f"QCAL f₀ value missing in {filepath.name}"

    def test_consistent_doi_reference(self):
        """Test that DOI is consistently referenced."""
        files_to_check = [
            DOCS_DIR / "hilbert_polyafinal.md",
            LEAN_DIR / "HilbertPolyaValidation.lean",
            STREAMLIT_DIR / "hilbert.py",
        ]
        
        doi = "10.5281/zenodo"
        
        for filepath in files_to_check:
            content = filepath.read_text(encoding='utf-8')
            assert doi in content, f"DOI reference missing in {filepath.name}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
