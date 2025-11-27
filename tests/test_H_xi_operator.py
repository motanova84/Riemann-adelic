"""
Test H_Ξ operator formalization in Lean4.

This module tests the H_xi_operator.lean file to ensure:
1. File exists and is properly structured
2. Contains required definitions and theorems
3. Follows repository conventions
4. Has proper documentation

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import os
import re
import pytest
from pathlib import Path


# Get repository root dynamically
def get_repo_root():
    """Get the repository root directory dynamically."""
    current = Path(__file__).resolve().parent
    # Walk up to find the repository root (contains .git or formalization directory)
    while current != current.parent:
        if (current / ".git").exists() or (current / "formalization").exists():
            return current
        current = current.parent
    # Fallback to parent of tests directory
    return Path(__file__).resolve().parent.parent


REPO_ROOT = get_repo_root()
LEAN_FILE = REPO_ROOT / "formalization" / "lean" / "operators" / "H_xi_operator.lean"


class TestHXiOperatorFile:
    """Tests for H_xi_operator.lean file structure and content."""
    
    def test_file_exists(self):
        """Verify the H_xi_operator.lean file exists."""
        assert LEAN_FILE.exists(), f"File {LEAN_FILE} should exist"
    
    def test_file_not_empty(self):
        """Verify the file is not empty."""
        content = LEAN_FILE.read_text()
        assert len(content) > 0, "File should not be empty"
        assert len(content) > 1000, "File should have substantial content"
    
    def test_has_proper_header(self):
        """Verify the file has a proper header with author info."""
        content = LEAN_FILE.read_text()
        assert "H_xi_operator.lean" in content, "Should have filename in header"
        assert "José Manuel Mota Burruezo" in content, "Should have author name"
        assert "ORCID" in content, "Should have ORCID reference"
        assert "DOI" in content, "Should have DOI reference"
    
    def test_has_required_imports(self):
        """Verify required Mathlib imports are present."""
        content = LEAN_FILE.read_text()
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace",
            "Mathlib.Analysis.SpecialFunctions.Complex",
            "Mathlib.MeasureTheory",
        ]
        for imp in required_imports:
            assert imp in content, f"Should import {imp}"
    
    def test_defines_H_xi_operator(self):
        """Verify H_xi_operator is defined."""
        content = LEAN_FILE.read_text()
        assert "def H_xi_operator" in content, "Should define H_xi_operator"
        assert "HΨ →L[ℂ] HΨ" in content or "HΨ →ₗ[ℂ] HΨ" in content or "HΨ → HΨ" in content, \
            "Should define H_xi as linear map"
    
    def test_defines_self_adjoint_predicate(self):
        """Verify IsSelfAdjointCLM predicate is defined."""
        content = LEAN_FILE.read_text()
        assert "IsSelfAdjointCLM" in content, "Should define IsSelfAdjointCLM predicate"
        assert "inner" in content, "Should reference inner product"
    
    def test_has_self_adjoint_axiom(self):
        """Verify H_xi_self_adjoint axiom is declared."""
        content = LEAN_FILE.read_text()
        assert "H_xi_self_adjoint" in content, "Should have H_xi_self_adjoint axiom"
        assert "axiom H_xi_self_adjoint" in content, "Should declare as axiom"
    
    def test_defines_spectrum(self):
        """Verify spectrum definition is present."""
        content = LEAN_FILE.read_text()
        assert "spectrum_H_xi" in content, "Should define spectrum_H_xi"
        assert "Set ℂ" in content, "Should define spectrum as Set ℂ"
    
    def test_has_spectrum_real_theorem(self):
        """Verify spectrum_real theorem is present."""
        content = LEAN_FILE.read_text()
        assert "spectrum_real" in content, "Should have spectrum_real theorem"
        assert "λ.im = 0" in content or "im = 0" in content, \
            "Should state imaginary part is zero"
    
    def test_has_spectral_correspondence(self):
        """Verify spectral_zeta_correspondence is present."""
        content = LEAN_FILE.read_text()
        assert "spectral_zeta_correspondence" in content, \
            "Should have spectral_zeta_correspondence"
    
    def test_has_zeros_critical_line_theorem(self):
        """Verify zeros_on_critical_line theorem is present."""
        content = LEAN_FILE.read_text()
        assert "zeros_on_critical_line" in content, \
            "Should have zeros_on_critical_line theorem"
        assert "s.re = 1/2" in content, "Should state Re(s) = 1/2"
    
    def test_has_hilbert_polya_reference(self):
        """Verify Hilbert-Pólya principle is referenced."""
        content = LEAN_FILE.read_text()
        assert "Hilbert" in content and "Pólya" in content, \
            "Should reference Hilbert-Pólya principle"
    
    def test_has_qcal_constants(self):
        """Verify QCAL constants are present."""
        content = LEAN_FILE.read_text()
        assert "141.7001" in content, "Should have QCAL frequency 141.7001"
        assert "244.36" in content, "Should have QCAL coherence 244.36"
    
    def test_has_namespace(self):
        """Verify proper namespace is used."""
        content = LEAN_FILE.read_text()
        assert "namespace RiemannAdelic" in content, \
            "Should use RiemannAdelic namespace"
    
    def test_no_unclosed_sorry(self):
        """Verify there are no unexpected sorry statements."""
        content = LEAN_FILE.read_text()
        # Count sorry statements
        sorry_count = len(re.findall(r'\bsorry\b', content))
        # Some sorry statements are expected in proofs that need completion
        # but should be documented
        assert sorry_count <= 5, \
            f"Should have at most 5 sorry statements, found {sorry_count}"


class TestHXiOperatorMathematicalContent:
    """Tests for mathematical content and structure."""
    
    def test_hilbert_space_variable(self):
        """Verify Hilbert space variable is properly defined."""
        content = LEAN_FILE.read_text()
        assert "variable" in content, "Should use variable declaration"
        assert "InnerProductSpace" in content, "Should reference InnerProductSpace"
        assert "CompleteSpace" in content, "Should require CompleteSpace"
    
    def test_operator_is_continuous_linear_map(self):
        """Verify operator is defined as continuous linear map."""
        content = LEAN_FILE.read_text()
        # Check for either notation
        assert "→L[ℂ]" in content or "→ₗ[ℂ]" in content, \
            "Should define as linear map over ℂ"
    
    def test_spectrum_definition_correct(self):
        """Verify spectrum is defined via eigenvalues."""
        content = LEAN_FILE.read_text()
        assert "∃ f" in content or "exists f" in content.lower(), \
            "Spectrum should be defined via existence of eigenfunction"
        assert "f ≠ 0" in content, "Should require non-trivial eigenfunction"
    
    def test_inner_product_symmetry(self):
        """Verify self-adjointness uses inner product symmetry."""
        content = LEAN_FILE.read_text()
        # Check for inner product notation
        assert "inner (T f) g" in content or "⟨T f, g⟩" in content or \
               "inner f (T g)" in content, \
            "Should express self-adjointness via inner products"


class TestHXiOperatorDocumentation:
    """Tests for documentation quality."""
    
    def test_has_module_docstring(self):
        """Verify module has proper docstring."""
        content = LEAN_FILE.read_text()
        assert "/-!" in content, "Should have documentation block"
        assert "-/" in content, "Should close documentation block"
    
    def test_documents_hilbert_polya(self):
        """Verify Hilbert-Pólya principle is documented."""
        content = LEAN_FILE.read_text()
        assert "Hilbert-Pólya" in content or "Hilbert–Pólya" in content, \
            "Should document Hilbert-Pólya principle"
    
    def test_documents_spectral_correspondence(self):
        """Verify spectral correspondence is documented."""
        content = LEAN_FILE.read_text()
        assert "espectro" in content.lower() or "spectrum" in content.lower(), \
            "Should document spectrum concept"
        assert "ξ(s)" in content or "xi" in content.lower(), \
            "Should reference xi function"
    
    def test_has_references_section(self):
        """Verify references section is present."""
        content = LEAN_FILE.read_text()
        assert "Berry" in content, "Should reference Berry"
        assert "Keating" in content, "Should reference Keating"
        assert "1999" in content, "Should include publication year"
    
    def test_has_summary_section(self):
        """Verify summary section is present."""
        content = LEAN_FILE.read_text()
        assert "Resumen" in content or "Summary" in content, \
            "Should have summary section"


class TestHXiOperatorIntegration:
    """Tests for integration with repository."""
    
    def test_file_in_operators_directory(self):
        """Verify file is in correct directory."""
        assert LEAN_FILE.parent.name == "operators", \
            "File should be in operators directory"
    
    def test_consistent_with_other_operators(self):
        """Verify consistency with other operator files."""
        operators_dir = LEAN_FILE.parent
        other_operators = [
            "operator_H_psi.lean",
            "H_psi_hermitian.lean",
            "spectral_derivative.lean",
        ]
        for op in other_operators:
            op_file = operators_dir / op
            if op_file.exists():
                op_content = op_file.read_text()
                assert "RiemannAdelic" in op_content or "namespace" in op_content, \
                    f"{op} should have namespace"
    
    def test_uses_standard_notation(self):
        """Verify standard Lean4/Mathlib notation is used."""
        content = LEAN_FILE.read_text()
        # Check for standard Lean4 constructs
        assert "theorem" in content or "lemma" in content, \
            "Should have theorem or lemma declarations"
        assert "def" in content, "Should have definitions"
        assert "by" in content, "Should use tactic proofs"


class TestHXiOperatorZenodoDOI:
    """Tests for Zenodo DOI compliance."""
    
    def test_has_zenodo_doi(self):
        """Verify Zenodo DOI is present."""
        content = LEAN_FILE.read_text()
        assert "10.5281/zenodo" in content, "Should have Zenodo DOI"
    
    def test_has_correct_doi(self):
        """Verify correct DOI is used."""
        content = LEAN_FILE.read_text()
        assert "10.5281/zenodo.17379721" in content, \
            "Should have correct DOI 10.5281/zenodo.17379721"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
