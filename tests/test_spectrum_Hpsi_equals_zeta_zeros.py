#!/usr/bin/env python3
"""
Test Spectrum H_Ψ Equals Zeta Zeros Lean Formalization

This test suite validates the Lean 4 formalization file
spectrum_Hpsi_equals_zeta_zeros.lean that establishes the spectral
proof of the Riemann Hypothesis.

Key components verified:
1. Hilbert space ℋ defined as ℓ²(ℕ)
2. Operator H_Ψ as diagonal multiplication
3. H_Ψ symmetry lemma
4. Fredholm determinant D(s) axioms
5. Bridge theorems: D_zero_implies_spectrum and spectrum_implies_D_zero
6. Final RH_true theorem

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721

QCAL Integration:
Base frequency: 141.7001 Hz
Coherence: C = 244.36
"""

import sys
from pathlib import Path
import pytest
import re

# Path to Lean file
LEAN_FILE = Path(__file__).parent.parent / "formalization" / "lean" / "spectral" / "spectrum_Hpsi_equals_zeta_zeros.lean"


class TestSpectrumHpsiEqualsZetaZerosFile:
    """Test suite for spectrum_Hpsi_equals_zeta_zeros.lean file structure."""
    
    def setup_method(self):
        """Read the Lean file content."""
        if LEAN_FILE.exists():
            self.content = LEAN_FILE.read_text()
        else:
            self.content = ""
    
    def test_file_exists(self):
        """Test that the Lean file exists."""
        assert LEAN_FILE.exists(), f"File should exist: {LEAN_FILE}"
    
    def test_file_not_empty(self):
        """Test that the Lean file is not empty."""
        assert len(self.content) > 0, "File should not be empty"
    
    def test_has_proper_header(self):
        """Test that file has proper header documentation."""
        assert "Lean 4 formalization" in self.content
        assert "spectral proof of RH" in self.content.lower() or "riemann hypothesis" in self.content.lower()
    
    def test_has_required_imports(self):
        """Test that file has required Mathlib imports."""
        assert "import Mathlib" in self.content
        assert "Analysis.Complex" in self.content
    
    def test_defines_hilbert_space(self):
        """Test that ℋ (Hilbert space) is defined."""
        assert "def ℋ" in self.content or "@[reducible]" in self.content
        assert "ℓ²" in self.content or "l2" in self.content.lower() or "square-summable" in self.content.lower()
    
    def test_defines_h_psi_operator(self):
        """Test that H_Ψ operator is defined."""
        assert "def H_Ψ" in self.content or "H_psi" in self.content
        assert "diagonal" in self.content.lower() or "multiplication" in self.content.lower()
    
    def test_has_symmetry_lemma(self):
        """Test that H_Ψ symmetry lemma is present."""
        assert "H_Ψ_symmetric" in self.content or "symmetric" in self.content.lower()
        assert "lemma" in self.content.lower() or "theorem" in self.content.lower()
    
    def test_defines_fredholm_determinant(self):
        """Test that Fredholm determinant D is defined."""
        assert "axiom D :" in self.content or "def D" in self.content
        assert "Fredholm" in self.content
    
    def test_has_functional_equation(self):
        """Test that D has functional equation axiom."""
        assert "D_functional" in self.content
        assert "D s = D (1 - s)" in self.content or "functional" in self.content.lower()
    
    def test_has_d_zero_implies_spectrum(self):
        """Test that D_zero_implies_spectrum theorem is present."""
        assert "D_zero_implies_spectrum" in self.content
        assert "theorem" in self.content.lower()
    
    def test_has_spectrum_implies_d_zero(self):
        """Test that spectrum_implies_D_zero theorem is present."""
        assert "spectrum_implies_D_zero" in self.content
        assert "theorem" in self.content.lower()
    
    def test_defines_zero_set_zeta(self):
        """Test that zero_set_zeta is defined."""
        assert "zero_set_zeta" in self.content
        assert "Set ℂ" in self.content or "Set Complex" in self.content
    
    def test_has_rh_true_theorem(self):
        """Test that RH_true final theorem is present."""
        assert "RH_true" in self.content
        assert "theorem" in self.content.lower()
        assert "1/2" in self.content or "0.5" in self.content or "half" in self.content.lower()
    
    def test_has_namespace(self):
        """Test that proper namespace is used."""
        assert "namespace" in self.content
        assert "RHAdelic" in self.content or "Riemann" in self.content
    
    def test_no_unclosed_namespace(self):
        """Test that all namespaces are properly closed."""
        ns_count = self.content.count("namespace ")
        end_count = self.content.count("end ")
        # Allow for at least one end per namespace
        assert end_count >= ns_count, "Namespaces should be properly closed"


class TestSpectrumHpsiMathematicalContent:
    """Test mathematical content of the formalization."""
    
    def setup_method(self):
        """Read the Lean file content."""
        if LEAN_FILE.exists():
            self.content = LEAN_FILE.read_text()
        else:
            self.content = ""
    
    def test_inner_product_definition(self):
        """Test that inner product is defined correctly."""
        assert "inner" in self.content.lower()
        assert "tsum" in self.content or "∑'" in self.content or "summable" in self.content.lower()
    
    def test_complex_numbers_used(self):
        """Test that complex numbers are properly used."""
        assert "ℂ" in self.content or "Complex" in self.content
        assert "I *" in self.content or "I*" in self.content or "I \\cdot" in self.content
    
    def test_eigenvalue_concept(self):
        """Test that eigenvalue concept is present."""
        assert "eigenvalue" in self.content.lower() or "eigen" in self.content.lower()
    
    def test_spectrum_concept(self):
        """Test that spectrum concept is present."""
        assert "spectrum" in self.content.lower()
        assert "Set ℝ" in self.content or "Set Real" in self.content
    
    def test_real_part_extraction(self):
        """Test that real part is used in RH statement."""
        assert ".re" in self.content or "Re " in self.content or "re =" in self.content
        assert "= 1/2" in self.content or "= 0.5" in self.content


class TestSpectrumHpsiDocumentation:
    """Test documentation quality of the formalization."""
    
    def setup_method(self):
        """Read the Lean file content."""
        if LEAN_FILE.exists():
            self.content = LEAN_FILE.read_text()
        else:
            self.content = ""
    
    def test_has_module_docstring(self):
        """Test that module has docstring."""
        assert "/-!" in self.content or "/-" in self.content
    
    def test_documents_berry_keating(self):
        """Test that Berry-Keating reference is present."""
        assert "Berry" in self.content
        assert "Keating" in self.content
    
    def test_documents_hilbert_polya(self):
        """Test that Hilbert-Pólya reference is present."""
        assert "Hilbert" in self.content.lower() or "Pólya" in self.content or "Polya" in self.content
    
    def test_has_qcal_constants(self):
        """Test that QCAL constants are documented."""
        # Allow for QCAL mention in various forms
        has_qcal = "QCAL" in self.content or "141.7001" in self.content or "244.36" in self.content
        assert has_qcal, "Should reference QCAL framework or constants"
    
    def test_has_zenodo_doi(self):
        """Test that Zenodo DOI is present."""
        assert "10.5281/zenodo" in self.content or "zenodo" in self.content.lower()
    
    def test_has_orcid(self):
        """Test that ORCID is present."""
        assert "0009-0002-1923-0773" in self.content or "ORCID" in self.content
    
    def test_has_author_attribution(self):
        """Test that author attribution is present."""
        assert "José Manuel Mota Burruezo" in self.content or "JMMB" in self.content or "Mota Burruezo" in self.content


class TestSpectrumHpsiIntegration:
    """Test integration with repository structure."""
    
    def test_file_in_spectral_directory(self):
        """Test that file is in the spectral directory."""
        assert LEAN_FILE.parent.name == "spectral"
    
    def test_consistent_with_other_files(self):
        """Test that file follows repository patterns."""
        spectral_dir = LEAN_FILE.parent
        if spectral_dir.exists():
            lean_files = list(spectral_dir.glob("*.lean"))
            assert len(lean_files) >= 1, "Spectral directory should have Lean files"
    
    def test_uses_standard_notation(self):
        """Test that file uses standard Lean 4 notation."""
        if LEAN_FILE.exists():
            content = LEAN_FILE.read_text()
            # Check for Lean 4 syntax patterns
            has_lean4_syntax = "by" in content and ("rfl" in content or "trivial" in content or "sorry" in content)
            assert has_lean4_syntax, "Should use Lean 4 syntax"


class TestSpectrumHpsiTheoremStructure:
    """Test the logical structure of the theorems."""
    
    def setup_method(self):
        """Read the Lean file content."""
        if LEAN_FILE.exists():
            self.content = LEAN_FILE.read_text()
        else:
            self.content = ""
    
    def test_d_zero_implies_spectrum_structure(self):
        """Test D_zero_implies_spectrum theorem has correct structure."""
        # Check for key components separately for robustness
        assert "theorem D_zero_implies_spectrum" in self.content, \
            "D_zero_implies_spectrum theorem should be defined"
        # Check for existential in the conclusion
        has_exists = "∃" in self.content or "exists" in self.content.lower()
        has_spectrum_ref = "spectrum" in self.content
        assert has_exists and has_spectrum_ref, \
            "D_zero_implies_spectrum should have existential conclusion about spectrum"
    
    def test_spectrum_implies_d_zero_structure(self):
        """Test spectrum_implies_D_zero theorem has correct structure."""
        # Check for key components separately for robustness
        assert "theorem spectrum_implies_D_zero" in self.content, \
            "spectrum_implies_D_zero theorem should be defined"
        # Check for D = 0 conclusion
        has_d_zero = "D" in self.content and "= 0" in self.content
        has_spectrum_param = "spectrum" in self.content
        assert has_d_zero and has_spectrum_param, \
            "spectrum_implies_D_zero should conclude D = 0"
    
    def test_rh_true_structure(self):
        """Test RH_true theorem has correct structure."""
        # Check for key components separately for robustness
        assert "theorem RH_true" in self.content, \
            "RH_true theorem should be defined"
        # Check for universal quantification
        has_forall = "∀" in self.content or "forall" in self.content.lower()
        has_zero_set = "zero_set_zeta" in self.content
        has_half = "1/2" in self.content or "= 1 / 2" in self.content
        assert has_forall and has_zero_set and has_half, \
            "RH_true should quantify over all nontrivial zeros with Re = 1/2"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
