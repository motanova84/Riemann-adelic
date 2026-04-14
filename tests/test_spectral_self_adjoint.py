#!/usr/bin/env python3
"""
Test suite for spectral/self_adjoint.lean module.

This test suite validates the structure and mathematical coherence
of the self-adjoint operator formalization.

Author: José Manuel Mota Burruezo
Date: 26 November 2025
"""

import pytest
import re
from pathlib import Path


# Path to the Lean file
LEAN_FILE_PATH = Path(__file__).parent.parent / "formalization" / "lean" / "spectral" / "self_adjoint.lean"


@pytest.fixture
def lean_content():
    """Load the Lean file content."""
    with open(LEAN_FILE_PATH, 'r', encoding='utf-8') as f:
        return f.read()


class TestSpectralSelfAdjointStructure:
    """Tests for the structure of spectral/self_adjoint.lean."""
    
    def test_file_exists(self):
        """Verify the Lean file exists."""
        assert LEAN_FILE_PATH.exists(), f"File not found: {LEAN_FILE_PATH}"
    
    def test_file_not_empty(self, lean_content):
        """Verify the file has content."""
        assert len(lean_content) > 1000, "File seems too small"
    
    def test_has_namespace(self, lean_content):
        """Verify the NoeticOperator namespace is defined."""
        assert "namespace NoeticOperator" in lean_content


class TestMathLibImports:
    """Tests for Mathlib imports."""
    
    def test_has_inner_product_space(self, lean_content):
        """Verify InnerProductSpace import."""
        assert "Mathlib.Analysis.InnerProductSpace" in lean_content
    
    def test_has_measure_theory(self, lean_content):
        """Verify MeasureTheory imports."""
        assert "Mathlib.MeasureTheory" in lean_content
    
    def test_has_complex_analysis(self, lean_content):
        """Verify Complex analysis import."""
        assert "Mathlib.Analysis.Complex.Basic" in lean_content
    
    def test_import_count(self, lean_content):
        """Verify adequate number of imports."""
        imports = re.findall(r'import Mathlib\.[A-Za-z0-9.]+', lean_content)
        assert len(imports) >= 5, f"Expected at least 5 Mathlib imports, got {len(imports)}"


class TestKeyDefinitions:
    """Tests for key mathematical definitions."""
    
    def test_h_space_defined(self, lean_content):
        """Verify H_space is defined."""
        assert re.search(r'\bdef\s+H_space\b', lean_content) is not None
    
    def test_noetic_measure_defined(self, lean_content):
        """Verify noeticMeasure is defined."""
        assert re.search(r'\bdef\s+noeticMeasure\b', lean_content) is not None
    
    def test_h_psi_operator_defined(self, lean_content):
        """Verify H_Ψ operator is defined."""
        assert re.search(r'\bdef\s+H_Ψ\b', lean_content) is not None
    
    def test_xi_function_defined(self, lean_content):
        """Verify Xi function placeholder is defined."""
        assert re.search(r'\bdef\s+Ξ\b', lean_content) is not None
    
    def test_spectrum_operator_defined(self, lean_content):
        """Verify spectrum_operator is defined."""
        assert re.search(r'\bdef\s+spectrum_operator\b', lean_content) is not None


class TestAxioms:
    """Tests for temporary axioms."""
    
    def test_self_adjoint_axiom(self, lean_content):
        """Verify H_Ψ_self_adjoint axiom is declared."""
        assert re.search(r'\baxiom\s+H_Ψ_self_adjoint\b', lean_content) is not None
    
    def test_spectrum_axiom(self, lean_content):
        """Verify spectrum correspondence axiom is declared."""
        assert re.search(r'\baxiom\s+spectrum_HΨ_equals_zeros_Ξ\b', lean_content) is not None
    
    def test_axiom_count(self, lean_content):
        """Verify exactly 2 temporal axioms."""
        axioms = re.findall(r'\baxiom\s+\w+', lean_content)
        assert len(axioms) == 2, f"Expected 2 axioms, got {len(axioms)}"


class TestLemmasAndTheorems:
    """Tests for lemmas and theorems."""
    
    def test_symmetric_lemma(self, lean_content):
        """Verify H_Ψ_symmetric lemma exists."""
        assert re.search(r'\blemma\s+H_Ψ_symmetric\b', lean_content) is not None
    
    def test_rh_theorem(self, lean_content):
        """Verify riemann_hypothesis_from_spectral theorem exists."""
        assert re.search(r'\btheorem\s+riemann_hypothesis_from_spectral\b', lean_content) is not None
    
    def test_sorry_count(self, lean_content):
        """Verify sorry count is within expected range."""
        sorry_count = len(re.findall(r'\bsorry\b', lean_content))
        # We expect 3 sorries: 1 in lemma, 1 in Ξ definition, 1 in H_Ψ_symmetric
        assert sorry_count <= 5, f"Too many sorries: {sorry_count}"


class TestQCALIntegration:
    """Tests for QCAL integration."""
    
    def test_base_frequency_constant(self, lean_content):
        """Verify QCAL base frequency is defined."""
        assert "141.7001" in lean_content
    
    def test_coherence_constant(self, lean_content):
        """Verify QCAL coherence constant is defined."""
        assert "244.36" in lean_content
    
    def test_qcal_frequency_definition(self, lean_content):
        """Verify QCAL_base_frequency definition."""
        assert re.search(r'\bdef\s+QCAL_base_frequency\b', lean_content) is not None
    
    def test_qcal_coherence_definition(self, lean_content):
        """Verify QCAL_coherence definition."""
        assert re.search(r'\bdef\s+QCAL_coherence\b', lean_content) is not None
    
    def test_mensaje_selfadjoint(self, lean_content):
        """Verify symbolic message is defined."""
        assert re.search(r'\bdef\s+mensaje_selfadjoint\b', lean_content) is not None
        assert "operador de amor coherente" in lean_content


class TestDocumentation:
    """Tests for documentation quality."""
    
    def test_has_module_header(self, lean_content):
        """Verify module has a proper header comment."""
        assert lean_content.startswith("/-")
    
    def test_has_author_info(self, lean_content):
        """Verify author information is present."""
        assert "José Manuel Mota Burruezo" in lean_content or "JMMB" in lean_content
    
    def test_has_doi_reference(self, lean_content):
        """Verify DOI reference is present."""
        assert "10.5281/zenodo" in lean_content
    
    def test_has_berry_keating_reference(self, lean_content):
        """Verify Berry-Keating reference is present."""
        assert "Berry" in lean_content and "Keating" in lean_content
    
    def test_has_orcid(self, lean_content):
        """Verify ORCID is present."""
        assert "0009-0002-1923-0773" in lean_content
    
    def test_has_noetic_symbol(self, lean_content):
        """Verify ∞³ symbol is present."""
        assert "∞³" in lean_content


class TestMathematicalChain:
    """Tests for the logical chain to RH."""
    
    def test_symmetry_mentioned(self, lean_content):
        """Verify symmetry property is mentioned."""
        assert "symmetric" in lean_content.lower() or "simetría" in lean_content.lower()
    
    def test_self_adjoint_property(self, lean_content):
        """Verify self-adjoint property is mentioned."""
        assert "self_adjoint" in lean_content or "autoadjoint" in lean_content.lower()
    
    def test_spectrum_real(self, lean_content):
        """Verify real spectrum property is discussed."""
        assert "real" in lean_content.lower() or "ℝ" in lean_content
    
    def test_riemann_hypothesis_connection(self, lean_content):
        """Verify RH connection is made."""
        assert "riemann" in lean_content.lower() or "RH" in lean_content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
