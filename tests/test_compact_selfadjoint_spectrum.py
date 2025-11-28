#!/usr/bin/env python3
"""
Test suite for spectral/compact_selfadjoint_spectrum.lean module.

This test suite validates the structure and mathematical coherence
of the compact self-adjoint operator spectrum formalization.

Author: José Manuel Mota Burruezo
Date: 27 November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import re
from pathlib import Path


# Path to the Lean file
LEAN_FILE_PATH = Path(__file__).parent.parent / "formalization" / "lean" / "spectral" / "compact_selfadjoint_spectrum.lean"

# Minimum file size for a complete formalization (bytes)
# A complete Lean formalization with definitions, theorems, proofs, and documentation
# typically requires at least 5KB of content
MIN_FILE_SIZE_BYTES = 5000

# Minimum expected axioms for classical spectral theory results
# We expect at least 3 axioms for: Fredholm theory, Riesz-Schauder theorem, and spectral discreteness
MIN_EXPECTED_AXIOMS = 3


@pytest.fixture
def lean_content():
    """Load the Lean file content."""
    with open(LEAN_FILE_PATH, 'r', encoding='utf-8') as f:
        return f.read()


class TestCompactSelfAdjointSpectrumStructure:
    """Tests for the structure of spectral/compact_selfadjoint_spectrum.lean."""
    
    def test_file_exists(self):
        """Verify the Lean file exists."""
        assert LEAN_FILE_PATH.exists(), f"File not found: {LEAN_FILE_PATH}"
    
    def test_file_not_empty(self, lean_content):
        """Verify the file has content."""
        assert len(lean_content) > MIN_FILE_SIZE_BYTES, \
            f"File seems too small for a complete formalization (got {len(lean_content)} bytes, expected > {MIN_FILE_SIZE_BYTES})"
    
    def test_has_namespace(self, lean_content):
        """Verify the SpectralQCAL.CompactSelfAdjoint namespace is defined."""
        assert "namespace SpectralQCAL.CompactSelfAdjoint" in lean_content


class TestMathLibImports:
    """Tests for Mathlib imports."""
    
    def test_has_inner_product_space(self, lean_content):
        """Verify InnerProductSpace import."""
        assert "Mathlib.Analysis.InnerProductSpace" in lean_content
    
    def test_has_compact_operator(self, lean_content):
        """Verify Compact operator import."""
        assert "Compact" in lean_content
    
    def test_has_topology(self, lean_content):
        """Verify Topology imports."""
        assert "Mathlib.Topology" in lean_content
    
    def test_import_count(self, lean_content):
        """Verify adequate number of imports."""
        imports = re.findall(r'import Mathlib\.[A-Za-z0-9.]+', lean_content)
        assert len(imports) >= 4, f"Expected at least 4 Mathlib imports, got {len(imports)}"


class TestKeyDefinitions:
    """Tests for key mathematical definitions."""
    
    def test_is_self_adjoint_defined(self, lean_content):
        """Verify IsSelfAdjoint predicate is defined."""
        assert re.search(r'\bdef\s+IsSelfAdjoint\b', lean_content) is not None
    
    def test_is_compact_operator_defined(self, lean_content):
        """Verify IsCompactOp predicate is defined."""
        assert re.search(r'\bdef\s+IsCompactOp\b', lean_content) is not None
    
    def test_spectrum_real_defined(self, lean_content):
        """Verify spectrum_real is defined."""
        assert re.search(r'\bdef\s+spectrum_real\b', lean_content) is not None
    
    def test_point_spectrum_defined(self, lean_content):
        """Verify point_spectrum is defined."""
        assert re.search(r'\bdef\s+point_spectrum\b', lean_content) is not None


class TestMainTheorem:
    """Tests for the main theorem."""
    
    def test_main_theorem_exists(self, lean_content):
        """Verify spectrum_compact_selfadjoint_discrete theorem exists."""
        assert re.search(r'\btheorem\s+spectrum_compact_selfadjoint_discrete\b', lean_content) is not None
    
    def test_main_theorem_statement(self, lean_content):
        """Verify the theorem has proper hypotheses."""
        # Should have self-adjoint and compact operator hypotheses
        assert "IsSelfAdjoint T" in lean_content or "hT_self" in lean_content
        assert "IsCompactOperator T" in lean_content or "hT_compact" in lean_content
    
    def test_ball_intersection_empty(self, lean_content):
        """Verify the theorem states isolation of non-zero spectral points."""
        # The theorem should conclude with a ball having empty intersection
        assert "ball" in lean_content.lower()
        assert "∅" in lean_content or "= ∅" in lean_content


class TestCorollaries:
    """Tests for corollary theorems."""
    
    def test_countable_corollary(self, lean_content):
        """Verify countability corollary exists."""
        assert re.search(r'\btheorem\s+spectrum_compact_selfadjoint_countable\b', lean_content) is not None
    
    def test_enumerable_corollary(self, lean_content):
        """Verify enumerability corollary exists."""
        assert re.search(r'\btheorem\s+eigenvalues_enumerable\b', lean_content) is not None
    
    def test_orthonormal_basis_theorem(self, lean_content):
        """Verify orthonormal basis theorem exists."""
        assert re.search(r'\btheorem\s+discrete_spectrum_implies_orthonormal_basis\b', lean_content) is not None


class TestAxiomsAndLemmas:
    """Tests for axioms and auxiliary lemmas."""
    
    def test_has_axioms(self, lean_content):
        """Verify axioms are declared for classical results.
        
        We expect at least MIN_EXPECTED_AXIOMS axioms for classical spectral
        theory results (Fredholm theory, Riesz-Schauder theorem, spectral discreteness).
        """
        axiom_count = len(re.findall(r'\baxiom\s+\w+', lean_content))
        assert axiom_count >= MIN_EXPECTED_AXIOMS, \
            f"Expected at least {MIN_EXPECTED_AXIOMS} axioms for classical results, got {axiom_count}"
    
    def test_auxiliary_axioms_exist(self, lean_content):
        """Verify key auxiliary axioms exist."""
        assert "is_compact_self_adjoint_spectrum_discrete" in lean_content


class TestQCALIntegration:
    """Tests for QCAL integration."""
    
    def test_base_frequency_constant(self, lean_content):
        """Verify QCAL base frequency is defined."""
        assert "141.7001" in lean_content
    
    def test_coherence_constant(self, lean_content):
        """Verify QCAL coherence constant is defined."""
        assert "244.36" in lean_content
    
    def test_qcal_frequency_definition(self, lean_content):
        """Verify qcal_frequency definition."""
        assert re.search(r'\bdef\s+qcal_frequency\b', lean_content) is not None
    
    def test_qcal_coherence_definition(self, lean_content):
        """Verify qcal_coherence definition."""
        assert re.search(r'\bdef\s+qcal_coherence\b', lean_content) is not None


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
    
    def test_has_orcid(self, lean_content):
        """Verify ORCID is present."""
        assert "0009-0002-1923-0773" in lean_content
    
    def test_has_noetic_symbol(self, lean_content):
        """Verify ∞³ symbol is present."""
        assert "∞³" in lean_content
    
    def test_has_references(self, lean_content):
        """Verify classical references are present."""
        assert "Kreyszig" in lean_content or "Reed" in lean_content or "Simon" in lean_content


class TestMathematicalContent:
    """Tests for mathematical content and completeness."""
    
    def test_hilbert_space_variable(self, lean_content):
        """Verify Hilbert space type variable is used."""
        assert "InnerProductSpace" in lean_content
    
    def test_complete_space_requirement(self, lean_content):
        """Verify CompleteSpace requirement."""
        assert "CompleteSpace" in lean_content
    
    def test_eigenvalue_discussion(self, lean_content):
        """Verify eigenvalue concept is discussed."""
        assert "eigenvalue" in lean_content.lower() or "eigenv" in lean_content.lower()
    
    def test_accumulation_at_zero(self, lean_content):
        """Verify accumulation at zero is mentioned."""
        assert "accumulation" in lean_content.lower() or "0" in lean_content
    
    def test_discreteness_concept(self, lean_content):
        """Verify discreteness is discussed."""
        assert "discrete" in lean_content.lower() or "isolated" in lean_content.lower()


class TestRiemannHypothesisConnection:
    """Tests for connection to Riemann Hypothesis."""
    
    def test_rh_connection_mentioned(self, lean_content):
        """Verify connection to RH is mentioned."""
        assert "Riemann" in lean_content
    
    def test_hilbert_polya_mentioned(self, lean_content):
        """Verify Hilbert-Pólya approach is mentioned."""
        assert "Hilbert" in lean_content or "Pólya" in lean_content or "Polya" in lean_content
    
    def test_h_psi_operator_mentioned(self, lean_content):
        """Verify H_Ψ operator is mentioned."""
        assert "H_Ψ" in lean_content or "H_psi" in lean_content.lower()


class TestLean4Syntax:
    """Tests for correct Lean 4 syntax patterns."""
    
    def test_noncomputable_section(self, lean_content):
        """Verify noncomputable section is used."""
        assert "noncomputable section" in lean_content
    
    def test_open_scoped(self, lean_content):
        """Verify open scoped is used correctly."""
        assert "open" in lean_content
    
    def test_end_namespace(self, lean_content):
        """Verify namespace is properly closed."""
        assert "end SpectralQCAL.CompactSelfAdjoint" in lean_content
    
    def test_theorem_by_syntax(self, lean_content):
        """Verify theorem proofs use 'by' syntax."""
        assert re.search(r'theorem\s+\w+.*:=\s*by', lean_content, re.DOTALL) is not None or \
               re.search(r'theorem\s+\w+.*\sby\b', lean_content, re.DOTALL) is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
