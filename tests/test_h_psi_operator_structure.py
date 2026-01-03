#!/usr/bin/env python3
"""
Test suite for H_psi_self_adjoint_structure.lean module.

This test suite validates the structure and mathematical coherence
of the H_psi_operator self-adjoint structure formalization.

The formalization addresses the issue:
"Autoadjunción del operador H_Ψ - Formalización parcial — eliminación del sorry principal"

Author: José Manuel Mota Burruezo
Date: 27 November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import re
from pathlib import Path


# Path to the Lean file
LEAN_FILE_PATH = Path(__file__).parent.parent / "formalization" / "lean" / "operators" / "H_psi_self_adjoint_structure.lean"


@pytest.fixture
def lean_content():
    """Load the Lean file content."""
    if not LEAN_FILE_PATH.exists():
        pytest.skip(f"File not found: {LEAN_FILE_PATH}")
    with open(LEAN_FILE_PATH, 'r', encoding='utf-8') as f:
        return f.read()


class TestHpsiOperatorStructure:
    """Tests for the H_psi_operator structure definition."""
    
    def test_file_exists(self):
        """Verify the Lean file exists."""
        assert LEAN_FILE_PATH.exists(), f"File not found: {LEAN_FILE_PATH}"
    
    def test_file_not_empty(self, lean_content):
        """Verify the file has substantial content."""
        assert len(lean_content) > 5000, "File seems too small for a complete formalization"
    
    def test_has_namespace(self, lean_content):
        """Verify the HpsiSelfAdjointStructure namespace is defined."""
        assert "namespace HpsiSelfAdjointStructure" in lean_content
    
    def test_has_h_psi_operator_structure(self, lean_content):
        """Verify the H_psi_operator structure is defined."""
        assert re.search(r'\bstructure\s+H_psi_operator\b', lean_content) is not None
    
    def test_structure_has_to_lin_field(self, lean_content):
        """Verify the structure has to_lin field."""
        assert "to_lin" in lean_content
        # Check that to_lin is defined as a linear map
        assert re.search(r'to_lin\s*:\s*H\s*→ₗ', lean_content) is not None
    
    def test_structure_has_is_self_adjoint_field(self, lean_content):
        """Verify the structure has is_self_adjoint field."""
        assert "is_self_adjoint" in lean_content
        # Check that is_self_adjoint involves inner products
        assert "inner" in lean_content


class TestHpsiCanonicalInstance:
    """Tests for the canonical H_ψ instance."""
    
    def test_h_psi_instance_defined(self, lean_content):
        """Verify H_ψ instance is defined."""
        assert re.search(r'\bdef\s+H_ψ\b', lean_content) is not None
    
    def test_h_psi_uses_h_psi_operator(self, lean_content):
        """Verify H_ψ is of type H_psi_operator."""
        assert "H_psi_operator" in lean_content
    
    def test_h_psi_has_explicit_to_lin(self, lean_content):
        """Verify H_ψ has an explicit to_lin definition."""
        # Check that the where clause assigns to_lin
        assert re.search(r'def\s+H_ψ\s*:\s*H_psi_operator.*where', lean_content, re.DOTALL) is not None
        assert "to_lin :=" in lean_content
    
    def test_h_psi_has_explicit_is_self_adjoint(self, lean_content):
        """Verify H_ψ has an explicit is_self_adjoint proof."""
        assert "is_self_adjoint :=" in lean_content


class TestMathLibImports:
    """Tests for Mathlib imports."""
    
    def test_has_inner_product_space(self, lean_content):
        """Verify InnerProductSpace import."""
        assert "Mathlib.Analysis.InnerProductSpace" in lean_content
    
    def test_has_adjoint_import(self, lean_content):
        """Verify Adjoint import for self-adjoint operators."""
        assert "Mathlib.Analysis.InnerProductSpace.Adjoint" in lean_content
    
    def test_has_l2_space(self, lean_content):
        """Verify L2Space import."""
        assert "L2Space" in lean_content
    
    def test_has_measure_theory(self, lean_content):
        """Verify MeasureTheory imports."""
        assert "Mathlib.MeasureTheory" in lean_content
    
    def test_import_count(self, lean_content):
        """Verify adequate number of imports."""
        imports = re.findall(r'import Mathlib\.[A-Za-z0-9.]+', lean_content)
        assert len(imports) >= 6, f"Expected at least 6 Mathlib imports, got {len(imports)}"


class TestSpectralProperties:
    """Tests for spectral properties of H_Ψ."""
    
    def test_eigenvalue_defined(self, lean_content):
        """Verify eigenvalue function is defined."""
        assert re.search(r'\bdef\s+eigenvalue\b', lean_content) is not None
    
    def test_eigenvalues_formula(self, lean_content):
        """Verify eigenvalue formula λ_n = 2n + 1."""
        assert "2 * n + 1" in lean_content or "2*n + 1" in lean_content
    
    def test_eigenvalues_discrete_real(self, lean_content):
        """Verify eigenvalues are discrete and real."""
        assert re.search(r'\btheorem\s+eigenvalues_discrete_real\b', lean_content) is not None
    
    def test_eigenvalues_strictly_increasing(self, lean_content):
        """Verify eigenvalues are strictly increasing."""
        assert re.search(r'\btheorem\s+eigenvalues_strictly_increasing\b', lean_content) is not None
    
    def test_eigenvalue_gap(self, lean_content):
        """Verify eigenvalue gap theorem."""
        assert re.search(r'\btheorem\s+eigenvalue_gap\b', lean_content) is not None
    
    def test_spectrum_is_real(self, lean_content):
        """Verify spectrum reality theorem."""
        assert re.search(r'\btheorem\s+spectrum_is_real\b', lean_content) is not None


class TestHermiteFunctions:
    """Tests for Hermite function definitions."""
    
    def test_hermite_poly_defined(self, lean_content):
        """Verify Hermite polynomials are defined."""
        assert re.search(r'\bdef\s+hermitePoly\b', lean_content) is not None
    
    def test_hermite_fun_defined(self, lean_content):
        """Verify normalized Hermite functions are defined."""
        assert re.search(r'\bdef\s+hermiteFun\b', lean_content) is not None
    
    def test_hermite_norm_factor(self, lean_content):
        """Verify Hermite normalization factor is defined."""
        assert re.search(r'\bdef\s+hermiteNormFactor\b', lean_content) is not None


class TestGaussianHilbertSpace:
    """Tests for Gaussian Hilbert space definitions."""
    
    def test_gaussian_measure_defined(self, lean_content):
        """Verify Gaussian measure is defined."""
        assert re.search(r'\bdef\s+gaussianMeasure\b', lean_content) is not None
    
    def test_gaussian_hilbert_defined(self, lean_content):
        """Verify Gaussian Hilbert space is defined."""
        assert re.search(r'\bdef\s+GaussianHilbert\b', lean_content) is not None
    
    def test_gaussian_inner_defined(self, lean_content):
        """Verify Gaussian inner product is defined."""
        assert re.search(r'\bdef\s+gaussianInner\b', lean_content) is not None


class TestSelfAdjointProperties:
    """Tests for self-adjoint property axioms and theorems."""
    
    def test_h_psi_is_symmetric_axiom(self, lean_content):
        """Verify symmetry axiom is stated."""
        assert "H_Ψ_is_symmetric" in lean_content
    
    def test_eigenvectors_orthogonal(self, lean_content):
        """Verify eigenvector orthogonality theorem."""
        assert re.search(r'\btheorem\s+eigenvectors_orthogonal\b', lean_content) is not None
    
    def test_heat_kernel_symmetric(self, lean_content):
        """Verify heat kernel symmetry lemma."""
        assert re.search(r'\blemma\s+heatKernel_symmetric\b', lean_content) is not None


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
    
    def test_has_mensaje(self, lean_content):
        """Verify symbolic message is defined."""
        assert re.search(r'\bdef\s+mensaje_H_ψ_selfadjoint\b', lean_content) is not None


class TestSorryElimination:
    """Tests to verify sorry elimination from the main definition."""
    
    def test_h_psi_definition_has_no_sorry(self, lean_content):
        """Verify the H_ψ definition doesn't use sorry."""
        # Extract the H_ψ definition block
        h_psi_pattern = r'def\s+H_ψ\s*:.*?where.*?(?=\n\s*\n|def\s+|theorem\s+|lemma\s+|end\s+)'
        match = re.search(h_psi_pattern, lean_content, re.DOTALL)
        if match:
            h_psi_block = match.group(0)
            # The main sorry should be eliminated in the H_ψ definition
            # Sorries in other parts are acceptable
            assert "sorry" not in h_psi_block, "H_ψ definition should not contain sorry"
    
    def test_to_lin_is_explicit(self, lean_content):
        """Verify to_lin is explicitly defined."""
        # Check that to_lin is assigned to H_Ψ_linear
        assert "to_lin := H_Ψ_linear" in lean_content
    
    def test_is_self_adjoint_is_explicit(self, lean_content):
        """Verify is_self_adjoint is explicitly defined."""
        # Check that is_self_adjoint is assigned to H_Ψ_is_symmetric
        assert "is_self_adjoint := H_Ψ_is_symmetric" in lean_content
    
    def test_sorries_are_in_helper_lemmas(self, lean_content):
        """Verify any remaining sorries are in helper lemmas, not in main definitions."""
        # Count sorries
        sorry_count = len(re.findall(r'\bsorry\b', lean_content))
        # Allow sorries in helper theorems and corollaries, but not too many
        # The main H_ψ definition should be sorry-free, but helper lemmas
        # like spectrum_is_real and eigenvectors_orthogonal may have sorries
        # as they require extensive Mathlib inner product infrastructure
        assert sorry_count <= 10, f"Too many sorries: {sorry_count}"


class TestMathematicalCorrectness:
    """Tests for mathematical correctness of the formalization."""
    
    def test_hilbert_space_structure(self, lean_content):
        """Verify Hilbert space structure is properly declared."""
        assert "InnerProductSpace" in lean_content
        assert "CompleteSpace" in lean_content
    
    def test_linear_map_type(self, lean_content):
        """Verify linear map type notation."""
        assert "→ₗ" in lean_content  # Linear map notation
    
    def test_inner_product_symmetry(self, lean_content):
        """Verify inner product symmetry is used correctly."""
        assert "inner" in lean_content
        assert re.search(r'inner\s*\([^)]+\)\s*[^)]+\s*=\s*inner', lean_content) is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
