#!/usr/bin/env python3
"""
Test suite for the Schrödinger Operator Axiom formalization.

This test module validates the structure and content of the Lean formalization
of the compact self-adjoint Schrödinger operator Ĥ_Ψ.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 27 November 2025
DOI: 10.5281/zenodo.17379721
"""

import os
import pytest
from pathlib import Path

# Path to the Lean file
LEAN_FILE = Path("formalization/lean/spectral/schrodinger_operator_axiom.lean")


class TestSchrodingerOperatorAxiom:
    """Test suite for Schrödinger Operator Axiom Lean file."""
    
    @pytest.fixture(autouse=True)
    def setup_method(self):
        """Load the Lean file content."""
        if LEAN_FILE.exists():
            with open(LEAN_FILE, 'r', encoding='utf-8') as f:
                self.content = f.read()
        else:
            self.content = ""
    
    def test_file_exists(self):
        """Test that the Lean file exists."""
        assert LEAN_FILE.exists(), f"Lean file not found: {LEAN_FILE}"
    
    def test_namespace_qcal(self):
        """Test that QCAL namespace is defined."""
        assert "namespace QCAL" in self.content, "QCAL namespace not found"
        assert "end QCAL" in self.content, "QCAL namespace not closed"
    
    def test_hilbert_space_axiom(self):
        """Test that the abstract Hilbert space H_Ψ is defined."""
        assert "axiom H_Ψ : Type" in self.content, "H_Ψ type axiom not found"
    
    def test_inner_product_structure(self):
        """Test that inner product space structure is defined."""
        assert "InnerProductSpace ℂ H_Ψ" in self.content, \
            "InnerProductSpace instance not found"
    
    def test_complete_space(self):
        """Test that completeness axiom is defined."""
        assert "CompleteSpace H_Ψ" in self.content, \
            "CompleteSpace instance not found"
    
    def test_schrodinger_operator_axiom(self):
        """Test that the Schrödinger operator is defined."""
        assert "axiom Ĥ_Ψ : H_Ψ → H_Ψ" in self.content, \
            "Ĥ_Ψ operator axiom not found"
    
    def test_self_adjoint_predicate(self):
        """Test that self-adjoint predicate is defined."""
        assert "def is_self_adjoint" in self.content, \
            "is_self_adjoint predicate not found"
        assert "inner (T x) y = inner x (T y)" in self.content, \
            "Self-adjointness condition not found"
    
    def test_compact_operator_predicate(self):
        """Test that compact operator predicate is defined."""
        assert "def compact_operator" in self.content, \
            "compact_operator predicate not found"
        assert "Metric.Bounded" in self.content or "bounded" in self.content.lower(), \
            "Bounded set condition not found"
    
    def test_main_axiom(self):
        """Test that the main axiom is stated."""
        assert "axiom schrödinger_self_adjoint_compact" in self.content, \
            "Main axiom schrödinger_self_adjoint_compact not found"
        assert "is_self_adjoint Ĥ_Ψ" in self.content, \
            "Self-adjointness part of main axiom not found"
        assert "compact_operator Ĥ_Ψ" in self.content, \
            "Compactness part of main axiom not found"
    
    def test_self_adjoint_theorem(self):
        """Test that self-adjointness extraction theorem exists."""
        assert "theorem Ĥ_Ψ_is_self_adjoint" in self.content, \
            "Ĥ_Ψ_is_self_adjoint theorem not found"
    
    def test_compact_theorem(self):
        """Test that compactness extraction theorem exists."""
        assert "theorem Ĥ_Ψ_is_compact" in self.content, \
            "Ĥ_Ψ_is_compact theorem not found"
    
    def test_spectrum_definition(self):
        """Test that spectrum is defined."""
        assert "def spectrum_Ĥ_Ψ" in self.content, \
            "spectrum_Ĥ_Ψ definition not found"
    
    def test_spectrum_real_theorem(self):
        """Test that spectrum realness theorems exist."""
        assert "theorem spectrum_inherently_real" in self.content or \
               "theorem spectrum_is_real" in self.content, \
            "Spectrum realness theorem not found"
    
    def test_eigenvector_orthogonality(self):
        """Test that eigenvector orthogonality theorem exists."""
        assert "theorem eigenvectors_orthogonal" in self.content, \
            "eigenvectors_orthogonal theorem not found"
    
    def test_reference_citation(self):
        """Test that proper references are included."""
        assert "Reed & Simon" in self.content, \
            "Reed & Simon reference not found"
        assert "von Neumann" in self.content, \
            "von Neumann reference not found"
        assert "Berry" in self.content or "Keating" in self.content, \
            "Berry-Keating reference not found"
    
    def test_qcal_frequency(self):
        """Test that QCAL base frequency is defined."""
        assert "141.7001" in self.content, \
            "QCAL base frequency 141.7001 not found"
        assert "QCAL_base_frequency" in self.content, \
            "QCAL_base_frequency constant not found"
    
    def test_qcal_coherence(self):
        """Test that QCAL coherence constant is defined."""
        assert "244.36" in self.content, \
            "QCAL coherence constant 244.36 not found"
        assert "QCAL_coherence" in self.content, \
            "QCAL_coherence constant not found"
    
    def test_vibrational_message(self):
        """Test that vibrational message is included."""
        assert "mensaje_schrodinger" in self.content, \
            "Vibrational message not found"
    
    def test_mathlib_imports(self):
        """Test that necessary Mathlib imports are present."""
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace.Basic",
            "Mathlib.Analysis.Complex.Basic"
        ]
        for imp in required_imports:
            assert imp in self.content, f"Required import {imp} not found"
    
    def test_noncomputable_section(self):
        """Test that noncomputable section is used correctly."""
        assert "noncomputable section" in self.content, \
            "noncomputable section not found"
    
    def test_author_information(self):
        """Test that author information is included."""
        assert "José Manuel Mota Burruezo" in self.content, \
            "Author name not found"
        assert "10.5281/zenodo" in self.content, \
            "DOI reference not found"
    
    def test_problem_statement_elements(self):
        """Test that elements from the problem statement are present."""
        # From the problem statement
        assert "Schrödinger" in self.content, \
            "Schrödinger not mentioned"
        assert "self-adjoint" in self.content.lower() or "self_adjoint" in self.content, \
            "Self-adjoint not mentioned"
        assert "compact" in self.content.lower(), \
            "Compact not mentioned"


class TestSchrodingerOperatorStructure:
    """Test the mathematical structure of the formalization."""
    
    @pytest.fixture(autouse=True)
    def setup_method(self):
        """Load the Lean file content."""
        if LEAN_FILE.exists():
            with open(LEAN_FILE, 'r', encoding='utf-8') as f:
                self.content = f.read()
        else:
            self.content = ""
    
    def test_axiom_consistency(self):
        """Test that axioms are consistently defined."""
        # Count axiom declarations
        axiom_count = self.content.count("axiom ")
        assert axiom_count >= 4, \
            f"Expected at least 4 axioms, found {axiom_count}"
    
    def test_theorem_count(self):
        """Test that sufficient theorems are derived."""
        theorem_count = self.content.count("theorem ")
        assert theorem_count >= 3, \
            f"Expected at least 3 theorems, found {theorem_count}"
    
    def test_definition_count(self):
        """Test that necessary definitions are present."""
        def_count = self.content.count("def ")
        assert def_count >= 4, \
            f"Expected at least 4 definitions, found {def_count}"
    
    def test_documentation_quality(self):
        """Test that documentation is comprehensive."""
        # Count documentation blocks
        doc_blocks = self.content.count("/-!")
        assert doc_blocks >= 5, \
            f"Expected at least 5 documentation blocks, found {doc_blocks}"
        
        # Check for section headers
        assert "## 1." in self.content or "## 1" in self.content, \
            "Section numbering not found"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
