"""
Test suite for V5.2 Minimal Axiom System validation

This module validates the V5.2 axiom documentation and ensures
that the minimal axiom system is properly documented with:
- 3 fundamental axioms (Noésicos V5.2)
- All other properties as theorems
- Non-circular construction
- Clear mathematical justification

Author: JMMB Ψ ✳ ∞
Version: V5.2
Date: October 24, 2025
"""

import os
import pytest
import re
from pathlib import Path


# Path to repository root
REPO_ROOT = Path(__file__).parent.parent


class TestV52MinimalAxioms:
    """Test the V5.2 minimal axiom system documentation."""

    def test_v52_axiom_document_exists(self):
        """Verify that AXIOMAS_MINIMOS_V5.2.md exists."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        assert doc_path.exists(), "AXIOMAS_MINIMOS_V5.2.md must exist"

    def test_v52_document_structure(self):
        """Verify the document has all required sections."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        required_sections = [
            "# Axiomas Mínimos del Sistema D(s)",
            "## I. Los Tres Axiomas Noésicos V5.2",
            "## II. Todo lo Demás es Teorema",
            "## III. Construcción No Circular",
            "## IV. Lenguaje Técnico Formal",
            "## V. Verificación y Validación",
        ]
        
        for section in required_sections:
            assert section in content, f"Missing section: {section}"

    def test_three_fundamental_axioms_documented(self):
        """Verify that exactly 3 fundamental axioms are documented."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check for the 3 axioms
        assert "### Axiom 1: Medida Adélica Finita S" in content
        assert "### Axiom 2: Operadores Autoadjuntos con Espectro Discreto" in content
        assert "### Axiom 3: Teorema de Fredholm + Determinante Analítico" in content
        
        # Verify axiom table
        assert "Axiom 1" in content and "Existencia de medida adélica finita S" in content
        assert "Axiom 2" in content and "Definibilidad de operadores autoadjuntos" in content
        assert "Axiom 3" in content and "Aplicabilidad de teorema de Fredholm" in content

    def test_axiom1_medida_adelica(self):
        """Verify Axiom 1 (S-finite adelic measure) is properly documented."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check key components
        assert "S_finite_adelic_measure" in content
        assert "Medida Haar" in content
        assert "Compactación S-finita" in content
        assert "No es circular" in content

    def test_axiom2_operador_autoadjunto(self):
        """Verify Axiom 2 (self-adjoint operator) is properly documented."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check key components
        assert "selfAdjoint_discrete_spectrum" in content
        assert "IsSelfAdjoint H" in content
        assert "espectro discreto" in content or "IsDiscrete" in content
        assert "eigenvalores reales" in content or "λₙ ∈ ℝ" in content

    def test_axiom3_fredholm_determinante(self):
        """Verify Axiom 3 (Fredholm determinant) is properly documented."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check key components
        assert "fredholm_analytic_determinant" in content
        assert "IsTraceClass" in content or "traza" in content
        assert "determinante analítico" in content or "Det(I - s·K)" in content

    def test_all_theorems_derived(self):
        """Verify that key properties are now theorems, not axioms."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Section "Todo lo Demás es Teorema" must exist
        assert "## II. Todo lo Demás es Teorema" in content
        
        # Check that these are documented as theorems
        assert "### Teorema 1: Función Entera de Orden 1" in content
        assert "### Teorema 2: Simetría Funcional" in content
        assert "### Teorema 3: Ceros Reales en Línea Crítica" in content
        assert "### Teorema 4: D(s) ≡ Ξ(s)" in content

    def test_theorem1_entire_function(self):
        """Verify Theorem 1 (entire function) is documented as derived."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "D_entire_order_one" in content
        # Check it's documented as a theorem (not axiom)
        assert "### Teorema 1: Función Entera de Orden 1" in content
        assert "**Teorema**" in content

    def test_theorem2_functional_equation(self):
        """Verify Theorem 2 (functional equation) is documented as derived."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "D_functional_equation" in content
        assert "D(1-s) = D(s)" in content
        assert "Sumación de Poisson" in content

    def test_theorem3_zeros_critical_line(self):
        """Verify Theorem 3 (zeros on critical line) is documented as derived."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "zeros_on_critical_line" in content
        assert "Re(s) = 1/2" in content or "ℜs = ½" in content
        assert "Consecuencia Espectral" in content or "espacio de de Branges" in content

    def test_theorem4_d_equals_xi(self):
        """Verify Theorem 4 (D ≡ Ξ) is documented as derived."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "D_equals_Xi" in content or "D(s) ≡ Ξ(s)" in content
        assert "Coincidencia de Medidas Espectrales" in content or "μ_D = μ_Ξ" in content

    def test_non_circular_construction(self):
        """Verify that non-circular construction is documented."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "## III. Construcción No Circular" in content
        assert "Diagrama de Dependencias" in content
        assert "Ausencia de Circularidad" in content
        
        # Check that ζ(s) is NOT assumed
        non_circular_section = content[content.find("## III. Construcción No Circular"):]
        assert "No se asume" in non_circular_section
        assert "Propiedades de ζ(s)" in non_circular_section or "ζ(s)" in non_circular_section

    def test_mathematical_formula_d_construction(self):
        """Verify the key formula D(s) ∈ 𝔼 with properties."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check for D(1-s) = D(s)
        assert "D(1-s) = D(s)" in content or "D(1-s)=D(s)" in content
        
        # Check for spectral measure equivalence
        assert "μ_D = μ_Ξ" in content or "μ_D" in content

    def test_lean4_formalization_snippets(self):
        """Verify that Lean 4 code snippets are present."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check for Lean code blocks
        assert "```lean" in content
        assert "axiom S_finite_adelic_measure" in content
        assert "axiom selfAdjoint_discrete_spectrum" in content
        assert "axiom fredholm_analytic_determinant" in content
        assert "theorem D_entire_order_one" in content
        assert "theorem D_functional_equation" in content

    def test_validation_section_present(self):
        """Verify validation section with tests and numerical verification."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "## V. Verificación y Validación" in content
        assert "Tests Matemáticos" in content or "Test 1" in content
        assert "validate_v5_coronacion.py" in content

    def test_references_preserved(self):
        """Verify that DOI and mathematical references are preserved."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check DOI
        assert "10.5281/zenodo.17116291" in content
        
        # Check references
        assert "Referencias Matemáticas" in content or "## IX. Referencias" in content
        assert "Tate, J. T." in content
        assert "Weil, A." in content
        assert "Fredholm, I." in content or "Fredholm" in content
        assert "de Branges" in content
        assert "Hadamard" in content

    def test_transparency_statement(self):
        """Verify that transparency is explicitly stated."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Check title mentions transparency
        assert "Transparencia" in content
        
        # Check that the document explains what is assumed vs proven
        assert "Qué se asume" in content or "axiomas estructurales" in content
        assert "Qué se demuestra" in content or "teoremas" in content

    def test_dependency_diagram_present(self):
        """Verify that dependency diagram is present."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "Diagrama de Dependencias" in content
        # Check for diagram structure with arrows
        assert "↓" in content
        assert "Axiom 1" in content or "Medida Adélica" in content


class TestV52NumericalValidation:
    """Test numerical validation of V5.2 axiom system."""

    @pytest.mark.skip(reason="Requires mpmath and numerical computation (optional)")
    def test_functional_equation_symmetry(self):
        """Verify D(1-s) = D(s) numerically."""
        # This would require implementing D(s) computation
        # Skipped as it's covered by validate_v5_coronacion.py
        pass


class TestV52Documentation:
    """Test documentation quality and completeness."""

    def test_document_has_author_and_date(self):
        """Verify document has proper metadata."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "**Autor**: José Manuel Mota Burruezo" in content or "JMMB" in content
        assert "**Versión**: V5.2" in content
        assert "**Fecha**:" in content
        assert "**DOI**:" in content

    def test_document_has_conclusion(self):
        """Verify document has conclusion section."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "## X. Conclusión" in content or "Conclusión" in content
        assert "Sistema V5.2" in content or "Axiomas fundamentales: 3" in content

    def test_document_mentions_next_steps(self):
        """Verify document outlines next steps (V5.3/V5.4)."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "V5.3" in content
        assert "V5.4" in content or "Próximos Pasos" in content

    def test_bilingual_documentation(self):
        """Verify document has Spanish primary with technical English."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        # Spanish sections
        assert "Axiomas Mínimos" in content
        assert "Teorema" in content
        
        # English technical terms
        assert "self-adjoint" in content or "IsSelfAdjoint" in content
        assert "spectrum" in content or "espectro" in content

    def test_comparison_with_classical_approach(self):
        """Verify comparison with classical Riemann approach."""
        doc_path = REPO_ROOT / "AXIOMAS_MINIMOS_V5.2.md"
        content = doc_path.read_text(encoding='utf-8')
        
        assert "Aproximación Clásica" in content or "Comparación" in content
        assert "Riemann 1859" in content or "clásica" in content
        assert "Aproximación V5.2" in content or "V5.2 (JMMB" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
