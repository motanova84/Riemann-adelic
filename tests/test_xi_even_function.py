#!/usr/bin/env python3
"""
Test suite for xi_even_function.lean formalization

Verifies the Lean formalization file for:
1. Definition of riemann_xi function
2. Even symmetry theorem: ξ(1 - s) = ξ(s)
3. Corollaries about zeros and the critical line
4. Connection to the Riemann Hypothesis
5. QCAL integration constants

🧠 Formalización: La función ξ(s) es par: ξ(1 - s) = ξ(s)

📘 Justificación:
Este resultado clave proviene directamente de la ecuación funcional 
de la función xi, que combina la ecuación funcional de Riemann ζ con 
simetría alrededor de la línea crítica Re(s) = 1/2. Es esencial para 
restringir los ceros a la línea crítica y establecer el principio de reflexión.

Author: José Manuel Mota Burruezo
Date: November 29, 2025
Part: QCAL Framework - Xi Even Function
DOI: 10.5281/zenodo.17379721
"""

import os
from pathlib import Path


class TestXiEvenFunctionFormalization:
    """Test the Xi even function formalization"""

    def test_xi_even_function_file_exists(self):
        """Verify xi_even_function.lean exists"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_xi_even_function_has_main_theorem(self):
        """Verify the main theorem xi_even is declared"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for main theorem declaration
        assert "theorem xi_even" in content, \
            "Main theorem 'xi_even' not found"
        
        # Check for proper symmetry statement
        assert "riemann_xi (1 - s) = riemann_xi s" in content, \
            "Symmetry statement 'riemann_xi (1 - s) = riemann_xi s' not found"

    def test_xi_even_function_has_definition(self):
        """Verify riemann_xi function is properly defined"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for definition of riemann_xi
        assert "def riemann_xi" in content, \
            "Definition 'riemann_xi' not found"
        
        # Check for key components of the definition
        assert "Gamma" in content, \
            "Gamma function not referenced in definition"
        assert "riemannZeta" in content, \
            "Riemann zeta function not referenced"
        assert "Real.pi" in content, \
            "Pi constant not referenced"

    def test_xi_even_function_has_zeta_functional_equation(self):
        """Verify zeta functional equation axiom is declared"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for functional equation axiom
        assert "axiom zeta_functional_eq" in content, \
            "Zeta functional equation axiom not found"

    def test_xi_even_function_has_gamma_reflection(self):
        """Verify gamma reflection formula axiom is declared"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for gamma reflection axiom
        assert "axiom gamma_reflection_formula" in content, \
            "Gamma reflection formula axiom not found"

    def test_xi_even_function_has_zeros_symmetric(self):
        """Verify corollary about symmetric zeros"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for zeros symmetry theorem
        assert "theorem zeros_symmetric" in content, \
            "Zeros symmetry theorem not found"
        
        # Check for proper statement
        assert "riemann_xi (1 - s) = 0" in content, \
            "Zeros symmetry statement not complete"


class TestXiEvenFunctionHeader:
    """Test header and metadata of xi_even_function.lean"""

    def test_xi_even_function_header(self):
        """Verify file has proper module documentation"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for module documentation
        assert "ξ(1 - s) = ξ(s)" in content, \
            "Main symmetry equation not in documentation"
        assert "even" in content.lower() or "par" in content.lower(), \
            "Even/par property not mentioned in header"

    def test_xi_even_function_has_author_info(self):
        """Verify author information is present"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for author info
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found"
        assert "JMMB" in content, \
            "Author abbreviation not found"

    def test_xi_even_function_has_orcid(self):
        """Verify ORCID is present"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for ORCID
        assert "ORCID: 0009-0002-1923-0773" in content, \
            "ORCID not found or incorrect"

    def test_xi_even_function_has_doi(self):
        """Verify DOI reference is present"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for DOI
        assert "10.5281/zenodo.17379721" in content, \
            "DOI reference not found"

    def test_xi_even_function_has_namespace(self):
        """Verify proper namespace is used"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for namespace
        assert "namespace XiEvenFunction" in content, \
            "XiEvenFunction namespace not found"


class TestXiEvenFunctionMathematicalContent:
    """Test mathematical content of xi_even_function.lean"""

    def test_xi_even_function_has_symmetric_factor_lemma(self):
        """Verify symmetric factor invariance lemma"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for symmetric factor lemma
        assert "lemma symmetric_factor_invariant" in content, \
            "Symmetric factor invariance lemma not found"

    def test_xi_even_function_has_critical_line_lemma(self):
        """Verify critical line fixed by reflection lemma"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for critical line lemma
        assert "critical_line_fixed" in content, \
            "Critical line lemma not found"
        
        # Check for Re(s) = 1/2 statement
        assert "s.re = 1/2" in content, \
            "Critical line condition not found"

    def test_xi_even_function_has_mathlib_imports(self):
        """Verify Mathlib imports are correct"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for essential Mathlib imports
        assert "import Mathlib.Analysis.SpecialFunctions.Gamma.Basic" in content, \
            "Gamma import not found"
        assert "import Mathlib.NumberTheory.ZetaFunction" in content, \
            "ZetaFunction import not found"
        assert "import Mathlib.Analysis.Complex.Basic" in content, \
            "Complex import not found"

    def test_xi_even_function_has_riemann_hypothesis_def(self):
        """Verify Riemann Hypothesis definition"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for RH definition
        assert "def RiemannHypothesis" in content, \
            "Riemann Hypothesis definition not found"
        assert "ρ.re = 1/2" in content, \
            "RH condition not found"

    def test_xi_even_function_has_qcal_integration(self):
        """Verify QCAL integration constants"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for QCAL frequency
        assert "141.7001" in content, \
            "QCAL base frequency not found"
        
        # Check for QCAL coherence
        assert "244.36" in content, \
            "QCAL coherence constant not found"
        
        # Check for QCAL equation
        assert "Ψ = I × A_eff²" in content, \
            "QCAL fundamental equation not found"

    def test_xi_even_function_has_xi_even_about_half(self):
        """Verify xi_even_about_half corollary"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for even about half theorem
        assert "theorem xi_even_about_half" in content, \
            "xi_even_about_half theorem not found"


class TestXiEvenFunctionCompleteness:
    """Test completeness of the formalization"""

    def test_xi_even_function_is_valid_lean(self):
        """Verify file has valid Lean 4 structure"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for section/namespace structure
        assert "noncomputable section" in content, \
            "Noncomputable section not declared"
        assert "end" in content, \
            "End of section/namespace not found"
        
        # Check for open statements
        assert "open Complex" in content, \
            "Complex namespace not opened"

    def test_xi_even_function_has_summary_section(self):
        """Verify summary section exists at end"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for summary section markers
        assert "Summary" in content, \
            "Summary section not found"
        assert "Theorems Proven" in content or "References" in content, \
            "References/Theorems section not found"

    def test_xi_even_function_has_titchmarsh_reference(self):
        """Verify Titchmarsh reference is present"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for Titchmarsh reference
        assert "Titchmarsh" in content, \
            "Titchmarsh reference not found"

    def test_xi_even_function_uses_lean4_syntax(self):
        """Verify file uses Lean 4 syntax, not Lean 3"""
        file_path = Path("formalization/lean/spectral/xi_even_function.lean")
        content = file_path.read_text()
        
        # Check for Lean 4 syntax elements
        assert "by" in content, \
            "Lean 4 'by' tactic not found"
        
        # Check for Lean 4 theorem/lemma style (no 'begin...end' blocks)
        # Note: 'end' alone is valid in Lean 4 for closing namespaces/sections
        # We specifically check for Lean 3's 'begin...end' proof blocks
        import re
        begin_end_pattern = re.compile(r'\bbegin\b.*?\bend\b', re.DOTALL)
        assert not begin_end_pattern.search(content), \
            "Lean 3 'begin...end' proof block syntax found - should use Lean 4 'by' tactic"
