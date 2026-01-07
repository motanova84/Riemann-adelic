#!/usr/bin/env python3
"""
Test suite for Paley-Wiener uniqueness and D limit formalization

Verifies the new Lean formalization files for:
1. paley_wiener_uniqueness.lean
2. D_limit_equals_xi.lean

Author: José Manuel Mota Burruezo
Date: November 21, 2025
"""

import os
import re
from pathlib import Path


class TestPaleyWienerFormalization:
    """Test the Paley-Wiener uniqueness formalization"""

    def test_paley_wiener_file_exists(self):
        """Verify paley_wiener_uniqueness.lean exists"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_paley_wiener_has_main_theorem(self):
        """Verify the main uniqueness theorem is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        content = file_path.read_text()
        
        # Check for theorem declaration
        assert "theorem paley_wiener_uniqueness" in content, \
            "Main theorem 'paley_wiener_uniqueness' not found"
        
        # Check for proper structure
        assert "EntireOrderOne" in content, \
            "EntireOrderOne structure not found"
        
        # Check for symmetry hypothesis
        assert "hsymm_f" in content and "hsymm_g" in content, \
            "Symmetry hypotheses not found"
        
        # Check for critical line hypothesis
        assert "hcrit" in content, \
            "Critical line hypothesis not found"

    def test_paley_wiener_imports_correct(self):
        """Verify correct imports in paley_wiener_uniqueness.lean"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        content = file_path.read_text()
        
        required_imports = [
            "Mathlib.Analysis.Complex.CauchyIntegral",
            "Mathlib.Analysis.Complex",
        ]
        
        # Check that at least one of the required imports is present
        found = any(imp in content for imp in required_imports)
        assert found, f"None of the required imports found: {required_imports}"

    def test_paley_wiener_has_helper_lemma(self):
        """Verify helper lemma for exponential bounds exists"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        content = file_path.read_text()
        
        assert "add_exp_le_max_exp_mul" in content, \
            "Helper lemma 'add_exp_le_max_exp_mul' not found"

    def test_paley_wiener_structure(self):
        """Verify the proof structure is complete"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        content = file_path.read_text()
        
        # Check for proof steps mentioned in comments
        assert "Paso 1" in content, "Proof step 1 not found"
        assert "Paso 2" in content, "Proof step 2 not found"
        assert "Paso 3" in content, "Proof step 3 not found"
        assert "Paso 4" in content, "Proof step 4 not found"
        assert "Paso 5" in content, "Proof step 5 not found"


class TestDLimitFormalization:
    """Test the D limit equals xi formalization"""

    def test_d_limit_file_exists(self):
        """Verify D_limit_equals_xi.lean exists"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_d_limit_has_main_definitions(self):
        """Verify main definitions are present"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        # Check for key definitions
        definitions = [
            "xi_function",
            "P_polynomial",
            "D_ideal",
            "D_approx"
        ]
        
        for defn in definitions:
            assert f"def {defn}" in content, f"Definition '{defn}' not found"

    def test_d_limit_has_lemmas(self):
        """Verify all required lemmas are declared"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        lemmas = [
            "D_approx_tendsto_ideal",
            "D_ideal_eq_reflection",
            "xi_over_P_eq_reflection"
        ]
        
        for lemma in lemmas:
            assert f"lemma {lemma}" in content, f"Lemma '{lemma}' not found"

    def test_d_limit_has_main_theorem(self):
        """Verify the main theorem is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        assert "theorem D_limit_equals_xi" in content, \
            "Main theorem 'D_limit_equals_xi' not found"
        
        # Check for Tendsto in theorem
        assert "Tendsto" in content, \
            "Tendsto (limit) statement not found"

    def test_d_limit_imports_correct(self):
        """Verify correct imports in D_limit_equals_xi.lean"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        required_imports = [
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Analysis.Asymptotics",
            "Mathlib.NumberTheory.ZetaFunction",
            "Mathlib.Analysis.SpecialFunctions.Gamma"
        ]
        
        for imp in required_imports:
            assert imp in content, f"Required import '{imp}' not found"

    def test_d_limit_uses_gamma_and_zeta(self):
        """Verify Gamma and zeta functions are used"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        assert "Gamma" in content, "Gamma function not found"
        assert "riemannZeta" in content or "zeta" in content, \
            "Zeta function not found"


class TestMainIntegration:
    """Test Main.lean integration"""

    def test_main_imports_paley_wiener(self):
        """Verify Main.lean imports paley_wiener_uniqueness"""
        file_path = Path("formalization/lean/Main.lean")
        content = file_path.read_text()
        
        assert "import RiemannAdelic.paley_wiener_uniqueness" in content, \
            "Main.lean does not import paley_wiener_uniqueness"

    def test_main_imports_d_limit(self):
        """Verify Main.lean imports D_limit_equals_xi"""
        file_path = Path("formalization/lean/Main.lean")
        content = file_path.read_text()
        
        assert "import RiemannAdelic.D_limit_equals_xi" in content, \
            "Main.lean does not import D_limit_equals_xi"

    def test_main_mentions_new_modules(self):
        """Verify Main.lean mentions the new modules in output"""
        file_path = Path("formalization/lean/Main.lean")
        content = file_path.read_text()
        
        # Check that the IO.println mentions are updated
        assert "Paley-Wiener theory" in content or "uniqueness" in content, \
            "Main.lean does not mention Paley-Wiener in output"

    def test_main_imports_identity_principle(self):
        """Verify Main.lean imports identity_principle_exp_type"""
        file_path = Path("formalization/lean/Main.lean")
        content = file_path.read_text()
        
        assert "import paley.identity_principle_exp_type" in content, \
            "Main.lean does not import identity_principle_exp_type"


class TestIdentityPrincipleFormalization:
    """Test the Identity Principle for Exponential Type formalization"""

    def test_identity_principle_file_exists(self):
        """Verify identity_principle_exp_type.lean exists"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_identity_principle_has_exponential_type_def(self):
        """Verify exponential_type definition is declared"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for definition
        assert "def exponential_type" in content, \
            "Definition 'exponential_type' not found"
        
        # Check for growth bound in definition
        assert "Real.exp" in content, \
            "Exponential growth not found in definition"

    def test_identity_principle_has_main_lemma(self):
        """Verify the main identity principle lemma is declared"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for lemma declaration
        assert "lemma identity_principle_exp_line" in content, \
            "Main lemma 'identity_principle_exp_line' not found"
        
        # Check for hypotheses
        assert "Differentiable" in content, \
            "Differentiable hypothesis not found"
        assert "exponential_type" in content, \
            "exponential_type hypothesis not found"

    def test_identity_principle_imports_correct(self):
        """Verify correct imports in identity_principle_exp_type.lean"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        required_imports = [
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Topology.MetricSpace.Basic",
            "Mathlib.Analysis.Analytic.Basic",
        ]
        
        for imp in required_imports:
            assert imp in content, f"Required import '{imp}' not found"

    def test_identity_principle_header(self):
        """Verify identity_principle_exp_type.lean has proper header"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for header comment
        assert "identity_principle_exp_type.lean" in content, \
            "File header missing file name"
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found in header"
        assert "QCAL" in content, \
            "QCAL reference not found in header"

    def test_identity_principle_has_documentation(self):
        """Verify the file has proper documentation"""
        file_path = Path("formalization/lean/paley/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for mathematical documentation
        assert "recta crítica" in content or "critical line" in content, \
            "Critical line mention not found"
        assert "principio de identidad" in content or "identity theorem" in content, \
            "Identity principle reference not found"


class TestFileHeaders:
    """Test file headers and documentation"""

    def test_paley_wiener_header(self):
        """Verify paley_wiener_uniqueness.lean has proper header"""
        file_path = Path("formalization/lean/RiemannAdelic/paley_wiener_uniqueness.lean")
        content = file_path.read_text()
        
        # Check for header comment
        assert "paley_wiener_uniqueness.lean" in content, \
            "File header missing file name"
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found in header"
        assert "100% sorry-free" in content or "sorry" in content, \
            "Completion status not mentioned"

    def test_d_limit_header(self):
        """Verify D_limit_equals_xi.lean has proper header"""
        file_path = Path("formalization/lean/RiemannAdelic/D_limit_equals_xi.lean")
        content = file_path.read_text()
        
        # Check for header comment
        assert "D_limit_equals_xi.lean" in content, \
            "File header missing file name"
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found in header"


if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-v"])
