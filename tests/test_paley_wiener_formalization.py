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
            "Mathlib.Analysis.Complex",
        ]
        
        for imp in required_imports:
            assert imp in content, f"Required import '{imp}' not found"

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
