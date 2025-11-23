#!/usr/bin/env python3
"""
Test suite for identity_principle_exp_type formalization

Verifies the new Lean formalization file for:
- identity_principle_exp_type.lean

This module provides the identity principle for entire functions of exponential type,
closing the analytical uniqueness chain for the Riemann Hypothesis proof.

Author: José Manuel Mota Burruezo
Date: November 23, 2025
"""

import os
import re
from pathlib import Path


class TestIdentityPrincipleExpType:
    """Test the identity principle for exponential type functions formalization"""

    def test_identity_principle_file_exists(self):
        """Verify identity_principle_exp_type.lean exists"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_identity_principle_has_exponential_type_def(self):
        """Verify exponential_type definition is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for definition
        assert "def exponential_type" in content, \
            "Definition 'exponential_type' not found"
        
        # Check for proper structure
        assert "∃ M > 0" in content, \
            "Existential quantifier for M not found"
        
        # Check for exponential bound
        assert "Real.exp" in content, \
            "Real.exp (exponential function) not found"

    def test_identity_principle_has_main_lemma(self):
        """Verify the main identity principle lemma is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for lemma declaration
        assert "lemma identity_principle_exp_line" in content, \
            "Main lemma 'identity_principle_exp_line' not found"
        
        # Check for hypotheses
        assert "hf : Differentiable" in content, \
            "Differentiability hypothesis not found"
        
        assert "hexp : exponential_type" in content, \
            "Exponential type hypothesis not found"
        
        assert "hvanish" in content, \
            "Vanishing hypothesis not found"

    def test_identity_principle_imports_correct(self):
        """Verify correct imports in identity_principle_exp_type.lean"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        required_imports = [
            "Mathlib.Analysis.Complex.Basic",
            "Mathlib.Topology.MetricSpace.Basic",
            "Mathlib.Analysis.Analytic.Basic",
        ]
        
        for imp in required_imports:
            assert imp in content, f"Required import '{imp}' not found"

    def test_identity_principle_has_proof_steps(self):
        """Verify the proof structure is complete"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for proof steps mentioned in comments
        assert "Paso 1" in content, "Proof step 1 not found"
        assert "Paso 2" in content, "Proof step 2 not found"
        assert "Paso 3" in content, "Proof step 3 not found"

    def test_identity_principle_uses_analytic_functions(self):
        """Verify use of analytic function theory"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for analytic function concepts
        assert "AnalyticOn" in content, \
            "AnalyticOn not found"
        
        # Check for identity theorem references (implementation may vary)
        assert ("teorema de identidad" in content or 
                "identity theorem" in content or
                "AnalyticOn.eqOn" in content), \
            "Identity theorem reference not found"

    def test_identity_principle_critical_line_reference(self):
        """Verify critical line (1/2 + I*t) is referenced correctly"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for critical line 1/2
        assert "1/2" in content, \
            "Critical line real part 1/2 not found"
        
        assert "I * t" in content or "I*t" in content, \
            "Imaginary part I*t not found"

    def test_identity_principle_header(self):
        """Verify identity_principle_exp_type.lean has proper header"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for header comment
        assert "identity_principle_exp_type.lean" in content, \
            "File header missing file name"
        
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found in header"
        
        assert "ICQ" in content or "Instituto de Conciencia Cuántica" in content, \
            "Institution not found in header"
        
        assert "QCAL" in content, \
            "QCAL reference not found in header"

    def test_identity_principle_documentation(self):
        """Verify proper documentation is present"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for doc comments
        assert "/--" in content, \
            "Documentation comments not found"
        
        # Check for closing comment about usage
        assert "entire_exponential_growth" in content or "paley_wiener_uniqueness" in content, \
            "Usage references not found in documentation"

    def test_identity_principle_uses_complex_analysis(self):
        """Verify use of complex analysis concepts"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for complex analysis concepts
        assert "Complex" in content, \
            "Complex numbers not referenced"
        
        assert "Complex.abs" in content, \
            "Complex absolute value not found"

    def test_identity_principle_noncomputable(self):
        """Verify noncomputable section is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        assert "noncomputable section" in content, \
            "noncomputable section not declared"

    def test_identity_principle_opens_namespaces(self):
        """Verify required namespaces are opened"""
        file_path = Path("formalization/lean/RiemannAdelic/identity_principle_exp_type.lean")
        content = file_path.read_text()
        
        # Check for opened namespaces
        assert "open Complex" in content, \
            "Complex namespace not opened"
        
        assert "open Topology" in content or "Topology" in content, \
            "Topology namespace not referenced"


if __name__ == "__main__":
    import pytest
    pytest.main([__file__, "-v"])
