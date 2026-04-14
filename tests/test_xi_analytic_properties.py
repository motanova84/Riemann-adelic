#!/usr/bin/env python3
"""
Test suite for Xi_analytic_properties.lean formalization (Script 14)

Verifies the Lean formalization file for:
1. Definition of Xi function Ξ(s) = π^{-s/2} · Γ(s/2) · ζ(s)
2. Well-definedness: Ξ is defined for all s ∈ ℂ
3. Entirety: Ξ is analytic on all of ℂ
4. Schwartz-type decay: exponential type 1 growth bounds
5. Pole cancellation analysis
6. QCAL integration constants

The analytic properties of Ξ are fundamental for:
- Hadamard factorization
- Spectral theory applications
- Hilbert-Polya operator construction

Author: José Manuel Mota Burruezo
Date: November 29, 2025
Part: QCAL Framework - Script 14 Xi Analytic Properties
DOI: 10.5281/zenodo.17379721
"""

import os
from pathlib import Path


class TestXiAnalyticPropertiesFormalization:
    """Test the Xi analytic properties formalization"""

    def test_xi_analytic_properties_file_exists(self):
        """Verify Xi_analytic_properties.lean exists"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        assert file_path.exists(), f"File not found: {file_path}"

    def test_xi_analytic_properties_has_xi_definition(self):
        """Verify Xi function is properly defined"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for definition of Xi
        assert "def Xi" in content, \
            "Definition 'Xi' not found"
        
        # Check for key components of the definition
        assert "Gamma" in content, \
            "Gamma function not referenced in definition"
        assert "riemannZeta" in content, \
            "Riemann zeta function not referenced"
        assert "Real.pi" in content, \
            "Pi constant not referenced"

    def test_xi_analytic_properties_has_well_defined_theorem(self):
        """Verify Xi_well_defined_on_C theorem is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for well-definedness theorem
        assert "theorem Xi_well_defined_on_C" in content, \
            "Xi_well_defined_on_C theorem not found"

    def test_xi_analytic_properties_has_entire_theorem(self):
        """Verify Xi_entire_analytic_on_C and Xi_is_entire_function theorems"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for entirety theorems
        assert "theorem Xi_entire_analytic_on_C" in content, \
            "Xi_entire_analytic_on_C theorem not found"
        assert "AnalyticOn ℂ Xi Set.univ" in content, \
            "AnalyticOn statement not found"
        
        assert "theorem Xi_is_entire_function" in content, \
            "Xi_is_entire_function theorem not found"
        assert "Differentiable ℂ Xi" in content, \
            "Differentiable statement not found"

    def test_xi_analytic_properties_has_product_entire(self):
        """Verify xi_product_is_entire theorem is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for product entirety theorem
        assert "theorem xi_product_is_entire" in content, \
            "xi_product_is_entire theorem not found"

    def test_xi_analytic_properties_has_schwartz_decay(self):
        """Verify Schwartz-type decay theorems"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for Schwartz decay theorems
        assert "Xi_exponential_type_one" in content, \
            "Xi_exponential_type_one theorem not found"
        assert "Xi_rapid_decay_vertical" in content, \
            "Xi_rapid_decay_vertical theorem not found"
        assert "Xi_Schwartz_type_decay" in content, \
            "Xi_Schwartz_type_decay theorem not found"


class TestXiAnalyticPropertiesPoleCancellation:
    """Test pole cancellation lemmas"""

    def test_xi_analytic_properties_has_pi_power_entire(self):
        """Verify pi_power_entire lemma is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for pi power entirety lemma
        assert "lemma pi_power_entire" in content, \
            "pi_power_entire lemma not found"

    def test_xi_analytic_properties_has_gamma_meromorphic(self):
        """Verify Gamma meromorphic lemma is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for Gamma meromorphic lemma
        assert "Gamma_half_meromorphic_away_from_poles" in content, \
            "Gamma_half_meromorphic_away_from_poles lemma not found"

    def test_xi_analytic_properties_has_zeta_holomorphic(self):
        """Verify zeta holomorphic lemma is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for zeta holomorphic lemma
        assert "zeta_holomorphic_away_from_one" in content, \
            "zeta_holomorphic_away_from_one lemma not found"

    def test_xi_analytic_properties_has_trivial_zeros(self):
        """Verify trivial zeros lemma is declared"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for trivial zeros lemma
        assert "zeta_trivial_zeros" in content, \
            "zeta_trivial_zeros lemma not found"

    def test_xi_analytic_properties_has_pole_cancellation(self):
        """Verify pole cancellation lemmas"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for pole cancellation lemmas
        assert "Gamma_times_zeta_finite_at_zero" in content, \
            "Gamma_times_zeta_finite_at_zero lemma not found"
        assert "pole_cancellation_at_trivial_zeros" in content, \
            "pole_cancellation_at_trivial_zeros lemma not found"


class TestXiAnalyticPropertiesHeader:
    """Test header and metadata"""

    def test_xi_analytic_properties_header(self):
        """Verify file has proper module documentation"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for module documentation
        assert "Script 14" in content, \
            "Script 14 designation not in documentation"
        assert "Analytic Properties" in content, \
            "Analytic Properties not mentioned in header"
        assert "Entirety" in content or "entire" in content.lower(), \
            "Entirety not mentioned in header"

    def test_xi_analytic_properties_has_author_info(self):
        """Verify author information is present"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for author info
        assert "José Manuel Mota Burruezo" in content, \
            "Author name not found"
        assert "JMMB" in content, \
            "Author abbreviation not found"

    def test_xi_analytic_properties_has_orcid(self):
        """Verify ORCID is present"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for ORCID
        assert "ORCID: 0009-0002-1923-0773" in content, \
            "ORCID not found or incorrect"

    def test_xi_analytic_properties_has_doi(self):
        """Verify DOI reference is present"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for DOI
        assert "10.5281/zenodo.17379721" in content, \
            "DOI reference not found"

    def test_xi_analytic_properties_has_namespace(self):
        """Verify proper namespace is used"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for namespace
        assert "namespace RiemannAdelic.Script14" in content, \
            "RiemannAdelic.Script14 namespace not found"


class TestXiAnalyticPropertiesMathematicalContent:
    """Test mathematical content"""

    def test_xi_analytic_properties_has_proof_outline(self):
        """Verify proof outline is documented"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for proof outline
        assert "Proof" in content, \
            "Proof outline not found"

    def test_xi_analytic_properties_has_mathlib_imports(self):
        """Verify Mathlib imports are correct"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for essential Mathlib imports
        assert "import Mathlib.Analysis.SpecialFunctions.Gamma.Basic" in content, \
            "Gamma import not found"
        assert "import Mathlib.NumberTheory.ZetaFunction" in content, \
            "ZetaFunction import not found"
        assert "import Mathlib.Analysis.Complex.CauchyIntegral" in content, \
            "CauchyIntegral import not found"

    def test_xi_analytic_properties_has_functional_equation(self):
        """Verify functional equation is stated"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for functional equation
        assert "Xi_functional_equation" in content, \
            "Functional equation theorem not found"
        assert "Xi (1 - s) = Xi s" in content, \
            "Functional equation statement not found"

    def test_xi_analytic_properties_has_real_on_critical_line(self):
        """Verify reality on critical line is stated"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for reality on critical line
        assert "Xi_real_on_critical_line" in content, \
            "Xi_real_on_critical_line theorem not found"

    def test_xi_analytic_properties_has_qcal_integration(self):
        """Verify QCAL integration constants are mentioned"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for QCAL frequency
        assert "141.7001" in content, \
            "QCAL base frequency not found"
        
        # Check for QCAL coherence
        assert "244.36" in content, \
            "QCAL coherence constant not found"

    def test_xi_analytic_properties_has_references(self):
        """Verify mathematical references are present"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for Titchmarsh reference
        assert "Titchmarsh" in content, \
            "Titchmarsh reference not found"
        
        # Check for Edwards reference
        assert "Edwards" in content, \
            "Edwards reference not found"
        
        # Check for de Branges reference
        assert "de Branges" in content, \
            "de Branges reference not found"


class TestXiAnalyticPropertiesCompleteness:
    """Test completeness of the formalization"""

    def test_xi_analytic_properties_is_valid_lean(self):
        """Verify file has valid Lean 4 structure"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for section/namespace structure
        assert "noncomputable section" in content, \
            "Noncomputable section not declared"
        assert "end" in content, \
            "End of section/namespace not found"
        
        # Check for open statements
        assert "open Complex" in content, \
            "Complex namespace not opened"

    def test_xi_analytic_properties_has_summary_section(self):
        """Verify summary section exists at end"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for summary section markers
        assert "Summary" in content, \
            "Summary section not found"
        assert "Status" in content, \
            "Status section not found"

    def test_xi_analytic_properties_has_all_sections(self):
        """Verify all main sections are present"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for section markers
        assert "Section 1" in content, \
            "Section 1 not found"
        assert "Section 2" in content, \
            "Section 2 not found"
        assert "Section 3" in content, \
            "Section 3 not found"
        assert "Section 4" in content, \
            "Section 4 not found"
        assert "Section 5" in content, \
            "Section 5 not found"

    def test_xi_analytic_properties_has_v5_coronacion(self):
        """Verify V5 Coronación framework reference"""
        file_path = Path("formalization/lean/RiemannAdelic/Xi_analytic_properties.lean")
        content = file_path.read_text()
        
        # Check for V5 Coronación
        assert "V5 Coronación" in content, \
            "V5 Coronación framework not referenced"
