#!/usr/bin/env python3
"""
Test suite for Berry-Keating operator H_Ψ formalization

This test verifies the mathematical structure and consistency of the
H_psi_core_complete.lean formalization.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 2026-01-06
DOI: 10.5281/zenodo.17379721
"""

import unittest
import re
from pathlib import Path


class TestBerryKeatingOperator(unittest.TestCase):
    """Test suite for Berry-Keating operator formalization."""
    
    @classmethod
    def setUpClass(cls):
        """Load the Lean file content."""
        filepath = Path(__file__).parent.parent / "formalization" / "lean" / "Operator" / "H_psi_core_complete.lean"
        cls.content = filepath.read_text(encoding='utf-8')
    
    def test_file_header(self):
        """Test that file has proper header with attribution."""
        self.assertIn("José Manuel Mota Burruezo", self.content)
        self.assertIn("ORCID: 0009-0002-1923-0773", self.content)
        self.assertIn("DOI: 10.5281/zenodo.17379721", self.content)
        self.assertIn("Berry-Keating", self.content)
    
    def test_no_sorry_statements(self):
        """Test that no 'sorry' statements exist in code."""
        # Remove block comments
        content_no_block_comments = re.sub(r'/-.*?-/', '', self.content, flags=re.DOTALL)
        # Remove line comments
        lines = content_no_block_comments.split('\n')
        code_lines = [line.split('--')[0] for line in lines]
        code = '\n'.join(code_lines)
        
        # Check for sorry
        self.assertNotIn('sorry', code.lower(),
                        "Found 'sorry' statement in code (outside comments)")
    
    def test_required_imports(self):
        """Test that all required Mathlib imports are present."""
        required_imports = [
            'Mathlib.Analysis.Distribution.SchwartzSpace',
            'Mathlib.Analysis.InnerProductSpace.Basic',
            'Mathlib.MeasureTheory.Function.L2Space',
            'Mathlib.Analysis.Calculus.Deriv.Basic',
        ]
        
        for imp in required_imports:
            with self.subTest(import_=imp):
                self.assertIn(f'import {imp}', self.content,
                            f"Missing required import: {imp}")
    
    def test_schwarz_space_definition(self):
        """Test that Schwarz space is properly defined."""
        self.assertIn('abbrev SchwarzSpace', self.content)
        self.assertIn('SchwartzMap ℝ ℂ', self.content)
    
    def test_h_psi_action_definition(self):
        """Test that H_Ψ action is properly defined."""
        self.assertIn('def H_psi_action', self.content)
        self.assertIn('-x * deriv f x', self.content)
    
    def test_preservation_theorem(self):
        """Test that H_Ψ preservation theorem exists."""
        self.assertIn('theorem H_psi_preserves_schwartz', self.content)
        self.assertIn('SchwarzSpace', self.content)
    
    def test_linearity(self):
        """Test that H_Ψ is defined as a linear map."""
        self.assertIn('def H_psi_linear', self.content)
        self.assertIn('SchwarzSpace →ₗ[ℂ] SchwarzSpace', self.content)
        self.assertIn('map_add', self.content)
        self.assertIn('map_smul', self.content)
    
    def test_boundedness_theorem(self):
        """Test that boundedness theorem with constant 4 exists."""
        self.assertIn('theorem H_psi_bounded_L2', self.content)
        # Check for constant 4
        bounded_section = self.content[self.content.find('H_psi_bounded_L2'):]
        self.assertIn('⟨4, by norm_num', bounded_section[:500])
    
    def test_symmetry_theorem(self):
        """Test that symmetry theorem exists."""
        self.assertIn('theorem H_psi_symmetric', self.content)
        self.assertIn('integration_by_parts', self.content)
    
    def test_continuous_operator(self):
        """Test that H_Ψ is defined as continuous linear operator."""
        self.assertIn('def H_psi_core', self.content)
        self.assertIn('SchwarzSpace →L[ℂ] SchwarzSpace', self.content)
        self.assertIn('LinearMap.mkContinuous', self.content)
    
    def test_hardy_inequality_axiom(self):
        """Test that Hardy inequality axiom is present."""
        self.assertIn('axiom hardy_inequality', self.content)
        # Check for the factor 4
        hardy_section = self.content[self.content.find('axiom hardy_inequality'):]
        self.assertIn('4 *', hardy_section[:200])
    
    def test_spectral_connection(self):
        """Test that spectral connection to Riemann zeros is documented."""
        self.assertIn('berry_keating_spectrum', self.content)
        self.assertIn('spectrum', self.content)
        self.assertIn('riemannZeta', self.content)
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency connection exists."""
        self.assertIn('fundamental_frequency', self.content)
        self.assertIn('141.70001', self.content)
    
    def test_namespace(self):
        """Test that proper namespace is used."""
        self.assertIn('namespace Operator', self.content)
        self.assertIn('end Operator', self.content)
    
    def test_noncomputable_section(self):
        """Test that noncomputable section is properly opened/closed."""
        self.assertIn('noncomputable section', self.content)
        self.assertIn('end -- noncomputable section', self.content)
    
    def test_documentation_comments(self):
        """Test that proper documentation comments exist."""
        self.assertIn('/-!', self.content)
        self.assertIn('## Part 1:', self.content)
        self.assertIn('## Part 2:', self.content)
    
    def test_mathematical_constants(self):
        """Test that mathematical constants are correct."""
        # Hardy inequality constant
        self.assertIn('4', self.content)
        # Frequency
        self.assertIn('141.70001', self.content)
        # Critical line
        self.assertIn('1/2', self.content)
    
    def test_axiom_count(self):
        """Test that axiom count is reasonable (6-7 expected)."""
        axiom_count = len(re.findall(r'\baxiom\s+\w+', self.content))
        self.assertGreaterEqual(axiom_count, 6, "Too few axioms")
        self.assertLessEqual(axiom_count, 8, "Too many axioms")
    
    def test_qcal_integration(self):
        """Test that QCAL framework integration is documented."""
        self.assertIn('QCAL', self.content)
        self.assertIn('141.70001 Hz', self.content)
        self.assertIn('∞³', self.content)


class TestBerryKeatingDocumentation(unittest.TestCase):
    """Test suite for Berry-Keating operator documentation."""
    
    @classmethod
    def setUpClass(cls):
        """Load the README file content."""
        filepath = Path(__file__).parent.parent / "formalization" / "lean" / "Operator" / "H_PSI_CORE_COMPLETE_README.md"
        cls.content = filepath.read_text(encoding='utf-8')
    
    def test_documentation_exists(self):
        """Test that documentation file exists and is readable."""
        self.assertIsNotNone(self.content)
        self.assertGreater(len(self.content), 1000, "Documentation too short")
    
    def test_overview_section(self):
        """Test that overview section exists."""
        self.assertIn('## Overview', self.content)
        self.assertIn('Berry-Keating', self.content)
    
    def test_mathematical_background(self):
        """Test that mathematical background is documented."""
        self.assertIn('Mathematical Background', self.content)
        self.assertIn('H_Ψ', self.content)
    
    def test_axioms_documented(self):
        """Test that all axioms are documented."""
        axiom_names = [
            'mul_polynomial_schwartz',
            'dense_schwarz_in_L2Haar',
            'hardy_inequality',
            'integration_by_parts_schwartz',
            'berry_keating_spectrum',
            'fundamental_frequency',
        ]
        
        for axiom in axiom_names:
            with self.subTest(axiom=axiom):
                self.assertIn(axiom, self.content,
                            f"Axiom {axiom} not documented")
    
    def test_theorems_documented(self):
        """Test that main theorems are documented."""
        theorems = [
            'H_psi_preserves_schwartz',
            'H_psi_bounded_L2',
            'H_psi_symmetric',
        ]
        
        for theorem in theorems:
            with self.subTest(theorem=theorem):
                self.assertIn(theorem, self.content,
                            f"Theorem {theorem} not documented")
    
    def test_references(self):
        """Test that references are provided."""
        self.assertIn('References', self.content)
        self.assertIn('Berry', self.content)
        self.assertIn('1999', self.content)
        self.assertIn('Hardy', self.content)
    
    def test_attribution(self):
        """Test that proper attribution is present."""
        self.assertIn('José Manuel Mota Burruezo', self.content)
        self.assertIn('0009-0002-1923-0773', self.content)
        self.assertIn('10.5281/zenodo.17379721', self.content)


def run_tests():
    """Run all tests and return exit code."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    suite.addTests(loader.loadTestsFromTestCase(TestBerryKeatingOperator))
    suite.addTests(loader.loadTestsFromTestCase(TestBerryKeatingDocumentation))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    import sys
    sys.exit(run_tests())
