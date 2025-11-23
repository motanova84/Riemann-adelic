"""
Test suite for J composition theorem
====================================

Tests the J operator composition theorem implementation in Lean 4.
"""

import pytest
import sys
from pathlib import Path
import subprocess

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestJCompositionTheorem:
    """Tests for J composition theorem in Lean formalization"""
    
    def test_j_composition_file_exists(self):
        """Test that the J composition theorem file exists"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        assert j_file.exists(), f"J composition theorem file not found: {j_file}"
        assert j_file.stat().st_size > 0, "J composition theorem file is empty"
    
    def test_j_composition_has_correct_definition(self):
        """Test that J is defined with the correct formula: J(f)(x) = (1/x) * f(1/x)"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for the J operator definition
        assert "def J (f : ℝ → ℂ) : ℝ → ℂ" in content, "J operator definition not found"
        assert "(1 / x) * f (1 / x)" in content, "J operator formula incorrect"
    
    def test_j_composition_has_main_theorem(self):
        """Test that the main theorem J_squared_eq_id is present"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for the main theorem
        assert "theorem J_squared_eq_id" in content, "Main theorem J_squared_eq_id not found"
        assert "(J ∘ J) f x = f x" in content, "Theorem statement incorrect"
    
    def test_j_composition_theorem_proof_complete(self):
        """Test that the theorem proof is complete (no sorry)"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check that there are no sorry placeholders
        assert "sorry" not in content.lower(), "Theorem has incomplete proofs (sorry found)"
    
    def test_j_composition_uses_correct_tactics(self):
        """Test that the proof uses the correct tactics from the problem statement"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for required tactics and lemmas
        assert "Function.comp_apply" in content, "Missing Function.comp_apply"
        assert "one_div_div" in content, "Missing one_div_div lemma"
        assert "one_div_one_div" in content, "Missing one_div_one_div lemma"
        assert "field_simp" in content, "Missing field_simp tactic"
    
    def test_j_composition_imported_in_main(self):
        """Test that J_composition_theorem is imported in Main.lean"""
        main_file = PROJECT_ROOT / "formalization" / "lean" / "Main.lean"
        content = main_file.read_text()
        
        assert "import RiemannAdelic.J_composition_theorem" in content, \
            "J_composition_theorem not imported in Main.lean"
    
    def test_j_composition_validates_successfully(self):
        """Test that the J composition theorem validates successfully"""
        validation_script = PROJECT_ROOT / "validate_lean_formalization.py"
        result = subprocess.run(
            [sys.executable, str(validation_script)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True
        )
        
        # Should exit with 0 (success)
        assert result.returncode == 0, f"Validation failed: {result.stderr}"
        
        # Check that J_composition_theorem appears in validation output
        assert "J_composition_theorem" in result.stdout, \
            "J_composition_theorem not found in validation output"
        
        # Check that it has 0 sorries
        assert "J_composition_theorem.lean: 3 theorems, 0 axioms, 0 sorry" in result.stdout, \
            "J_composition_theorem validation incorrect"
    
    def test_j_composition_has_documentation(self):
        """Test that the file has proper documentation"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for documentation sections
        assert "/-" in content, "Missing documentation block"
        assert "Author:" in content, "Missing author information"
        assert "DOI:" in content, "Missing DOI reference"
        
        # Check for theorem documentation
        assert "/--" in content, "Missing theorem docstring"
    
    def test_j_composition_has_involutive_property(self):
        """Test that the involutive property theorem is present"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for involutive property
        assert "theorem J_involutive" in content or "lemma J_involutive" in content, \
            "J_involutive theorem not found"
    
    def test_j_composition_namespace(self):
        """Test that the file uses the correct namespace"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check namespace
        assert "namespace RiemannAdelic" in content, "Missing or incorrect namespace"
        assert "end RiemannAdelic" in content, "Namespace not properly closed"


class TestJCompositionMathematicalProperties:
    """Tests for mathematical properties of the J operator"""
    
    def test_j_operator_domain(self):
        """Test that J operates on positive reals"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check that the theorem specifies x > 0
        assert "x > 0" in content, "Missing domain restriction x > 0"
    
    def test_j_composition_has_calc_proof(self):
        """Test that the proof uses calc mode as specified"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for calc proof structure
        assert "calc" in content, "Proof should use calc mode"
    
    def test_j_composition_correctness_notes(self):
        """Test that mathematical correctness notes are present"""
        j_file = PROJECT_ROOT / "formalization" / "lean" / "RiemannAdelic" / "J_composition_theorem.lean"
        content = j_file.read_text()
        
        # Check for mathematical explanation
        assert "Riemann" in content or "functional equation" in content, \
            "Missing connection to Riemann hypothesis"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
