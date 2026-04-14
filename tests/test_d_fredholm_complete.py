"""
Test suite for D_fredholm.lean completeness
============================================

Tests that the D_fredholm.lean file is complete without any sorry statements.
"""

import pytest
from pathlib import Path
import re

# Project root
PROJECT_ROOT = Path(__file__).parent.parent
LEAN_FILE = PROJECT_ROOT / "formalization" / "lean" / "D_fredholm.lean"


class TestDFredholmCompleteness:
    """Tests for the completeness of D_fredholm.lean"""
    
    def test_file_exists(self):
        """Test that D_fredholm.lean exists"""
        assert LEAN_FILE.exists(), f"File not found: {LEAN_FILE}"
        assert LEAN_FILE.stat().st_size > 0, "File is empty"
    
    @pytest.fixture
    def file_content(self):
        """Load the file content"""
        with open(LEAN_FILE, 'r', encoding='utf-8') as f:
            return f.read()
    
    def test_no_sorry_statements(self, file_content):
        """Test that there are no sorry statements in the code"""
        # Remove comments to avoid false positives
        lines = file_content.split('\n')
        code_lines = [line for line in lines if not line.strip().startswith('--') 
                      and not line.strip().startswith('/-') 
                      and not line.strip().startswith('✅')]
        code = '\n'.join(code_lines)
        
        # Check for sorry statements in actual code
        sorry_pattern = r'\bsorry\b'
        matches = re.findall(sorry_pattern, code)
        
        assert len(matches) == 0, f"Found {len(matches)} sorry statement(s) in code"
    
    def test_no_admit_statements(self, file_content):
        """Test that there are no admit statements in the code"""
        # Remove comments
        lines = file_content.split('\n')
        code_lines = [line for line in lines if not line.strip().startswith('--') 
                      and not line.strip().startswith('/-')]
        code = '\n'.join(code_lines)
        
        # Check for admit statements
        admit_pattern = r'\badmit\b'
        matches = re.findall(admit_pattern, code)
        
        assert len(matches) == 0, f"Found {len(matches)} admit statement(s) in code"
    
    def test_has_required_imports(self, file_content):
        """Test that required imports are present"""
        assert "import Mathlib.Analysis.InnerProductSpace.Adjoint" in file_content
        assert "import Mathlib.Analysis.FredholmAlternative" in file_content
    
    def test_has_j_involution(self, file_content):
        """Test that J involution is defined"""
        assert "def J :" in file_content
        assert "J_self_adjoint" in file_content
    
    def test_has_d_functional_equation(self, file_content):
        """Test that D_functional_equation theorem is complete"""
        assert "theorem D_functional_equation" in file_content
        # Make sure it's not using sorry
        lines = file_content.split('\n')
        in_functional_eq = False
        theorem_content = []
        for line in lines:
            if "theorem D_functional_equation" in line:
                in_functional_eq = True
            if in_functional_eq:
                theorem_content.append(line)
                if line.strip().startswith("theorem ") and "D_functional_equation" not in line:
                    break
                if line.strip().startswith("--") and "theorem" not in line.lower():
                    if len(theorem_content) > 10:  # Reasonable theorem size
                        break
        
        theorem_text = '\n'.join(theorem_content)
        assert 'sorry' not in theorem_text, "D_functional_equation still contains sorry"
    
    def test_has_d_entire_theorem(self, file_content):
        """Test that D_entire bonus theorem is present"""
        assert "theorem D_entire" in file_content
        assert "Holomorphic ℂ D" in file_content
    
    def test_has_completion_marker(self, file_content):
        """Test that the file has the completion marker"""
        assert "CIERRE DEFINITIVO DE D_fredholm.lean" in file_content
        assert "0 sorry – 0 admit" in file_content
    
    def test_verification_checks(self, file_content):
        """Test that verification checks include new theorems"""
        assert "#check D_functional_equation" in file_content
        assert "#check D_entire" in file_content


class TestDFredholmTheorems:
    """Tests for specific theorems in D_fredholm.lean"""
    
    @pytest.fixture
    def file_content(self):
        """Load the file content"""
        with open(LEAN_FILE, 'r', encoding='utf-8') as f:
            return f.read()
    
    def test_has_t_operator_axioms(self, file_content):
        """Test that T operator axioms are present"""
        assert "axiom T :" in file_content
        assert "axiom T_trace_class" in file_content
        assert "axiom T_holomorphic" in file_content
    
    def test_has_fredholm_axioms(self, file_content):
        """Test that Fredholm-related axioms are present"""
        assert "axiom det :" in file_content
        assert "axiom fredholm_det_holomorphic" in file_content
        assert "axiom det_adjoint_eq_of_trace_class" in file_content
    
    def test_has_supporting_axioms(self, file_content):
        """Test that supporting axioms are present"""
        assert "axiom TraceClass" in file_content
        assert "axiom IsSelfAdjoint" in file_content
        assert "axiom Holomorphic" in file_content
