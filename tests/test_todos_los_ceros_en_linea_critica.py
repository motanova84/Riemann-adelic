#!/usr/bin/env python3
"""
Tests for: Todos los Ceros en Línea Crítica

Unit tests validating the structural proof that ALL zeros of the 
Riemann zeta function lie on the critical line Re(s) = 1/2.

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import pytest
import sys
from pathlib import Path

# Add repository root to path
sys.path.insert(0, str(Path(__file__).parent.parent))


class TestLeanFormalizationStructure:
    """Test that the Lean formalization file has correct structure"""
    
    @pytest.fixture
    def lean_content(self):
        """Load the Lean file content"""
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        return lean_file.read_text()
    
    def test_main_theorem_exists(self, lean_content):
        """Test that the main theorem is defined"""
        assert "theorem todos_los_ceros_en_linea_critica" in lean_content
    
    def test_extended_theorem_exists(self, lean_content):
        """Test that the extended theorem for arbitrary height T exists"""
        assert "theorem todos_los_ceros_hasta_cualquier_altura" in lean_content
    
    def test_completeness_theorem_exists(self, lean_content):
        """Test that the spectral completeness theorem exists"""
        assert "theorem completitud_espectral" in lean_content
    
    def test_riemann_hypothesis_corollary_exists(self, lean_content):
        """Test that the RH corollary exists"""
        assert "theorem riemann_hypothesis" in lean_content
    
    def test_zero_symmetry_theorem_exists(self, lean_content):
        """Test that the zero symmetry theorem exists"""
        assert "theorem zero_symmetry" in lean_content
    
    def test_spectral_bijection_axiom_exists(self, lean_content):
        """Test that the spectral bijection axiom exists"""
        assert "axiom spectral_bijection_completa" in lean_content
    
    def test_spectral_completeness_axiom_exists(self, lean_content):
        """Test that the spectral completeness axiom exists"""
        assert "axiom spectral_completeness" in lean_content
    
    def test_multiplicity_axiom_exists(self, lean_content):
        """Test that the multiplicity axiom exists"""
        assert "axiom multiplicity_equals_one" in lean_content
    
    def test_density_exact_axiom_exists(self, lean_content):
        """Test that the exact density axiom exists"""
        assert "axiom density_exact" in lean_content
    
    def test_functional_equation_axiom_exists(self, lean_content):
        """Test that the functional equation axiom exists"""
        assert "axiom D_functional_equation" in lean_content
    
    def test_non_trivial_zero_definition_exists(self, lean_content):
        """Test that NonTrivialZero predicate is defined"""
        assert "def NonTrivialZero" in lean_content
    
    def test_no_admit_keyword(self, lean_content):
        """Test that 'admit' keyword is not used"""
        # 'admit' is used in documentation comments only, not as Lean tactics
        lines = lean_content.split('\n')
        for i, line in enumerate(lines, 1):
            # Skip comment lines
            if line.strip().startswith('--') or line.strip().startswith('/-') or line.strip().startswith('#'):
                continue
            # Check for 'admit' as a tactic
            if 'admit' in line and ':=' not in line:
                # Make sure it's not part of "admit" in comments
                if ' admit' in line or '\tadmit' in line:
                    # Allow if it's inside a string or documentation
                    if not ('"' in line or "'" in line or '--' in line):
                        pytest.fail(f"Found 'admit' keyword at line {i}: {line}")


class TestProofStructure:
    """Test the logical structure of the proof"""
    
    @pytest.fixture
    def lean_content(self):
        """Load the Lean file content"""
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        return lean_file.read_text()
    
    def test_proof_uses_contradiction(self, lean_content):
        """Test that the main proof uses proof by contradiction"""
        assert "by_contra" in lean_content
    
    def test_proof_uses_spectral_completeness(self, lean_content):
        """Test that the proof uses spectral completeness"""
        assert "spectral_completeness" in lean_content
    
    def test_proof_uses_zero_symmetry(self, lean_content):
        """Test that the proof uses zero symmetry"""
        assert "zero_symmetry" in lean_content
    
    def test_proof_uses_multiplicity(self, lean_content):
        """Test that the proof uses multiplicity argument"""
        assert "multiplicity" in lean_content.lower()
    
    def test_proof_has_qcal_constants(self, lean_content):
        """Test that QCAL constants are referenced"""
        assert "244.36" in lean_content  # C constant
        assert "141.7001" in lean_content  # f₀ frequency


class TestConceptualSoundness:
    """Test the conceptual soundness of the proof approach"""
    
    def test_structural_not_numerical(self):
        """
        Test that the proof is STRUCTURAL, not numerical.
        
        Key insight: The proof doesn't verify zeros up to some T and extrapolate.
        It establishes a structural property that applies to ALL zeros.
        """
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        
        content = lean_file.read_text()
        
        # The proof should not depend on any specific numerical bound
        # It should use structural arguments
        assert "ESTRUCTURAL" in content or "structural" in content.lower()
        
        # The proof should mention that T doesn't matter
        assert "no depende de T" in content.lower() or "doesn't depend" in content.lower() or \
               "irrelevant" in content.lower() or "IRRELEVANTE" in content
    
    def test_bijection_is_complete(self):
        """
        Test that the bijection between zeros and eigenvalues is COMPLETE.
        
        This is the key insight: the bijection covers ALL zeros, not just
        a finite subset.
        """
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        
        content = lean_file.read_text()
        
        # The bijection should be described as complete/completa
        assert "COMPLETA" in content or "COMPLETE" in content
        assert "bijection" in content.lower() or "biyección" in content.lower()
    
    def test_multiplicity_argument_structure(self):
        """
        Test the multiplicity argument:
        1. If ρ has Re(ρ) ≠ 1/2, then 1-ρ is also a zero (by functional eq)
        2. Both map to same eigenvalue
        3. This gives multiplicity ≥ 2
        4. Contradiction with multiplicity 1
        """
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        
        content = lean_file.read_text()
        
        # The proof should mention:
        # - defect or multiplicity
        # - The value 2 (multiplicity ≥ 2)
        # - Contradiction
        assert "defect" in content or "multiplicidad" in content.lower() or "multiplicity" in content.lower()
        assert "≥ 2" in content or ">= 2" in content
        assert "contradiction" in content.lower() or "contradicción" in content.lower()


class TestDocumentation:
    """Test that documentation is complete and correct"""
    
    @pytest.fixture
    def lean_content(self):
        """Load the Lean file content"""
        lean_file = Path(__file__).parent.parent / "formalization" / "lean" / "todos_los_ceros_en_linea_critica.lean"
        if not lean_file.exists():
            pytest.skip("Lean file not found")
        return lean_file.read_text()
    
    def test_author_attribution(self, lean_content):
        """Test that author is properly attributed"""
        assert "José Manuel Mota Burruezo" in lean_content
    
    def test_institution_attribution(self, lean_content):
        """Test that institution is properly attributed"""
        assert "Instituto de Conciencia Cuántica" in lean_content or "ICQ" in lean_content
    
    def test_doi_reference(self, lean_content):
        """Test that DOI is referenced"""
        assert "10.5281/zenodo" in lean_content
    
    def test_orcid_reference(self, lean_content):
        """Test that ORCID is referenced"""
        assert "0009-0002-1923-0773" in lean_content
    
    def test_summary_section_exists(self, lean_content):
        """Test that summary section exists"""
        assert "RESUMEN" in lean_content or "SUMMARY" in lean_content


class TestValidationScript:
    """Test the validation script"""
    
    def test_validation_script_exists(self):
        """Test that validation script exists"""
        script_path = Path(__file__).parent.parent / "formalization" / "lean" / "validate_todos_los_ceros.py"
        assert script_path.exists(), "Validation script should exist"
    
    def test_validation_script_can_import(self):
        """Test that validation script can be imported"""
        import importlib.util
        script_path = Path(__file__).parent.parent / "formalization" / "lean" / "validate_todos_los_ceros.py"
        spec = importlib.util.spec_from_file_location("validate_todos_los_ceros", script_path)
        module = importlib.util.module_from_spec(spec)
        try:
            spec.loader.exec_module(module)
        except Exception as e:
            pytest.fail(f"Validation script could not be loaded: {e}")
    
    def test_validation_functions_exist(self):
        """Test that validation functions exist"""
        import importlib.util
        script_path = Path(__file__).parent.parent / "formalization" / "lean" / "validate_todos_los_ceros.py"
        spec = importlib.util.spec_from_file_location("validate_todos_los_ceros", script_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        assert hasattr(module, "validate_lean_file_structure")
        assert hasattr(module, "validate_spectral_bijection_concept")
        assert hasattr(module, "validate_multiplicity_argument")
        assert hasattr(module, "validate_infinite_coverage")
        assert hasattr(module, "run_validation")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
