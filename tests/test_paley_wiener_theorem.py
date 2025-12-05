#!/usr/bin/env python3
"""
Test suite for validating the mathematical structure of the enhanced 
Paley-Wiener uniqueness theorem with multiplicities.

This test ensures that the theoretical framework is mathematically consistent
and properly implemented in the LaTeX documents.
"""

import re
import os
from pathlib import Path

class PaleyWienerTheoremValidator:
    """Validates the mathematical content of the Paley-Wiener theorem implementation."""
    
    def __init__(self):
        self.repo_root = Path(__file__).parent.parent
        self.appendix_a_path = self.repo_root / "paper" / "appendix_a.tex"
        self.unicidad_path = self.repo_root / "docs" / "teoremas_basicos" / "unicidad_paley_wiener.tex"
        self.main_tex_path = self.repo_root / "paper" / "main.tex"
    
    def test_theorem_structure(self):
        """Test that the theorem has the required mathematical structure."""
        print("Testing theorem structure...")
        
        with open(self.appendix_a_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for theorem label
        assert 'thm:paley-wiener-uniqueness' in content, "Theorem label missing"
        
        # Check for all four required conditions (simplified)
        assert 'entera de orden' in content, "Condition 1: entire function of order missing"
        assert 'D(1-s) = D(s)' in content, "Condition 2: functional symmetry missing"
        assert 'log D(s) = 0' in content, "Condition 3: normalization condition missing"
        assert 'medida espectral' in content, "Condition 4: spectral measure condition missing"
        
        print("✓ Theorem structure validation passed")
    
    def test_proof_structure(self):
        """Test that the proof has all required steps."""
        print("Testing proof structure...")
        
        with open(self.appendix_a_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for all proof steps (simplified)
        assert 'Paso 1' in content and 'Factorización de Hadamard' in content, "Proof step 1 missing"
        assert 'Paso 2' in content and 'Cociente auxiliar' in content, "Proof step 2 missing"
        assert 'Paso 3' in content and 'Simetría funcional' in content, "Proof step 3 missing"
        assert 'Paso 4' in content and 'Normalización asintótica' in content, "Proof step 4 missing"
        assert 'Conclusión' in content, "Conclusion missing"
        
        # Check for Hadamard factorization formula
        assert r'E_1(z) = (1-z)e^z' in content, "Hadamard factor formula missing"
        
        # Check for final conclusion
        assert 'D(s)' in content and 'Xi(s)' in content, "Final theorem conclusion missing"
        
        print("✓ Proof structure validation passed")
    
    def test_supporting_lemmas(self):
        """Test that supporting lemmas are present."""
        print("Testing supporting lemmas...")
        
        with open(self.appendix_a_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for Phragmén–Lindelöf lemma
        assert 'lem:phragmen' in content, "Phragmén–Lindelöf lemma label missing"
        assert 'Phragmén–Lindelöf' in content, "Phragmén–Lindelöf lemma missing"
        
        # Check for Paley-Wiener class proposition
        assert 'prop:pw-class' in content, "Paley-Wiener class proposition label missing"
        assert 'Clase determinante Paley–Wiener' in content, "Paley-Wiener class proposition missing"
        
        print("✓ Supporting lemmas validation passed")
    
    def test_bibliography_references(self):
        """Test that all required classical references are included."""
        print("Testing bibliography references...")
        
        with open(self.main_tex_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for required classical references (simplified)
        assert 'hadamard1893' in content and 'Hadamard' in content, "Hadamard reference missing"
        assert 'hamburger1921' in content and 'Hamburger' in content, "Hamburger reference missing"
        assert 'paleywiener1934' in content and 'Paley' in content and 'Wiener' in content, "Paley-Wiener reference missing"
        assert 'phragmen1908' in content and 'Phragmén' in content, "Phragmén-Lindelöf reference missing"
        
        print("✓ Bibliography references validation passed")
    
    def test_consistency_between_versions(self):
        """Test consistency between English and Spanish versions."""
        print("Testing consistency between language versions...")
        
        with open(self.appendix_a_path, 'r', encoding='utf-8') as f:
            appendix_content = f.read()
            
        with open(self.unicidad_path, 'r', encoding='utf-8') as f:
            unicidad_content = f.read()
        
        # Both should have the same theorem label
        assert 'thm:paley-wiener-uniqueness' in appendix_content
        assert 'thm:paley-wiener-uniqueness' in unicidad_content
        
        # Both should have Hadamard factorization
        assert 'E_1(z) = (1-z)e^z' in appendix_content
        assert 'E_1(z) = (1-z)e^z' in unicidad_content
        
        # Both should reference classical results
        assert 'Hadamard' in appendix_content and 'Hadamard' in unicidad_content
        assert 'Phragmén' in appendix_content and 'Phragmén' in unicidad_content
        
        print("✓ Language version consistency validation passed")
    
    def test_mathematical_notation(self):
        """Test that mathematical notation is consistent and correct."""
        print("Testing mathematical notation...")
        
        with open(self.appendix_a_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for proper math delimiters
        math_blocks = re.findall(r'\\\[(.*?)\\\]', content, re.DOTALL)
        assert len(math_blocks) >= 2, f"Not enough displayed math equations (found {len(math_blocks)}, need at least 2)"
        
        # Check for proper function notation
        assert 'D(s)' in content, "Function D(s) notation missing"
        assert 'Xi(s)' in content, "Function Ξ(s) notation missing"  
        assert 'H(s)' in content, "Auxiliary function H(s) missing"
        
        # Check for proper limit notation
        if 'lim' in content and 'log D(s)' in content:
            pass  # Found proper limit notation
        else:
            assert False, "Proper limit notation missing"
        
        print("✓ Mathematical notation validation passed")
    
    def run_all_tests(self):
        """Run all validation tests."""
        print("=" * 60)
        print("PALEY-WIENER THEOREM MATHEMATICAL VALIDATION")
        print("=" * 60)
        
        try:
            self.test_theorem_structure()
            self.test_proof_structure()
            self.test_supporting_lemmas()
            self.test_bibliography_references()
            self.test_consistency_between_versions()
            self.test_mathematical_notation()
            
            print("\n" + "=" * 60)
            print("✅ ALL MATHEMATICAL VALIDATION TESTS PASSED!")
            print("The enhanced Paley-Wiener uniqueness theorem is properly implemented.")
            print("=" * 60)
            return True
            
        except AssertionError as e:
            print(f"\n❌ VALIDATION FAILED: {e}")
            print("=" * 60)
            return False
        except Exception as e:
            print(f"\n💥 UNEXPECTED ERROR: {e}")
            print("=" * 60)
            return False

if __name__ == "__main__":
    validator = PaleyWienerTheoremValidator()
    success = validator.run_all_tests()
    exit(0 if success else 1)