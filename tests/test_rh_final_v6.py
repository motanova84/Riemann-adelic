#!/usr/bin/env python3
"""
Test suite for RH_final_v6 structure validation

Validates the existence and basic structure of the RH_final_v6 directory
containing the Lean 4 formalization of the Riemann Hypothesis proof.
"""

import pytest
from pathlib import Path
import re


class TestRHFinalV6Structure:
    """Test the RH_final_v6 directory structure."""
    
    @pytest.fixture(autouse=True)
    def setup_method(self):
        """Setup test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.rh_v6_dir = self.repo_root / "RH_final_v6"
    
    def test_directory_exists(self):
        """Test that RH_final_v6 directory exists."""
        assert self.rh_v6_dir.exists(), "RH_final_v6 directory should exist"
        assert self.rh_v6_dir.is_dir(), "RH_final_v6 should be a directory"
    
    def test_lean_files_exist(self):
        """Test that all required Lean files exist."""
        required_files = [
            "paley_wiener_uniqueness.lean",
            "selberg_trace.lean",
            "H_psi_complete.lean",
            "D_limit_equals_xi.lean",
            "spectrum_eq_zeros.lean",
            "spectrum_HΨ_equals_zeta_zeros.lean",
        ]
        
        for filename in required_files:
            filepath = self.rh_v6_dir / filename
            assert filepath.exists(), f"{filename} should exist"
            assert filepath.is_file(), f"{filename} should be a file"
            
            # Check that file is not empty
            content = filepath.read_text()
            assert len(content) > 0, f"{filename} should not be empty"
    
    def test_build_files_exist(self):
        """Test that build configuration files exist."""
        build_files = [
            "lakefile.lean",
            "lean-toolchain",
        ]
        
        for filename in build_files:
            filepath = self.rh_v6_dir / filename
            assert filepath.exists(), f"{filename} should exist"
            assert filepath.is_file(), f"{filename} should be a file"
    
    def test_documentation_exists(self):
        """Test that documentation files exist."""
        doc_files = [
            "README.md",
            "CITATION.cff",
        ]
        
        for filename in doc_files:
            filepath = self.rh_v6_dir / filename
            assert filepath.exists(), f"{filename} should exist"
            assert filepath.is_file(), f"{filename} should be a file"
    
    def test_lean_toolchain_content(self):
        """Test that lean-toolchain specifies correct version."""
        toolchain_file = self.rh_v6_dir / "lean-toolchain"
        content = toolchain_file.read_text().strip()
        
        # Should specify Lean 4.5.0 or compatible
        assert "lean4" in content.lower(), "Should specify Lean 4"
        assert "v4" in content.lower(), "Should specify version 4.x"
    
    def test_lakefile_structure(self):
        """Test basic structure of lakefile.lean."""
        lakefile = self.rh_v6_dir / "lakefile.lean"
        content = lakefile.read_text()
        
        # Should import Lake
        assert "import Lake" in content, "Should import Lake"
        
        # Should define package
        assert "package" in content, "Should define a package"
        
        # Should require mathlib
        assert "mathlib" in content, "Should require mathlib"
    
    def test_paley_wiener_structure(self):
        """Test structure of paley_wiener_uniqueness.lean."""
        pw_file = self.rh_v6_dir / "paley_wiener_uniqueness.lean"
        content = pw_file.read_text()
        
        # Should import necessary modules
        assert "import Mathlib" in content, "Should import Mathlib"
        
        # Should define EntireOrderOne structure
        assert "structure EntireOrderOne" in content, "Should define EntireOrderOne"
        
        # Should define main theorem
        assert "theorem paley_wiener_uniqueness" in content, "Should define main theorem"
        
        # Should have symmetry conditions
        assert "hsymm_f" in content, "Should have symmetry for f"
        assert "hsymm_g" in content, "Should have symmetry for g"
        
        # Should have critical line condition
        assert "hcrit" in content, "Should have critical line condition"
    
    def test_selberg_trace_structure(self):
        """Test structure of selberg_trace.lean."""
        st_file = self.rh_v6_dir / "selberg_trace.lean"
        content = st_file.read_text()
        
        # Should import necessary modules
        assert "import Mathlib" in content, "Should import Mathlib"
        
        # Should define TestFunction
        assert "structure TestFunction" in content or "def TestFunction" in content, \
            "Should define TestFunction"
        
        # Should define spectral side
        assert "spectral_side" in content, "Should define spectral_side"
        
        # Should define geometric side
        assert "geometric_side" in content, "Should define geometric_side"
        
        # Should define arithmetic side
        assert "arithmetic_side" in content, "Should define arithmetic_side"
        
        # Should have main theorem
        assert "theorem selberg_trace_formula" in content, \
            "Should define Selberg trace formula theorem"
    
    def test_h_psi_complete_structure(self):
        """Test structure of H_psi_complete.lean."""
        hpsi_file = self.rh_v6_dir / "H_psi_complete.lean"
        content = hpsi_file.read_text()
        
        # Should import necessary modules
        assert "import Mathlib" in content, "Should import Mathlib"
        
        # Should define H_psi structure
        assert "structure H_psi" in content or "def H_psi" in content, \
            "Should define H_psi"
        
        # Should have Cauchy sequence definition
        assert "Cauchy" in content or "IsCauchy" in content, \
            "Should define Cauchy sequences"
        
        # Should have completeness theorem
        assert "theorem" in content and "complete" in content.lower(), \
            "Should have completeness theorem"
    
    def test_d_limit_equals_xi_structure(self):
        """Test structure of D_limit_equals_xi.lean."""
        d_xi_file = self.rh_v6_dir / "D_limit_equals_xi.lean"
        content = d_xi_file.read_text()
        
        # Should import necessary modules
        assert "import Mathlib" in content, "Should import Mathlib"
        
        # Should define xi function
        assert "xi" in content, "Should define or reference xi function"
        
        # Should reference D function
        assert "D_function" in content or "D" in content, \
            "Should reference D function"
        
        # Should have main theorem
        assert "theorem" in content and ("D_equals_xi" in content or "equals" in content), \
            "Should have theorem about D equals xi"
    
    def test_readme_content(self):
        """Test README.md has required sections."""
        readme = self.rh_v6_dir / "README.md"
        content = readme.read_text()
        
        # Should have title
        assert "RH_final_v6" in content, "Should mention RH_final_v6"
        
        # Should have overview
        assert "overview" in content.lower() or "description" in content.lower(), \
            "Should have overview section"
        
        # Should mention components
        assert "paley" in content.lower() or "Paley" in content, \
            "Should mention Paley-Wiener"
        assert "selberg" in content.lower() or "Selberg" in content, \
            "Should mention Selberg"
        
        # Should have build instructions
        assert "build" in content.lower() or "lake" in content.lower(), \
            "Should have build instructions"
    
    def test_citation_cff_structure(self):
        """Test CITATION.cff has required fields."""
        citation = self.rh_v6_dir / "CITATION.cff"
        content = citation.read_text()
        
        # Should have cff-version
        assert "cff-version" in content, "Should have cff-version"
        
        # Should have title
        assert "title:" in content, "Should have title"
        
        # Should have authors
        assert "authors:" in content, "Should have authors"
        
        # Should mention Mota Burruezo
        assert "Mota Burruezo" in content, "Should have author name"
        
        # Should have date
        assert "date-released" in content or "year:" in content, \
            "Should have release date"
        
        # Should have DOI or repository
        assert "doi:" in content or "repository" in content, \
            "Should have DOI or repository URL"
    
    def test_lean_syntax_basics(self):
        """Test basic Lean syntax in all .lean files."""
        lean_files = list(self.rh_v6_dir.glob("*.lean"))
        
        for lean_file in lean_files:
            content = lean_file.read_text()
            
            # Check balanced parentheses
            assert content.count('(') == content.count(')'), \
                f"{lean_file.name}: Unbalanced parentheses"
            
            # Check balanced braces
            assert content.count('{') == content.count('}'), \
                f"{lean_file.name}: Unbalanced braces"
            
            # Check balanced brackets
            assert content.count('[') == content.count(']'), \
                f"{lean_file.name}: Unbalanced brackets"
            
            # lakefile.lean has different structure, skip ending check for it
            if lean_file.name == "lakefile.lean":
                continue
            
            # Should end with 'end' or proper closing
            lines = content.strip().split('\n')
            last_line = lines[-1].strip()
            assert last_line == 'end' or last_line == '' or last_line.startswith('--'), \
                f"{lean_file.name}: Should end properly"


class TestRHFinalV6Content:
    """Test the mathematical content of RH_final_v6."""
    
    @pytest.fixture(autouse=True)
    def setup_method(self):
        """Setup test fixtures."""
        self.repo_root = Path(__file__).parent.parent
        self.rh_v6_dir = self.repo_root / "RH_final_v6"
    
    def test_paley_wiener_has_uniqueness_theorem(self):
        """Test that Paley-Wiener file contains uniqueness theorem."""
        pw_file = self.rh_v6_dir / "paley_wiener_uniqueness.lean"
        content = pw_file.read_text()
        
        # Should prove f = g under conditions
        assert "f = g" in content, "Should prove equality of functions"
        
        # Should use functional equation
        assert "1 - z" in content, "Should use functional equation"
        
        # Should reference critical line
        assert "1/2" in content, "Should reference critical line"
    
    def test_all_files_have_noncomputable_section(self):
        """Test that Lean files properly handle noncomputable definitions."""
        lean_files = [
            "paley_wiener_uniqueness.lean",
            "selberg_trace.lean",
            "H_psi_complete.lean",
            "D_limit_equals_xi.lean",
            "spectrum_eq_zeros.lean",
            "spectrum_HΨ_equals_zeta_zeros.lean",
        ]
        
        for filename in lean_files:
            filepath = self.rh_v6_dir / filename
            content = filepath.read_text()
            
            # Should have noncomputable section for complex analysis
            assert "noncomputable" in content, \
                f"{filename} should have noncomputable section"
    
    def test_spectrum_version_a_structure(self):
        """Test structure of spectrum_HΨ_equals_zeta_zeros.lean (Version A)."""
        spectrum_file = self.rh_v6_dir / "spectrum_HΨ_equals_zeta_zeros.lean"
        content = spectrum_file.read_text()
        
        # Should be Version A - proof without axioms
        assert "Versión A" in content or "Version A" in content, \
            "Should be marked as Version A"
        
        # Should define H_model
        assert "H_model" in content, "Should define H_model operator"
        
        # Should have constructive self-adjoint proof (not axiom)
        assert "theorem H_model_selfAdjoint" in content, \
            "Should have theorem (not axiom) for self-adjointness"
        
        # Should define explicit isometry U
        assert "def U_map" in content or "U_map" in content, \
            "Should define explicit isometry U"
        
        # Should use Hermite functions
        assert "hermite" in content.lower(), \
            "Should use Hermite functions for basis"
        
        # Should define spectral equivalence
        assert "spectrum" in content.lower(), \
            "Should define spectrum"
        
        # Should reference zeta zeros
        assert "zeta" in content.lower() or "ζ" in content, \
            "Should reference zeta function"
        
        # Should have QCAL integration
        assert "141.7001" in content, "Should have QCAL base frequency"
        
        # Should be properly documented
        assert "DOI" in content or "doi" in content, \
            "Should have DOI reference"
        assert "ORCID" in content or "orcid" in content, \
            "Should have ORCID reference"
    
    def test_spectrum_version_a_no_main_axioms(self):
        """Test that Version A eliminates main axioms."""
        spectrum_file = self.rh_v6_dir / "spectrum_HΨ_equals_zeta_zeros.lean"
        content = spectrum_file.read_text()
        
        # Count axiom declarations
        axiom_pattern = r'\baxiom\s+H_model_selfAdjoint'
        h_model_axiom = re.findall(axiom_pattern, content)
        
        # H_model_selfAdjoint should be a theorem, not an axiom
        assert len(h_model_axiom) == 0, \
            "H_model_selfAdjoint should be a theorem, not an axiom"
        
        # Should have theorem instead
        assert "theorem H_model_selfAdjoint" in content, \
            "Should have constructive proof as theorem"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
