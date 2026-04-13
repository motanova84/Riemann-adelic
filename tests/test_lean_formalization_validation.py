"""
Test suite for Lean formalization validation
============================================

Tests the validation script and Lean formalization structure.
"""

import pytest
import sys
from pathlib import Path
import subprocess

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestLeanValidation:
    """Tests for Lean formalization validation script"""
    
    def test_validation_script_exists(self):
        """Test that the validation script exists"""
        script_path = PROJECT_ROOT / "validate_lean_formalization.py"
        assert script_path.exists(), f"Validation script not found: {script_path}"
        assert script_path.stat().st_size > 0, "Validation script is empty"
    
    def test_validation_script_is_executable(self):
        """Test that the validation script is executable"""
        script_path = PROJECT_ROOT / "validate_lean_formalization.py"
        assert script_path.exists()
        # Check if file has execute permissions
        import os
        assert os.access(script_path, os.X_OK), "Script is not executable"
    
    def test_validation_script_runs(self):
        """Test that the validation script runs successfully"""
        script_path = PROJECT_ROOT / "validate_lean_formalization.py"
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True
        )
        # Should exit with 0 (success) since structure is valid
        assert result.returncode == 0, f"Validation failed: {result.stderr}"
        assert "Validation Summary" in result.stdout
        assert "All validations passed" in result.stdout


class TestLeanFormalizationStructure:
    """Tests for Lean formalization file structure"""
    
    def test_lean_directory_exists(self):
        """Test that the Lean formalization directory exists"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        assert lean_dir.exists(), f"Lean directory not found: {lean_dir}"
        assert lean_dir.is_dir(), "formalization/lean is not a directory"
    
    def test_main_lean_exists(self):
        """Test that Main.lean exists"""
        main_file = PROJECT_ROOT / "formalization" / "lean" / "Main.lean"
        assert main_file.exists(), "Main.lean not found"
        assert main_file.stat().st_size > 0, "Main.lean is empty"
    
    def test_main_lean_imports_all_modules(self):
        """Test that Main.lean imports all required modules"""
        main_file = PROJECT_ROOT / "formalization" / "lean" / "Main.lean"
        with open(main_file, 'r') as f:
            content = f.read()
        
        required_imports = [
            "RiemannAdelic.axioms_to_lemmas",
            "RiemannAdelic.schwartz_adelic",
            "RiemannAdelic.D_explicit",
            "RiemannAdelic.entire_order",
            "RiemannAdelic.functional_eq",
            "RiemannAdelic.poisson_radon_symmetry",
            "RiemannAdelic.arch_factor",
            "RiemannAdelic.de_branges",
            "RiemannAdelic.positivity",
            "RiemannAdelic.doi_positivity",
            "RiemannAdelic.zero_localization",
            "RiemannAdelic.uniqueness_without_xi",
            "RiemannAdelic.pw_two_lines",
            "RiemannAdelic.lengths_derived",
            "RiemannAdelic.paley_wiener_uniqueness",
        ]
        
        for imp in required_imports:
            assert f"import {imp}" in content, f"Missing import: {imp}"
    
    def test_rh_final_exists(self):
        """Test that RH_final.lean exists"""
        rh_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final.lean"
        assert rh_file.exists(), "RH_final.lean not found"
        assert rh_file.stat().st_size > 0, "RH_final.lean is empty"
    
    def test_toolchain_file_exists(self):
        """Test that lean-toolchain file exists"""
        toolchain_file = PROJECT_ROOT / "formalization" / "lean" / "lean-toolchain"
        assert toolchain_file.exists(), "lean-toolchain not found"
        
        with open(toolchain_file, 'r') as f:
            content = f.read().strip()
        
        assert "leanprover/lean4" in content, "Invalid toolchain specification"
        assert "v4.5.0" in content, "Expected Lean 4.5.0"
    
    def test_lakefile_exists(self):
        """Test that lakefile.lean exists"""
        lakefile = PROJECT_ROOT / "formalization" / "lean" / "lakefile.lean"
        assert lakefile.exists(), "lakefile.lean not found"
        
        with open(lakefile, 'r') as f:
            content = f.read()
        
        assert "mathlib" in content.lower(), "mathlib dependency not found in lakefile"
    
    def test_required_modules_exist(self):
        """Test that all required Lean modules exist"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        
        required_modules = [
            "RiemannAdelic/axioms_to_lemmas.lean",
            "RiemannAdelic/schwartz_adelic.lean",
            "RiemannAdelic/D_explicit.lean",
            "RiemannAdelic/de_branges.lean",
            "RiemannAdelic/entire_order.lean",
            "RiemannAdelic/functional_eq.lean",
            "RiemannAdelic/positivity.lean",
            "RiemannAdelic/poisson_radon_symmetry.lean",
            "RiemannAdelic/zero_localization.lean",
            "RiemannAdelic/uniqueness_without_xi.lean",
            "RiemannAdelic/arch_factor.lean",
            "RiemannAdelic/pw_two_lines.lean",
            "RiemannAdelic/lengths_derived.lean",
            "RiemannAdelic/doi_positivity.lean",
            "RiemannAdelic/paley_wiener_uniqueness.lean",
        ]
        
        for module in required_modules:
            module_path = lean_dir / module
            assert module_path.exists(), f"Module not found: {module}"
            assert module_path.stat().st_size > 0, f"Module is empty: {module}"
    
    def test_xi_symmetry_identity_module_exists(self):
        """Test that the xi_symmetry_identity Lean module exists"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        xi_symmetry_path = lean_dir / "spectral" / "xi_symmetry_identity.lean"
        assert xi_symmetry_path.exists(), "xi_symmetry_identity.lean not found"
        assert xi_symmetry_path.stat().st_size > 0, "xi_symmetry_identity.lean is empty"
    
    def test_xi_symmetry_identity_content(self):
        """Test that xi_symmetry_identity.lean contains the main theorem"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        xi_symmetry_path = lean_dir / "spectral" / "xi_symmetry_identity.lean"
        
        with open(xi_symmetry_path, 'r') as f:
            content = f.read()
        
        # Check for main theorem
        assert "xi_symmetry_identity" in content, "Main theorem not found"
        assert "ξ s = ξ (1 - s)" in content, "Functional equation statement not found"
        # Check for supporting lemmas
        assert "symmetric_factor_invariant" in content, "symmetric_factor lemma not found"
        assert "zeros_symmetric" in content, "zeros_symmetric corollary not found"


class TestLeanDocumentation:
    """Tests for Lean formalization documentation"""
    
    def test_setup_guide_exists(self):
        """Test that SETUP_GUIDE.md exists"""
        guide_path = PROJECT_ROOT / "formalization" / "lean" / "SETUP_GUIDE.md"
        assert guide_path.exists(), "SETUP_GUIDE.md not found"
        assert guide_path.stat().st_size > 1000, "SETUP_GUIDE.md is too small"
    
    def test_setup_guide_has_installation_instructions(self):
        """Test that SETUP_GUIDE.md contains installation instructions"""
        guide_path = PROJECT_ROOT / "formalization" / "lean" / "SETUP_GUIDE.md"
        with open(guide_path, 'r') as f:
            content = f.read()
        
        assert "elan" in content.lower(), "Missing elan installation instructions"
        assert "lake build" in content.lower(), "Missing build instructions"
        assert "install" in content.lower(), "Missing installation section"
    
    def test_readme_updated(self):
        """Test that README.md has been updated"""
        readme_path = PROJECT_ROOT / "formalization" / "lean" / "README.md"
        assert readme_path.exists(), "README.md not found"
        
        with open(readme_path, 'r') as f:
            content = f.read()
        
        # Check for recent updates
        assert "V5.2" in content or "V5.3" in content, "README not updated to latest version"
        assert "SETUP_GUIDE" in content, "README doesn't mention SETUP_GUIDE"
    
    def test_formalization_status_updated(self):
        """Test that FORMALIZATION_STATUS.md has been updated"""
        status_path = PROJECT_ROOT / "FORMALIZATION_STATUS.md"
        assert status_path.exists(), "FORMALIZATION_STATUS.md not found"
        
        with open(status_path, 'r') as f:
            content = f.read()
        
        assert "ACTIVATED" in content or "activated" in content, "Status not marked as activated"
        assert "validate_lean_formalization.py" in content, "Validation script not mentioned"


class TestCIWorkflow:
    """Tests for CI/CD workflow template"""
    
    def test_ci_workflow_template_exists(self):
        """Test that CI workflow template exists"""
        workflow_path = PROJECT_ROOT / "formalization" / "lean" / "lean-ci-workflow-suggestion.yml"
        assert workflow_path.exists(), "CI workflow template not found"
        assert workflow_path.stat().st_size > 0, "CI workflow template is empty"
    
    def test_ci_workflow_has_validation_job(self):
        """Test that CI workflow includes validation job"""
        workflow_path = PROJECT_ROOT / "formalization" / "lean" / "lean-ci-workflow-suggestion.yml"
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        assert "validate_lean_formalization.py" in content, "Validation not in workflow"
        assert "lake build" in content, "Build step not in workflow"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
