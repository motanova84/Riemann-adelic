"""
Test suite for spectral_convergence_from_kernel.lean module
============================================================

Tests the existence, structure, and integration of the spectral 
convergence module in RH_final_v6.
"""

import pytest
import sys
from pathlib import Path

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestSpectralConvergenceModule:
    """Tests for spectral_convergence_from_kernel.lean module"""
    
    def test_module_exists(self):
        """Test that the spectral convergence module exists"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        assert module_path.exists(), f"Module not found: {module_path}"
        assert module_path.stat().st_size > 0, "Module is empty"
    
    def test_module_has_proper_header(self):
        """Test that the module has proper documentation header"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "spectral_convergence_from_kernel.lean" in content
        assert "José Manuel Mota Burruezo" in content
        assert "22 noviembre 2025" in content
    
    def test_module_has_required_imports(self):
        """Test that the module imports required dependencies"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_imports = [
            "Mathlib.Analysis.Fourier.FourierTransform",
            "Mathlib.MeasureTheory.Function.L2Space",
            "Mathlib.Topology.Distributions",
            "Mathlib.Data.Real.Basic",
        ]
        
        for imp in required_imports:
            assert f"import {imp}" in content, f"Missing import: {imp}"
    
    def test_module_has_test_function_structure(self):
        """Test that the TestFunction structure is defined"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "structure TestFunction" in content
        assert "contDiff" in content
        assert "decay" in content
    
    def test_module_has_spectral_side_definition(self):
        """Test that spectral_side is defined"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "def spectral_side" in content
        assert "Finset.range N" in content
    
    def test_module_has_spectral_limit_definition(self):
        """Test that spectral_limit is defined"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "def spectral_limit" in content
        assert "Nat.Primes" in content
    
    def test_module_has_main_convergence_theorem(self):
        """Test that the main convergence theorem is present"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "theorem spectral_convergence_from_kernel" in content
        assert "kernel_conv" in content
        assert "Tendsto" in content
    
    def test_module_has_uniform_convergence_theorem(self):
        """Test that uniform convergence theorem exists"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "theorem spectral_convergence_uniform" in content
    
    def test_module_has_proper_namespace(self):
        """Test that the module uses proper namespace"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "namespace SpectralConvergence" in content
        assert "end SpectralConvergence" in content
    
    def test_module_has_qcal_integration(self):
        """Test that QCAL framework references are present"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "141.7001" in content or "QCAL" in content
    
    def test_module_compilation_info(self):
        """Test that compilation info is present"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "Lean 4.13.0" in content or "Lean 4" in content
        assert "RH_final_v6" in content


class TestRHFinalV6Integration:
    """Tests for integration with RH_final_v6 framework"""
    
    def test_module_in_lakefile(self):
        """Test that the module is included in lakefile"""
        lakefile_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "lakefile.lean"
        with open(lakefile_path, 'r') as f:
            content = f.read()
        
        assert "spectral_convergence_from_kernel" in content
    
    def test_module_in_readme(self):
        """Test that the module is documented in README"""
        readme_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "README.md"
        with open(readme_path, 'r') as f:
            content = f.read()
        
        assert "spectral_convergence_from_kernel" in content
        assert "Convergencia del lado espectral" in content
    
    def test_rh_final_v6_directory_structure(self):
        """Test that RH_final_v6 has proper structure"""
        rh_dir = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6"
        assert rh_dir.exists()
        assert rh_dir.is_dir()
        
        required_files = [
            "lakefile.lean",
            "lean-toolchain",
            "README.md",
            "paley_wiener_uniqueness.lean",
            "selberg_trace.lean",
            "H_psi_complete.lean",
            "D_limit_equals_xi.lean",
            "spectral_convergence_from_kernel.lean"
        ]
        
        for filename in required_files:
            filepath = rh_dir / filename
            assert filepath.exists(), f"Required file not found: {filename}"
    
    def test_module_count_in_lakefile(self):
        """Test that lakefile includes all 5 modules"""
        lakefile_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "lakefile.lean"
        with open(lakefile_path, 'r') as f:
            content = f.read()
        
        modules = [
            "paley_wiener_uniqueness",
            "selberg_trace",
            "H_psi_complete",
            "D_limit_equals_xi",
            "spectral_convergence_from_kernel"
        ]
        
        for module in modules:
            assert module in content, f"Module not in lakefile: {module}"


class TestModuleDocumentation:
    """Tests for documentation quality"""
    
    def test_module_has_doc_comments(self):
        """Test that module has proper doc comments"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "/-!" in content, "Module missing doc comments"
        assert "Spectral Convergence from Heat Kernel" in content
    
    def test_module_has_mathematical_descriptions(self):
        """Test that module has mathematical descriptions"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "heat kernel" in content.lower()
        assert "convergence" in content.lower()
        assert "spectral" in content.lower()
    
    def test_module_has_author_info(self):
        """Test that module has proper author attribution"""
        module_path = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "spectral_convergence_from_kernel.lean"
        with open(module_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert "José Manuel Mota Burruezo" in content
        assert "Ψ" in content


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
