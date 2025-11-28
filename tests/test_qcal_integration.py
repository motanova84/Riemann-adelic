"""
Integration tests for QCAL FFI bridge and universal kernel.
"""

import pytest
import subprocess
import os
from pathlib import Path


class TestQCALIntegration:
    """Integration tests for the complete QCAL system."""
    
    @pytest.fixture
    def repo_root(self):
        """Get repository root directory."""
        return Path(__file__).parent.parent
    
    def test_ffi_bridge_compiled(self, repo_root):
        """Test that the FFI bridge library exists or can be compiled."""
        libbridge_path = repo_root / "formalization" / "lean" / "QCAL" / "FFI" / "libbridge.so"
        
        if not libbridge_path.exists():
            # Try to compile it
            ffi_dir = repo_root / "formalization" / "lean" / "QCAL" / "FFI"
            result = subprocess.run(
                ["clang", "-shared", "-fPIC", 
                 "-I/usr/include/python3.12", "-lpython3.12",
                 "-o", "libbridge.so", "libbridge.c"],
                cwd=ffi_dir,
                capture_output=True,
                text=True
            )
            
            if result.returncode != 0:
                pytest.skip(f"Could not compile FFI bridge: {result.stderr}")
        
        assert libbridge_path.exists(), "FFI bridge library does not exist"
        assert libbridge_path.stat().st_size > 0, "FFI bridge library is empty"
    
    def test_schema_file_exists(self, repo_root):
        """Test that example schema file exists."""
        schema_path = repo_root / "schema" / "metadatos_ejemplo.jsonld"
        assert schema_path.exists(), "Example schema file does not exist"
    
    def test_universal_kernel_script_exists(self, repo_root):
        """Test that universal kernel script exists."""
        kernel_path = repo_root / "tools" / "universal_kernel.py"
        assert kernel_path.exists(), "Universal kernel script does not exist"
    
    def test_lean_qcal_files_exist(self, repo_root):
        """Test that Lean QCAL files exist."""
        bridge_path = repo_root / "formalization" / "lean" / "QCAL" / "FFI" / "Bridge.lean"
        kernel_path = repo_root / "formalization" / "lean" / "QCAL" / "UniversalKernel.lean"
        
        assert bridge_path.exists(), "Bridge.lean does not exist"
        assert kernel_path.exists(), "UniversalKernel.lean does not exist"
    
    def test_universal_kernel_cli(self, repo_root):
        """Test universal kernel command-line interface."""
        schema_path = repo_root / "schema" / "metadatos_ejemplo.jsonld"
        proof_path = repo_root / "formalization" / "lean" / "Main.lean"
        kernel_path = repo_root / "tools" / "universal_kernel.py"
        
        result = subprocess.run(
            ["python3", str(kernel_path), str(schema_path), str(proof_path)],
            cwd=repo_root,
            capture_output=True,
            text=True
        )
        
        assert result.returncode == 0, f"Universal kernel failed: {result.stderr}"
        assert "✅" in result.stdout, "Success indicator not found in output"
    
    def test_qcal_state_generation(self, repo_root, tmp_path):
        """Test that verification generates state file."""
        import sys
        sys.path.insert(0, str(repo_root / "tools"))
        
        import universal_kernel
        
        output_file = tmp_path / "test_qcal_state.json"
        schema_path = repo_root / "schema" / "metadatos_ejemplo.jsonld"
        proof_path = repo_root / "formalization" / "lean" / "Main.lean"
        
        result = universal_kernel.register_verification(
            str(schema_path),
            str(proof_path),
            True,
            str(output_file)
        )
        
        assert result is True
        assert output_file.exists()
    
    def test_lakefile_includes_qcal(self, repo_root):
        """Test that lakefile.lean includes QCAL library."""
        lakefile_path = repo_root / "formalization" / "lean" / "lakefile.lean"
        
        with open(lakefile_path, 'r') as f:
            content = f.read()
        
        assert "QCAL" in content, "lakefile.lean does not include QCAL"
        assert "lean_lib «QCAL»" in content, "QCAL library declaration not found"
    
    def test_ci_workflow_includes_ffi(self, repo_root):
        """Test that CI workflow includes FFI compilation."""
        ci_path = repo_root / ".github" / "workflows" / "ci.yml"
        
        with open(ci_path, 'r') as f:
            content = f.read()
        
        assert "Compile FFI bridge" in content, "CI does not include FFI compilation"
        assert "Universal Coherence" in content, "CI does not include coherence check"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
