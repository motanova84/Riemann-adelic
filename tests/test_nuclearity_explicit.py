"""
Test suite for NuclearityExplicit.lean and verify_no_sorrys.py
===============================================================

Tests the new nuclear operator construction module and sorry verification.
"""

import pytest
import sys
import subprocess
from pathlib import Path

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestNuclearityExplicit:
    """Tests for NuclearityExplicit.lean module"""
    
    def test_nuclearity_file_exists(self):
        """Test that NuclearityExplicit.lean exists"""
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        assert lean_file.exists(), f"NuclearityExplicit.lean not found: {lean_file}"
        assert lean_file.stat().st_size > 0, "NuclearityExplicit.lean is empty"
    
    def test_nuclearity_file_has_required_imports(self):
        """Test that the file has the necessary imports"""
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        content = lean_file.read_text()
        
        # Check for required imports
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace.Basic",
            "Mathlib.Analysis.SpecialFunctions.Exp",
            "Mathlib.MeasureTheory.Integral.Bochner"
        ]
        
        for imp in required_imports:
            assert imp in content, f"Missing required import: {imp}"
    
    def test_nuclearity_file_has_key_definitions(self):
        """Test that the file defines key constants and functions"""
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        content = lean_file.read_text()
        
        # Check for key definitions
        assert "def T : ℝ := 888" in content, "Missing T definition"
        assert "def HΨ_kernel" in content, "Missing HΨ_kernel definition"
        assert "141.7001" in content, "Missing base frequency 141.7001 Hz"
    
    def test_nuclearity_file_has_key_theorems(self):
        """Test that the file contains the key theorems"""
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        content = lean_file.read_text()
        
        # Check for key theorems
        key_theorems = [
            "theorem HΨ_kernel_bounded",
            "theorem HΨ_kernel_L2_estimate",
            "theorem HΨ_is_hilbert_schmidt",
            "theorem HΨ_is_nuclear",
            "theorem HΨ_trace_norm_bound",
            "theorem HΨ_trace_norm_finite"
        ]
        
        for theorem in key_theorems:
            assert theorem in content, f"Missing key theorem: {theorem}"
    
    def test_nuclearity_file_has_no_sorrys(self):
        """Test that NuclearityExplicit.lean has no sorrys"""
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        content = lean_file.read_text()
        
        # Remove comments
        lines = content.split('\n')
        code_lines = []
        in_block_comment = False
        
        for line in lines:
            stripped = line.strip()
            
            if '/-' in stripped:
                in_block_comment = True
                before_comment = stripped.split('/-')[0]
                if before_comment and not in_block_comment:
                    code_lines.append(before_comment)
                continue
                
            if '-/' in stripped:
                in_block_comment = False
                continue
                
            if in_block_comment or stripped.startswith('--'):
                continue
                
            code_lines.append(line)
        
        code_content = '\n'.join(code_lines)
        sorry_count = code_content.count('sorry')
        
        assert sorry_count == 0, f"Found {sorry_count} sorrys in NuclearityExplicit.lean"
    
    def test_nuclearity_in_lakefile(self):
        """Test that NuclearityExplicit is added to lakefile.lean"""
        lakefile = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "lakefile.lean"
        content = lakefile.read_text()
        
        assert "`NuclearityExplicit" in content, "NuclearityExplicit not found in lakefile.lean roots"


class TestVerifyNoSorrysScript:
    """Tests for verify_no_sorrys.py script"""
    
    def test_verify_script_exists(self):
        """Test that verify_no_sorrys.py exists"""
        script_path = PROJECT_ROOT / "scripts" / "verify_no_sorrys.py"
        assert script_path.exists(), f"verify_no_sorrys.py not found: {script_path}"
        assert script_path.stat().st_size > 0, "verify_no_sorrys.py is empty"
    
    def test_verify_script_is_executable(self):
        """Test that the verification script is executable"""
        script_path = PROJECT_ROOT / "scripts" / "verify_no_sorrys.py"
        assert script_path.exists()
        # Check if file has execute permissions
        import os
        assert os.access(script_path, os.X_OK), "verify_no_sorrys.py is not executable"
    
    def test_verify_script_runs_on_nuclearity(self):
        """Test that verify_no_sorrys.py runs successfully on NuclearityExplicit.lean"""
        script_path = PROJECT_ROOT / "scripts" / "verify_no_sorrys.py"
        lean_file = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "NuclearityExplicit.lean"
        
        result = subprocess.run(
            [sys.executable, str(script_path), str(lean_file)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True
        )
        
        # Should exit with 0 (success) since NuclearityExplicit has 0 sorrys
        assert result.returncode == 0, f"Verification failed: {result.stderr}\n{result.stdout}"
        assert "VERIFICATION PASSED" in result.stdout
        assert "Total sorries: 0" in result.stdout
        assert "No sorries! All proofs are complete" in result.stdout
    
    def test_verify_script_shows_usage(self):
        """Test that the script shows usage when called without arguments"""
        script_path = PROJECT_ROOT / "scripts" / "verify_no_sorrys.py"
        
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True
        )
        
        # Should exit with 1 (failure) and show usage
        assert result.returncode == 1
        assert "Usage:" in result.stdout


class TestNuclearityDocumentation:
    """Tests for documentation of NuclearityExplicit module"""
    
    def test_readme_mentions_nuclearity(self):
        """Test that README.md mentions NuclearityExplicit"""
        readme = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "README.md"
        content = readme.read_text()
        
        assert "NuclearityExplicit" in content, "README doesn't mention NuclearityExplicit module"
        assert "0 sorrys" in content or "0 sorry" in content, "README doesn't mention 0 sorrys"
    
    def test_readme_has_nuclearity_section(self):
        """Test that README has a detailed section for NuclearityExplicit"""
        readme = PROJECT_ROOT / "formalization" / "lean" / "RH_final_v6" / "README.md"
        content = readme.read_text()
        
        # Check for key documentation elements
        assert "nuclear (trace-class)" in content.lower(), "Missing nuclear/trace-class description"
        assert "141.7001" in content, "Missing base frequency in documentation"
        assert "888" in content, "Missing T parameter or bound in documentation"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
