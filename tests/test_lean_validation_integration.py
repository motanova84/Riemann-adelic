"""
Test suite for Lean validation environment script and README update
====================================================================

Tests the validate_lean_env.py script and the update_lean_validation_table.py script.
"""

import pytest
import json
import sys
from pathlib import Path
import subprocess
import tempfile
import shutil

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestValidateLeanEnv:
    """Tests for validate_lean_env.py script"""
    
    def test_validate_lean_env_exists(self):
        """Test that the validate_lean_env.py script exists"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        assert script_path.exists(), f"Script not found: {script_path}"
        assert script_path.stat().st_size > 0, "Script is empty"
    
    def test_validate_lean_env_is_executable(self):
        """Test that the script is executable"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        assert script_path.exists()
        import os
        assert os.access(script_path, os.X_OK), "Script is not executable"
    
    def test_validate_lean_env_generates_report(self):
        """Test that the script generates a validation report"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        
        # Run the script
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=lean_dir,
            capture_output=True,
            text=True
        )
        
        # Should exit with 0
        assert result.returncode == 0, f"Script failed: {result.stderr}"
        
        # Check that report was generated
        report_path = lean_dir / "validation_report.json"
        assert report_path.exists(), "Validation report not generated"
        
        # Verify report structure
        with open(report_path, 'r') as f:
            report = json.load(f)
        
        assert "validation" in report, "Report missing 'validation' key"
        assert "build_details" in report, "Report missing 'build_details' key"
        
        validation = report["validation"]
        assert "status" in validation, "Missing 'status' field"
        assert "build_time_seconds" in validation, "Missing 'build_time_seconds' field"
        assert "warnings" in validation, "Missing 'warnings' field"
        assert "errors" in validation, "Missing 'errors' field"
        assert "lean_version" in validation, "Missing 'lean_version' field"
        assert "timestamp_utc" in validation, "Missing 'timestamp_utc' field"
        assert "file_count" in validation, "Missing 'file_count' field"
        
        # Clean up
        if report_path.exists():
            report_path.unlink()
    
    def test_lean_version_parsing(self):
        """Test that Lean version is parsed correctly"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        
        result = subprocess.run(
            [sys.executable, str(script_path)],
            cwd=lean_dir,
            capture_output=True,
            text=True
        )
        
        report_path = lean_dir / "validation_report.json"
        with open(report_path, 'r') as f:
            report = json.load(f)
        
        lean_version = report["validation"]["lean_version"]
        assert lean_version == "4.5.0", f"Unexpected Lean version: {lean_version}"
        
        # Clean up
        if report_path.exists():
            report_path.unlink()


class TestUpdateLeanValidationTable:
    """Tests for update_lean_validation_table.py script"""
    
    def test_update_script_exists(self):
        """Test that the update script exists"""
        script_path = PROJECT_ROOT / ".github" / "scripts" / "update_lean_validation_table.py"
        assert script_path.exists(), f"Script not found: {script_path}"
        assert script_path.stat().st_size > 0, "Script is empty"
    
    def test_update_script_is_executable(self):
        """Test that the update script is executable"""
        script_path = PROJECT_ROOT / ".github" / "scripts" / "update_lean_validation_table.py"
        assert script_path.exists()
        import os
        assert os.access(script_path, os.X_OK), "Script is not executable"
    
    def test_update_script_updates_readme(self):
        """Test that the update script correctly updates README"""
        script_path = PROJECT_ROOT / ".github" / "scripts" / "update_lean_validation_table.py"
        
        # Create a temporary directory
        with tempfile.TemporaryDirectory() as tmpdir:
            tmpdir = Path(tmpdir)
            
            # Create a test validation report
            test_report = {
                "validation": {
                    "status": "PASS",
                    "build_time_seconds": 42.5,
                    "warnings": 2,
                    "errors": 0,
                    "lean_version": "4.5.0",
                    "timestamp_utc": "2025-10-26 23:00:00",
                    "file_count": 20
                },
                "build_details": {
                    "return_code": 0,
                    "output_sample": "Build successful"
                }
            }
            
            report_path = tmpdir / "validation_report.json"
            with open(report_path, 'w') as f:
                json.dump(test_report, f)
            
            # Create a test README with validation table
            test_readme = """# Test README

## Riemann–Adelic Formalization (Lean 4 V5.3)

### Validation Summary

| Field | Value |
|-------|-------|
| **Status** | FAIL |
| **Build Time (s)** | 0.0 |
| **Warnings** | 0 |
| **Errors** | 1 |
| **Lean Version** | 4.5.0 |
| **Date (UTC)** | 2025-10-26 00:00:00 |

### Project Overview
This is a test.
"""
            
            readme_path = tmpdir / "README.md"
            with open(readme_path, 'w') as f:
                f.write(test_readme)
            
            # Run the update script
            result = subprocess.run(
                [sys.executable, str(script_path)],
                cwd=tmpdir,
                capture_output=True,
                text=True
            )
            
            assert result.returncode == 0, f"Script failed: {result.stderr}"
            assert "Updated existing validation table" in result.stdout
            
            # Read updated README
            with open(readme_path, 'r') as f:
                updated_readme = f.read()
            
            # Verify updates
            assert "PASS" in updated_readme, "Status not updated"
            assert "42.5" in updated_readme, "Build time not updated"
            assert "2025-10-26 23:00:00" in updated_readme, "Timestamp not updated"
            assert "| **Warnings** | 2 |" in updated_readme, "Warnings not updated"


class TestLeanValidationWorkflow:
    """Tests for lean-validation.yml workflow"""
    
    def test_workflow_exists(self):
        """Test that the lean-validation workflow exists"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        assert workflow_path.exists(), f"Workflow not found: {workflow_path}"
        assert workflow_path.stat().st_size > 0, "Workflow is empty"
    
    def test_workflow_has_validation_job(self):
        """Test that workflow has validation job"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        assert "validate_lean_env.py" in content, "Validation script not in workflow"
        assert "Generate Validation Report" in content, "Validation step missing"
    
    def test_workflow_has_update_badge_job(self):
        """Test that workflow has update-badge job"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        assert "update-badge" in content, "update-badge job missing"
        assert "update_lean_validation_table.py" in content, "Update script not in workflow"
    
    def test_workflow_syntax_valid(self):
        """Test that workflow YAML is valid"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        try:
            import yaml
            with open(workflow_path, 'r') as f:
                yaml.safe_load(f)
        except Exception as e:
            pytest.fail(f"Invalid YAML syntax: {e}")


class TestREADMELeanSection:
    """Tests for Lean formalization section in main README"""
    
    def test_readme_has_lean_section(self):
        """Test that README has Lean formalization section"""
        readme_path = PROJECT_ROOT / "README.md"
        assert readme_path.exists(), "README.md not found"
        
        with open(readme_path, 'r') as f:
            content = f.read()
        
        assert "Riemann–Adelic Formalization (Lean 4 V5.3)" in content, \
            "Lean formalization section missing"
    
    def test_readme_has_validation_badge(self):
        """Test that README has Lean validation badge"""
        readme_path = PROJECT_ROOT / "README.md"
        with open(readme_path, 'r') as f:
            content = f.read()
        
        assert "lean-validation.yml/badge.svg" in content, \
            "Lean validation badge missing"
    
    def test_readme_has_validation_table(self):
        """Test that README has validation summary table"""
        readme_path = PROJECT_ROOT / "README.md"
        with open(readme_path, 'r') as f:
            content = f.read()
        
        assert "### Validation Summary" in content, "Validation Summary section missing"
        assert "| Field | Value |" in content, "Validation table missing"
        assert "| **Status** |" in content, "Status field missing"
        assert "| **Build Time (s)** |" in content, "Build time field missing"
        assert "| **Lean Version** |" in content, "Lean version field missing"
    
    def test_readme_has_reproducibility_section(self):
        """Test that README has reproducibility instructions"""
        readme_path = PROJECT_ROOT / "README.md"
        with open(readme_path, 'r') as f:
            content = f.read()
        
        assert "### Reproducibility" in content or "Reproducibility" in content, \
            "Reproducibility section missing"
        assert "validate_lean_env.py" in content, \
            "validate_lean_env.py not mentioned in README"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
