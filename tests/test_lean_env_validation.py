"""
Test suite for Lean environment validation script
==================================================

Tests the validate_lean_env.py script and JSON report generation.
"""

import json
import pytest
import sys
from pathlib import Path
import subprocess

# Add project root to path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


class TestLeanEnvValidationScript:
    """Tests for validate_lean_env.py script"""
    
    def test_script_exists(self):
        """Test that validate_lean_env.py exists"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        assert script_path.exists(), f"Script not found: {script_path}"
        assert script_path.stat().st_size > 0, "Script is empty"
    
    def test_script_is_executable(self):
        """Test that the script has executable permissions"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        import os
        assert os.access(script_path, os.X_OK), "Script is not executable"
    
    def test_script_runs_from_lean_directory(self):
        """Test that the script runs when executed from formalization/lean"""
        script_path = PROJECT_ROOT / "formalization" / "lean" / "validate_lean_env.py"
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        
        result = subprocess.run(
            [sys.executable, "validate_lean_env.py"],
            cwd=lean_dir,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Script should run without crashing
        assert result.returncode in [0, 1], f"Script crashed: {result.stderr}"
        assert "Lean 4 Environment Validation" in result.stdout
        assert "VALIDATION SUMMARY" in result.stdout
    
    def test_script_generates_json_report(self):
        """Test that the script generates validation_report.json"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        report_path = lean_dir / "validation_report.json"
        
        # Clean up any existing report
        if report_path.exists():
            report_path.unlink()
        
        # Run the script
        result = subprocess.run(
            [sys.executable, "validate_lean_env.py"],
            cwd=lean_dir,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Check that report was created (script should complete successfully or with warnings)
        assert result.returncode in [0, 1], f"Script failed unexpectedly: {result.stderr}"
        assert report_path.exists(), "validation_report.json was not created"
        
        # Clean up after test
        if report_path.exists():
            report_path.unlink()
    
    def test_json_report_format(self):
        """Test that the JSON report has the correct format"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        report_path = lean_dir / "validation_report.json"
        
        # Clean up any existing report
        if report_path.exists():
            report_path.unlink()
        
        # Run the script
        result = subprocess.run(
            [sys.executable, "validate_lean_env.py"],
            cwd=lean_dir,
            capture_output=True,
            timeout=30,
            check=False  # Don't raise on non-zero exit (script may return 1 on validation fail)
        )
        
        # Ensure script completed (exit code 0 or 1 are both acceptable)
        assert result.returncode in [0, 1], f"Script failed unexpectedly: {result.stderr}"
        
        # Load and validate JSON
        assert report_path.exists(), "validation_report.json was not created"
        
        with open(report_path, 'r') as f:
            report = json.load(f)
        
        # Check required top-level keys
        required_keys = [
            "validation_timestamp",
            "summary",
            "environment",
            "project",
            "build_time_sec",
            "warnings",
            "errors",
            "details",
            "metadata"
        ]
        
        for key in required_keys:
            assert key in report, f"Missing required key: {key}"
        
        # Check summary structure
        assert "status" in report["summary"]
        assert "message" in report["summary"]
        assert report["summary"]["status"] in ["PASS", "FAIL", "PARTIAL"]
        
        # Check environment structure
        assert "lean" in report["environment"]
        assert "lake" in report["environment"]
        assert "installed" in report["environment"]["lean"]
        assert "version" in report["environment"]["lean"]
        
        # Check project structure
        assert "structure_valid" in report["project"]
        assert "dependencies_updated" in report["project"]
        assert "build_successful" in report["project"]
        
        # Check numeric fields
        assert isinstance(report["build_time_sec"], (int, float))
        assert isinstance(report["warnings"], int)
        assert isinstance(report["errors"], int)
        assert report["build_time_sec"] >= 0
        assert report["warnings"] >= 0
        assert report["errors"] >= 0
        
        # Check details structure
        assert "warnings" in report["details"]
        assert "errors" in report["details"]
        assert isinstance(report["details"]["warnings"], list)
        assert isinstance(report["details"]["errors"], list)
        
        # Check metadata
        assert "repository" in report["metadata"]
        assert "doi" in report["metadata"]
        assert "formalization" in report["metadata"]
        assert "10.5281/zenodo.17116291" in report["metadata"]["doi"]
        
        # Clean up after test
        if report_path.exists():
            report_path.unlink()
    
    def test_json_can_be_parsed_by_jq(self):
        """Test that the JSON report can be parsed by jq (for GitHub Actions)"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        report_path = lean_dir / "validation_report.json"
        
        # Clean up any existing report
        if report_path.exists():
            report_path.unlink()
        
        # Run the script
        result = subprocess.run(
            [sys.executable, "validate_lean_env.py"],
            cwd=lean_dir,
            capture_output=True,
            timeout=30,
            check=False  # Don't raise on non-zero exit (script may return 1 on validation fail)
        )
        
        # Ensure script completed
        assert result.returncode in [0, 1], f"Script failed unexpectedly: {result.stderr}"
        assert report_path.exists(), "validation_report.json was not created"
        
        # Try to parse with jq-like queries using Python's json
        with open(report_path, 'r') as f:
            report = json.load(f)
        
        # Simulate the jq query from the GitHub Actions workflow
        status = report["summary"]["status"]
        build_time = report["build_time_sec"]
        warnings = report["warnings"]
        errors = report["errors"]
        
        assert isinstance(status, str)
        assert isinstance(build_time, (int, float))
        assert isinstance(warnings, int)
        assert isinstance(errors, int)
        
        # Clean up after test
        if report_path.exists():
            report_path.unlink()
    
    def test_script_validates_project_structure(self):
        """Test that the script validates project structure correctly"""
        lean_dir = PROJECT_ROOT / "formalization" / "lean"
        report_path = lean_dir / "validation_report.json"
        
        # Clean up any existing report
        if report_path.exists():
            report_path.unlink()
        
        # Run the script
        result = subprocess.run(
            [sys.executable, "validate_lean_env.py"],
            cwd=lean_dir,
            capture_output=True,
            timeout=30,
            check=False  # Don't raise on non-zero exit (script may return 1 on validation fail)
        )
        
        # Ensure script completed
        assert result.returncode in [0, 1], f"Script failed unexpectedly: {result.stderr}"
        assert report_path.exists(), "validation_report.json was not created"
        
        with open(report_path, 'r') as f:
            report = json.load(f)
        
        # Since we know the project structure is valid, it should report true
        assert report["project"]["structure_valid"], \
            "Project structure should be valid"
        
        # Clean up after test
        if report_path.exists():
            report_path.unlink()


class TestLeanValidationWorkflow:
    """Tests for the lean-validation.yml GitHub Actions workflow"""
    
    def test_workflow_file_exists(self):
        """Test that lean-validation.yml exists"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        assert workflow_path.exists(), "lean-validation.yml not found"
        assert workflow_path.stat().st_size > 0, "Workflow file is empty"
    
    def test_workflow_yaml_is_valid(self):
        """Test that the workflow YAML is valid"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        try:
            import yaml
            with open(workflow_path, 'r') as f:
                workflow = yaml.safe_load(f)
            
            # Check basic structure
            assert "name" in workflow
            # Note: YAML may parse 'on' as boolean True
            assert ("on" in workflow or True in workflow)
            assert "jobs" in workflow
            
            # Check job structure
            assert "validate-lean" in workflow["jobs"]
            job = workflow["jobs"]["validate-lean"]
            assert "runs-on" in job
            assert "steps" in job
            
            # Check for required steps
            step_names = [step.get("name", "") for step in job["steps"]]
            
            # Check for key steps mentioned in problem statement
            assert any("Checkout" in name or "checkout" in name.lower() for name in step_names)
            assert any("Python" in name for name in step_names)
            assert any("Lean" in name for name in step_names)
            assert any("validation" in name.lower() for name in step_names)
            assert any("upload" in name.lower() or "artifact" in name.lower() for name in step_names)
            assert any("summary" in name.lower() for name in step_names)
            
        except ImportError:
            pytest.skip("PyYAML not installed, skipping YAML validation")
    
    def test_workflow_uses_correct_versions(self):
        """Test that workflow uses specified versions"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        # Check for Python 3.11
        assert "3.11" in content, "Should use Python 3.11"
        
        # Check for Lean 4.5.0
        assert "4.5.0" in content or "v4.5.0" in content, "Should use Lean 4.5.0"
        
        # Check for checkout@v4
        assert "checkout@v4" in content, "Should use checkout@v4"
        
        # Check for upload-artifact@v4
        assert "upload-artifact@v4" in content, "Should use upload-artifact@v4"
    
    def test_workflow_runs_script_in_correct_directory(self):
        """Test that workflow runs validation script in formalization/lean"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        # Check that script is run from formalization/lean
        assert "working-directory: formalization/lean" in content
        assert "validate_lean_env.py" in content
    
    def test_workflow_uploads_correct_artifact(self):
        """Test that workflow uploads validation_report.json"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        # Check artifact configuration
        assert "validation-report" in content
        assert "validation_report.json" in content
    
    def test_workflow_uses_jq_for_summary(self):
        """Test that workflow uses jq to format summary"""
        workflow_path = PROJECT_ROOT / ".github" / "workflows" / "lean-validation.yml"
        
        with open(workflow_path, 'r') as f:
            content = f.read()
        
        # Check that jq is used to parse JSON
        assert "jq" in content
        assert "GITHUB_STEP_SUMMARY" in content
        assert ".summary.status" in content
        assert ".build_time_sec" in content
        assert ".warnings" in content
        assert ".errors" in content


class TestGitignore:
    """Tests for .gitignore configuration"""
    
    def test_validation_report_in_gitignore(self):
        """Test that validation_report.json is in .gitignore"""
        gitignore_path = PROJECT_ROOT / ".gitignore"
        
        with open(gitignore_path, 'r') as f:
            content = f.read()
        
        # Check that validation report is ignored
        assert "validation_report.json" in content, \
            "validation_report.json should be in .gitignore"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
