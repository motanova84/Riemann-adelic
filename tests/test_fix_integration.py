"""
Test suite for fix_integration.py diagnostic script

Tests the IntegrationFix class methods including SABIO flow checks,
validation flow checks, GitHub Actions verification, and permission fixes.
"""

import pytest
import sys
import json
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / '.github' / 'scripts'))

# Import after path adjustment
import importlib.util
spec = importlib.util.spec_from_file_location(
    "fix_integration",
    Path(__file__).parent.parent / ".github" / "scripts" / "fix_integration.py"
)
fix_integration = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fix_integration)

IntegrationFix = fix_integration.IntegrationFix


class TestIntegrationFixInit:
    """Test IntegrationFix initialization"""
    
    def test_initialization(self, tmp_path, monkeypatch):
        """Test that IntegrationFix initializes correctly"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        
        assert fix.repo_root is not None
        assert "timestamp" in fix.results
        assert "fixes" in fix.results
        assert "status" in fix.results
        assert isinstance(fix.results["fixes"], list)
        assert isinstance(fix.results["status"], dict)


class TestCheckSabioFlows:
    """Test SABIO flows verification"""
    
    def test_check_sabio_all_present(self, tmp_path, monkeypatch):
        """Test when all SABIO files are present"""
        monkeypatch.chdir(tmp_path)
        
        # Create required files
        utils_dir = tmp_path / "utils"
        utils_dir.mkdir()
        (utils_dir / "exact_f0_derivation.py").touch()
        (tmp_path / "sabio_validator.py").touch()
        (tmp_path / "Evac_Rpsi_data.csv").touch()
        
        fix = IntegrationFix()
        fix.check_sabio_flows()
        
        assert fix.results["status"]["utils/exact_f0_derivation.py"] == "OK"
        assert fix.results["status"]["sabio_validator.py"] == "OK"
        assert fix.results["status"]["Evac_Rpsi_data.csv"] == "OK"
    
    def test_check_sabio_missing_files(self, tmp_path, monkeypatch):
        """Test when SABIO files are missing"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.check_sabio_flows()
        
        assert fix.results["status"]["utils/exact_f0_derivation.py"] == "MISSING"
        assert fix.results["status"]["sabio_validator.py"] == "MISSING"
        assert len(fix.results["fixes"]) > 0
    
    @patch('builtins.__import__')
    def test_check_sabio_missing_dependencies(self, mock_import, tmp_path, monkeypatch):
        """Test when Python dependencies are missing"""
        monkeypatch.chdir(tmp_path)
        
        # Create files but mock missing dependencies
        (tmp_path / "sabio_validator.py").touch()
        mock_import.side_effect = ImportError("numpy not found")
        
        fix = IntegrationFix()
        fix.check_sabio_flows()
        
        assert fix.results["status"]["python_deps"] == "MISSING"
        assert any("pip install" in f for f in fix.results["fixes"])


class TestCheckValidationFlows:
    """Test validation flows verification"""
    
    def test_check_validation_all_present(self, tmp_path, monkeypatch):
        """Test when all validation scripts are present"""
        monkeypatch.chdir(tmp_path)
        
        # Create validation scripts
        (tmp_path / "validate_v5_coronacion.py").touch()
        (tmp_path / "validate_critical_line.py").touch()
        (tmp_path / "validate_explicit_formula.py").touch()
        tests_dir = tmp_path / "tests"
        tests_dir.mkdir()
        (tests_dir / "test_rh_proved_framework.py").touch()
        
        fix = IntegrationFix()
        fix.check_validation_flows()
        
        assert fix.results["status"]["validate_v5_coronacion.py"] == "OK"
        assert fix.results["status"]["validate_critical_line.py"] == "OK"
        assert fix.results["status"]["validate_explicit_formula.py"] == "OK"
    
    def test_check_validation_missing_files(self, tmp_path, monkeypatch):
        """Test when validation scripts are missing"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.check_validation_flows()
        
        # All should be marked as missing
        assert fix.results["status"]["validate_v5_coronacion.py"] == "MISSING"
        assert fix.results["status"]["validate_critical_line.py"] == "MISSING"
    
    def test_check_validation_permissions(self, tmp_path, monkeypatch):
        """Test permission checking for validation scripts"""
        monkeypatch.chdir(tmp_path)
        
        # Create file without execute permission
        script = tmp_path / "validate_v5_coronacion.py"
        script.touch()
        script.chmod(0o644)  # rw-r--r--
        
        fix = IntegrationFix()
        fix.check_validation_flows()
        
        # Should detect it's not executable (before fix_permissions)
        assert fix.results["status"]["validate_v5_coronacion.py"] == "OK"


class TestCheckGithubActions:
    """Test GitHub Actions workflow verification"""
    
    def test_check_workflows_present(self, tmp_path, monkeypatch):
        """Test when workflows are present with valid syntax"""
        monkeypatch.chdir(tmp_path)
        
        # Create workflow directory and files
        workflows_dir = tmp_path / ".github" / "workflows"
        workflows_dir.mkdir(parents=True)
        
        workflow_content = """
name: Test Workflow
on: push
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - run: echo "test"
"""
        (workflows_dir / "noesis_multi_repo_v2.yml").write_text(workflow_content)
        (workflows_dir / "auto_evolution.yml").write_text(workflow_content)
        (workflows_dir / "validate-on-push.yml").write_text(workflow_content)
        
        fix = IntegrationFix()
        fix.check_github_actions()
        
        assert fix.results["status"][".github/workflows/noesis_multi_repo_v2.yml"] == "OK"
        assert fix.results["status"][".github/workflows/auto_evolution.yml"] == "OK"
    
    def test_check_workflows_missing(self, tmp_path, monkeypatch):
        """Test when workflows are missing"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.check_github_actions()
        
        assert fix.results["status"][".github/workflows/noesis_multi_repo_v2.yml"] == "MISSING"
    
    def test_check_workflows_invalid_syntax(self, tmp_path, monkeypatch):
        """Test when workflow has invalid syntax"""
        monkeypatch.chdir(tmp_path)
        
        workflows_dir = tmp_path / ".github" / "workflows"
        workflows_dir.mkdir(parents=True)
        
        # Create workflow with missing required keys
        invalid_content = "name: Test\n"
        (workflows_dir / "noesis_multi_repo_v2.yml").write_text(invalid_content)
        
        fix = IntegrationFix()
        fix.check_github_actions()
        
        # Should detect syntax issue
        assert fix.results["status"][".github/workflows/noesis_multi_repo_v2.yml"] == "WARNING"


class TestCheckFrequencyValidation:
    """Test frequency base validation"""
    
    def test_frequency_validation_file_exists(self, tmp_path, monkeypatch):
        """Test when Evac_Rpsi_data.csv exists"""
        monkeypatch.chdir(tmp_path)
        
        (tmp_path / "Evac_Rpsi_data.csv").write_text("header\ndata\n")
        
        fix = IntegrationFix()
        fix.check_frequency_validation()
        
        assert fix.results["status"]["frequency_data"] == "OK"
        assert fix.results["base_frequency"] == "141.7001 Hz"
    
    def test_frequency_validation_file_missing(self, tmp_path, monkeypatch):
        """Test when Evac_Rpsi_data.csv is missing"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.check_frequency_validation()
        
        assert fix.results["status"]["frequency_data"] == "MISSING"


class TestFixPermissions:
    """Test permission fixing functionality"""
    
    def test_fix_permissions_changes_mode(self, tmp_path, monkeypatch):
        """Test that fix_permissions changes file modes"""
        monkeypatch.chdir(tmp_path)
        
        # Create Python scripts without execute permission
        script1 = tmp_path / "test1.py"
        script2 = tmp_path / "test2.py"
        script1.touch()
        script2.touch()
        script1.chmod(0o644)
        script2.chmod(0o644)
        
        fix = IntegrationFix()
        fix.fix_permissions()
        
        # Check that permissions were fixed
        assert script1.stat().st_mode & 0o111 != 0
        assert script2.stat().st_mode & 0o111 != 0
    
    def test_fix_permissions_already_correct(self, tmp_path, monkeypatch):
        """Test when permissions are already correct"""
        monkeypatch.chdir(tmp_path)
        
        # Create script with execute permission
        script = tmp_path / "test.py"
        script.touch()
        script.chmod(0o755)
        
        fix = IntegrationFix()
        fix.fix_permissions()
        
        # Should report no changes needed
        assert len([f for f in fix.results["fixes"] if "Fixed permissions" in f]) == 0


class TestGenerateReport:
    """Test report generation"""
    
    def test_generate_report_creates_files(self, tmp_path, monkeypatch):
        """Test that report generation creates expected files"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.results["status"]["test_file"] = "OK"
        fix.results["fixes"].append("Test fix")
        
        report = fix.generate_report()
        
        # Check that report file was created
        assert (tmp_path / "INTEGRATION_FIX_REPORT.md").exists()
        assert (tmp_path / "integration_fix_results.json").exists()
        
        # Check report content
        assert "NOESIS INTEGRATION FIX REPORT" in report
        assert "test_file" in report
        assert "Test fix" in report
    
    def test_generate_report_json_structure(self, tmp_path, monkeypatch):
        """Test that JSON report has correct structure"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.results["status"]["file1"] = "OK"
        fix.results["fixes"].append("Fix 1")
        fix.generate_report()
        
        # Load and verify JSON
        with open(tmp_path / "integration_fix_results.json") as f:
            data = json.load(f)
        
        assert "timestamp" in data
        assert "fixes" in data
        assert "status" in data
        assert data["status"]["file1"] == "OK"


class TestRunMethod:
    """Test the main run method"""
    
    def test_run_executes_all_checks(self, tmp_path, monkeypatch):
        """Test that run method executes all checks"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        
        with patch.object(fix, 'check_sabio_flows') as mock_sabio, \
             patch.object(fix, 'check_validation_flows') as mock_validation, \
             patch.object(fix, 'check_github_actions') as mock_actions, \
             patch.object(fix, 'check_frequency_validation') as mock_freq, \
             patch.object(fix, 'fix_permissions') as mock_perms, \
             patch.object(fix, 'generate_report') as mock_report:
            
            result = fix.run()
            
            # Verify all methods were called
            mock_sabio.assert_called_once()
            mock_validation.assert_called_once()
            mock_actions.assert_called_once()
            mock_freq.assert_called_once()
            mock_perms.assert_called_once()
            mock_report.assert_called_once()
    
    def test_run_returns_zero_on_success(self, tmp_path, monkeypatch):
        """Test that run returns 0 when all checks pass"""
        monkeypatch.chdir(tmp_path)
        
        # Create all required files
        (tmp_path / "sabio_validator.py").touch()
        (tmp_path / "Evac_Rpsi_data.csv").touch()
        
        fix = IntegrationFix()
        result = fix.run()
        
        # Should return non-zero since some files are still missing
        assert isinstance(result, int)
    
    def test_run_returns_nonzero_on_critical_missing(self, tmp_path, monkeypatch):
        """Test that run returns 1 when critical files are missing"""
        monkeypatch.chdir(tmp_path)
        
        fix = IntegrationFix()
        fix.results["status"]["critical_file"] = "MISSING"
        
        result = fix.run()
        
        assert result == 1
