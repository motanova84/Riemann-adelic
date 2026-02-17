"""
Test suite for verify_sabio.py diagnostic script

Tests the SABIO ∞³ verification functions including frequency validation,
file checks, Lean formalization verification, and Python module checks.
"""

import pytest
import sys
import json
from pathlib import Path
from unittest.mock import Mock, patch, mock_open

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / '.github' / 'scripts'))

# Import after path adjustment
import importlib.util
spec = importlib.util.spec_from_file_location(
    "verify_sabio",
    Path(__file__).parent.parent / ".github" / "scripts" / "verify_sabio.py"
)
verify_sabio = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify_sabio)


class TestVerifyFrequency:
    """Test frequency verification function"""
    
    def test_frequency_verification_with_existing_file(self, tmp_path, monkeypatch):
        """Test frequency verification when Evac_Rpsi_data.csv exists"""
        # Change to temp directory
        monkeypatch.chdir(tmp_path)
        
        # Create mock Evac_Rpsi_data.csv
        evac_file = tmp_path / "Evac_Rpsi_data.csv"
        evac_file.write_text("header\ndata1\ndata2\ndata3\n")
        
        result = verify_sabio.verify_frequency()
        
        assert result is True
    
    def test_frequency_verification_with_missing_file(self, tmp_path, monkeypatch):
        """Test frequency verification when file is missing"""
        # Change to temp directory without the file
        monkeypatch.chdir(tmp_path)
        
        result = verify_sabio.verify_frequency()
        
        assert result is False
    
    def test_frequency_verification_with_exception(self, monkeypatch):
        """Test frequency verification handles exceptions gracefully"""
        def mock_exists():
            raise PermissionError("Access denied")
        
        # Mock Path.exists to raise exception
        with patch('pathlib.Path.exists', side_effect=mock_exists):
            result = verify_sabio.verify_frequency()
            assert result is False


class TestVerifySabioFiles:
    """Test SABIO files verification function"""
    
    def test_verify_sabio_files_all_present(self, tmp_path, monkeypatch):
        """Test when all SABIO files are present"""
        monkeypatch.chdir(tmp_path)
        
        # Create all required files
        (tmp_path / ".sabio").mkdir()
        (tmp_path / "sabio_validator.py").touch()
        (tmp_path / "utils").mkdir()
        (tmp_path / "utils" / "exact_f0_derivation.py").touch()
        
        result = verify_sabio.verify_sabio_files()
        
        assert result is True
    
    def test_verify_sabio_files_partial(self, tmp_path, monkeypatch):
        """Test when only some SABIO files are present"""
        monkeypatch.chdir(tmp_path)
        
        # Create only one file
        (tmp_path / "sabio_validator.py").touch()
        
        result = verify_sabio.verify_sabio_files()
        
        # Should still return True if at least one file found
        assert result is True
    
    def test_verify_sabio_files_none_present(self, tmp_path, monkeypatch):
        """Test when no SABIO files are present"""
        monkeypatch.chdir(tmp_path)
        
        result = verify_sabio.verify_sabio_files()
        
        assert result is False


class TestVerifyLeanFormalization:
    """Test Lean formalization verification function"""
    
    def test_verify_lean_with_lakefile(self, tmp_path, monkeypatch):
        """Test Lean verification when lakefile exists"""
        monkeypatch.chdir(tmp_path)
        
        # Create Lean directory structure
        lean_dir = tmp_path / "formalization" / "lean"
        lean_dir.mkdir(parents=True)
        (lean_dir / "lakefile.lean").touch()
        (lean_dir / "test1.lean").touch()
        (lean_dir / "test2.lean").touch()
        
        result = verify_sabio.verify_lean_formalization()
        
        # Returns False because no SABIO files, but doesn't crash
        assert result is False
    
    def test_verify_lean_with_sabio_files(self, tmp_path, monkeypatch):
        """Test Lean verification when SABIO files exist"""
        monkeypatch.chdir(tmp_path)
        
        # Create Lean directory with SABIO files
        lean_dir = tmp_path / "formalization" / "lean"
        lean_dir.mkdir(parents=True)
        (lean_dir / "lakefile.lean").touch()
        (lean_dir / "sabio_test.lean").touch()
        (lean_dir / "another_sabio.lean").touch()
        
        result = verify_sabio.verify_lean_formalization()
        
        assert result is True
    
    def test_verify_lean_no_directory(self, tmp_path, monkeypatch):
        """Test Lean verification when directory doesn't exist"""
        monkeypatch.chdir(tmp_path)
        
        result = verify_sabio.verify_lean_formalization()
        
        assert result is False


class TestVerifyPythonModules:
    """Test Python modules verification function"""
    
    def test_verify_python_modules_all_present(self):
        """Test when all required modules are available"""
        # numpy, scipy, mpmath, sympy should be installed in test environment
        result = verify_sabio.verify_python_modules()
        
        # May return True or False depending on test environment
        # Just ensure it doesn't crash
        assert isinstance(result, bool)
    
    @patch('builtins.__import__')
    def test_verify_python_modules_missing(self, mock_import):
        """Test when modules are missing"""
        mock_import.side_effect = ImportError("Module not found")
        
        result = verify_sabio.verify_python_modules()
        
        assert result is False


class TestMainFunction:
    """Test main function integration"""
    
    def test_main_all_pass(self, tmp_path, monkeypatch):
        """Test main function when all checks pass"""
        monkeypatch.chdir(tmp_path)
        
        # Create all required files for checks to pass
        (tmp_path / "Evac_Rpsi_data.csv").write_text("header\ndata\n")
        (tmp_path / ".sabio").mkdir()
        (tmp_path / "sabio_validator.py").touch()
        utils_dir = tmp_path / "utils"
        utils_dir.mkdir()
        (utils_dir / "exact_f0_derivation.py").touch()
        
        lean_dir = tmp_path / "formalization" / "lean"
        lean_dir.mkdir(parents=True)
        (lean_dir / "lakefile.lean").touch()
        (lean_dir / "sabio_test.lean").touch()
        
        result = verify_sabio.main()
        
        assert result == 0
        # Check JSON report was created
        assert (tmp_path / "sabio_verification_report.json").exists()
    
    def test_main_some_fail(self, tmp_path, monkeypatch):
        """Test main function when some checks fail"""
        monkeypatch.chdir(tmp_path)
        
        # Only create frequency file, everything else fails
        (tmp_path / "Evac_Rpsi_data.csv").write_text("header\ndata\n")
        
        result = verify_sabio.main()
        
        assert result == 1
        # Check JSON report was created even with failures
        assert (tmp_path / "sabio_verification_report.json").exists()
        
        # Verify report content
        with open(tmp_path / "sabio_verification_report.json") as f:
            report = json.load(f)
            assert report["frequency"] is True
            assert report["sabio_files"] is False
            assert report["lean_formalization"] is False
            # python_modules check depends on environment, so we don't assert it
