#!/usr/bin/env python3
"""
Tests for validate_v5_coronacion.py working directory check

This test suite validates that validate_v5_coronacion.py correctly enforces
execution from the repository root directory.

Author: Copilot Agent
Date: January 2026
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest


class TestValidateV5CwdCheck:
    """Test suite for validate_v5_coronacion.py working directory verification."""
    
    def setup_method(self):
        """Setup for each test method."""
        # Find the repository root (where this test file's parent's parent is)
        self.test_dir = Path(__file__).parent
        self.repo_root = self.test_dir.parent
        self.script_path = self.repo_root / "validate_v5_coronacion.py"
        
        # Verify the script exists
        assert self.script_path.exists(), f"Script not found at {self.script_path}"
    
    def test_script_runs_from_repo_root(self):
        """
        Test that the script runs (or at least passes the cwd check) when executed
        from the repository root directory.
        
        The script may fail on imports if dependencies aren't installed, but it
        should NOT fail with the "wrong directory" error message.
        """
        result = subprocess.run(
            [sys.executable, "validate_v5_coronacion.py", "--help"],
            cwd=self.repo_root,
            capture_output=True,
            text=True
        )
        
        # Check that we don't get the "wrong directory" error
        assert "❌ ERROR: Script must be executed from the repository root directory" not in result.stdout
        assert "❌ ERROR: Script must be executed from the repository root directory" not in result.stderr
        
        # The script might fail on missing dependencies, which is fine
        # We just want to ensure the directory check passed
    
    def test_script_fails_from_wrong_directory(self, tmp_path):
        """
        Test that the script fails with appropriate error message when executed
        from a directory that is NOT the repository root.
        
        Args:
            tmp_path: pytest fixture providing a temporary directory
        """
        result = subprocess.run(
            [sys.executable, str(self.script_path), "--help"],
            cwd=tmp_path,
            capture_output=True,
            text=True
        )
        
        # Should fail with exit code 1
        assert result.returncode == 1
        
        # Should show the error message
        output = result.stdout + result.stderr
        assert "❌ ERROR: Script must be executed from the repository root directory" in output
        assert "Missing expected files:" in output
        assert "validate_v5_coronacion.py" in output
        assert "requirements.txt" in output
        assert "README.md" in output
        assert ".qcal_beacon" in output
    
    def test_error_message_provides_guidance(self, tmp_path):
        """
        Test that the error message provides clear guidance on how to fix the issue.
        """
        result = subprocess.run(
            [sys.executable, str(self.script_path), "--help"],
            cwd=tmp_path,
            capture_output=True,
            text=True
        )
        
        output = result.stdout + result.stderr
        
        # Check for helpful instructions
        assert "Navigate to the repository root directory" in output
        assert "cd /path/to/Riemann-adelic" in output
        assert "python validate_v5_coronacion.py" in output
    
    def test_cwd_shown_in_error_message(self, tmp_path):
        """
        Test that the error message shows the current working directory
        to help users understand where they are.
        """
        result = subprocess.run(
            [sys.executable, str(self.script_path), "--help"],
            cwd=tmp_path,
            capture_output=True,
            text=True
        )
        
        output = result.stdout + result.stderr
        
        # Should show the current working directory
        assert "Current working directory:" in output
        assert str(tmp_path) in output
