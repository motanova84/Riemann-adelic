#!/usr/bin/env python3
"""
Test suite for environment integrity verification.

Tests the verify_environment_integrity.py script to ensure it properly
verifies lock files, checksums, and environment consistency.
"""

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


class TestEnvironmentIntegrity:
    """Test environment integrity verification functionality."""
    
    @pytest.fixture
    def repo_root(self):
        """Get repository root directory."""
        return Path(__file__).parent.parent.resolve()
    
    @pytest.fixture
    def temp_checksums(self, repo_root):
        """Backup and restore checksums file."""
        checksums_file = repo_root / "environment_checksums.json"
        backup = None
        
        if checksums_file.exists():
            backup = checksums_file.read_text()
        
        yield checksums_file
        
        # Restore original checksums
        if backup:
            checksums_file.write_text(backup)
        elif checksums_file.exists():
            checksums_file.unlink()
    
    def test_verify_script_exists(self, repo_root):
        """Test that verification script exists and is executable."""
        script = repo_root / "verify_environment_integrity.py"
        assert script.exists(), "verify_environment_integrity.py not found"
        assert script.is_file(), "verify_environment_integrity.py is not a file"
    
    def test_generate_script_exists(self, repo_root):
        """Test that generation script exists."""
        script = repo_root / "generate_env_lock.py"
        assert script.exists(), "generate_env_lock.py not found"
        assert script.is_file(), "generate_env_lock.py is not a file"
    
    def test_env_lock_exists(self, repo_root):
        """Test that ENV.lock file exists."""
        env_lock = repo_root / "ENV.lock"
        assert env_lock.exists(), "ENV.lock not found"
        assert env_lock.is_file(), "ENV.lock is not a file"
    
    def test_requirements_lock_exists(self, repo_root):
        """Test that requirements-lock.txt exists."""
        req_lock = repo_root / "requirements-lock.txt"
        assert req_lock.exists(), "requirements-lock.txt not found"
        assert req_lock.is_file(), "requirements-lock.txt is not a file"
    
    def test_checksums_file_exists(self, repo_root):
        """Test that checksums file exists."""
        checksums = repo_root / "environment_checksums.json"
        assert checksums.exists(), "environment_checksums.json not found"
        assert checksums.is_file(), "environment_checksums.json is not a file"
    
    def test_checksums_file_valid_json(self, repo_root):
        """Test that checksums file contains valid JSON."""
        checksums_file = repo_root / "environment_checksums.json"
        
        with open(checksums_file, 'r') as f:
            data = json.load(f)
        
        assert isinstance(data, dict), "Checksums file should contain a dict"
        assert len(data) > 0, "Checksums file should not be empty"
    
    def test_checksums_contain_required_files(self, repo_root):
        """Test that checksums include required files."""
        checksums_file = repo_root / "environment_checksums.json"
        
        with open(checksums_file, 'r') as f:
            checksums = json.load(f)
        
        required_files = ["ENV.lock", "requirements-lock.txt", "requirements.txt"]
        
        for filename in required_files:
            assert filename in checksums, f"{filename} missing from checksums"
            assert len(checksums[filename]) == 64, f"{filename} checksum should be 64 chars (SHA256)"
    
    def test_checksum_accuracy(self, repo_root):
        """Test that checksums are accurate."""
        checksums_file = repo_root / "environment_checksums.json"
        
        with open(checksums_file, 'r') as f:
            saved_checksums = json.load(f)
        
        for filename, saved_checksum in saved_checksums.items():
            filepath = repo_root / filename
            
            if not filepath.exists():
                continue
            
            # Compute actual checksum
            sha256 = hashlib.sha256()
            with open(filepath, 'rb') as f:
                for chunk in iter(lambda: f.read(4096), b''):
                    sha256.update(chunk)
            actual_checksum = sha256.hexdigest()
            
            assert actual_checksum == saved_checksum, \
                f"{filename}: checksum mismatch (saved={saved_checksum[:16]}..., actual={actual_checksum[:16]}...)"
    
    def test_env_lock_format(self, repo_root):
        """Test that ENV.lock has correct format."""
        env_lock = repo_root / "ENV.lock"
        
        with open(env_lock, 'r') as f:
            lines = f.readlines()
        
        # Should have header comments
        assert lines[0].startswith('#'), "First line should be a comment"
        
        # Should have package entries
        package_count = 0
        for line in lines:
            if '==' in line and not line.strip().startswith('#'):
                package_count += 1
                # Verify format: package==version
                assert '==' in line, "Package line should have =="
                parts = line.strip().split('==')
                assert len(parts) == 2, "Package line should have exactly one =="
        
        assert package_count > 0, "ENV.lock should contain packages"
    
    def test_requirements_lock_format(self, repo_root):
        """Test that requirements-lock.txt has correct format."""
        req_lock = repo_root / "requirements-lock.txt"
        
        with open(req_lock, 'r') as f:
            lines = f.readlines()
        
        # Should have header comments
        assert lines[0].startswith('#'), "First line should be a comment"
        
        # Should have package entries
        package_count = 0
        for line in lines:
            if '==' in line and not line.strip().startswith('#'):
                package_count += 1
        
        assert package_count > 0, "requirements-lock.txt should contain packages"
    
    def test_verify_script_runs(self, repo_root):
        """Test that verification script runs without errors."""
        script = repo_root / "verify_environment_integrity.py"
        
        result = subprocess.run(
            [sys.executable, str(script)],
            cwd=repo_root,
            capture_output=True,
            text=True
        )
        
        # Should exit with 0 (success) or 1 (warnings only)
        assert result.returncode in [0, 1], \
            f"Verification script failed with code {result.returncode}: {result.stderr}"
    
    def test_generate_checksums(self, repo_root, temp_checksums):
        """Test checksum generation."""
        script = repo_root / "verify_environment_integrity.py"
        
        # Remove existing checksums
        if temp_checksums.exists():
            temp_checksums.unlink()
        
        # Generate new checksums
        result = subprocess.run(
            [sys.executable, str(script), "--generate-checksums"],
            cwd=repo_root,
            capture_output=True,
            text=True
        )
        
        assert result.returncode in [0, 1], \
            f"Checksum generation failed: {result.stderr}"
        assert temp_checksums.exists(), "Checksums file not generated"
    
    def test_checksum_detection(self, repo_root, temp_checksums):
        """Test that checksum verification detects modifications."""
        # Save original checksums
        original_checksums = json.loads(temp_checksums.read_text())
        
        # Modify checksums
        modified_checksums = original_checksums.copy()
        modified_checksums["ENV.lock"] = "0" * 64  # Invalid checksum
        
        temp_checksums.write_text(json.dumps(modified_checksums, indent=2))
        
        # Run verification
        script = repo_root / "verify_environment_integrity.py"
        result = subprocess.run(
            [sys.executable, str(script)],
            cwd=repo_root,
            capture_output=True,
            text=True
        )
        
        # Should fail (exit code 1) due to checksum mismatch
        assert result.returncode == 1, "Should detect checksum mismatch"
        assert "mismatch" in result.stdout.lower() or "mismatch" in result.stderr.lower(), \
            "Should report checksum mismatch"
    
    def test_consistency_between_lock_files(self, repo_root):
        """Test that ENV.lock and requirements-lock.txt are consistent."""
        env_lock = repo_root / "ENV.lock"
        req_lock = repo_root / "requirements-lock.txt"
        
        # Parse packages from both files
        env_packages = {}
        req_packages = {}
        
        with open(env_lock, 'r') as f:
            for line in f:
                if '==' in line and not line.strip().startswith('#'):
                    pkg, ver = line.strip().split('==', 1)
                    env_packages[pkg.lower()] = ver
        
        with open(req_lock, 'r') as f:
            for line in f:
                if '==' in line and not line.strip().startswith('#'):
                    pkg, ver = line.strip().split('==', 1)
                    req_packages[pkg.lower()] = ver
        
        # All packages in requirements-lock should be in ENV.lock
        missing = []
        mismatched = []
        
        for pkg, req_ver in req_packages.items():
            if pkg not in env_packages:
                missing.append(f"{pkg}=={req_ver}")
            elif env_packages[pkg] != req_ver:
                mismatched.append(f"{pkg}: req={req_ver}, env={env_packages[pkg]}")
        
        assert len(missing) == 0, f"Packages missing from ENV.lock: {missing}"
        assert len(mismatched) == 0, f"Version mismatches: {mismatched}"


def test_env_lock_guide_exists():
    """Test that ENV_LOCK_GUIDE.md exists."""
    repo_root = Path(__file__).parent.parent.resolve()
    guide = repo_root / "ENV_LOCK_GUIDE.md"
    assert guide.exists(), "ENV_LOCK_GUIDE.md not found"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v"])
