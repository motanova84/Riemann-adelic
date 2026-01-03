"""
Tests for the plagiarism monitoring system.
"""
import json
import os
import sys
from pathlib import Path

import pytest

# Add monitoring directory to path
monitoring_dir = Path(__file__).resolve().parents[1] / "monitoring"
sys.path.insert(0, str(monitoring_dir))


def test_fingerprints_exist():
    """Test that fingerprints.json exists and is valid."""
    fingerprints_path = monitoring_dir / "fingerprints.json"
    
    assert fingerprints_path.exists(), "fingerprints.json should exist"
    
    with open(fingerprints_path) as f:
        data = json.load(f)
    
    # Check structure
    assert "version" in data
    assert "doi" in data
    assert "files" in data
    assert "latex_snippets" in data
    assert "metadata" in data
    
    # Check DOI
    assert data["doi"] == "10.5281/zenodo.17116291"


def test_fingerprints_has_file_hashes():
    """Test that key files are fingerprinted."""
    fingerprints_path = monitoring_dir / "fingerprints.json"
    
    with open(fingerprints_path) as f:
        data = json.load(f)
    
    files = data.get("files", {})
    
    # Check that at least some key files are present
    assert len(files) > 0, "Should have at least one file fingerprinted"
    
    # Each file should have sha256 and size
    for file_name, file_info in files.items():
        assert "sha256" in file_info, f"{file_name} should have sha256"
        assert "size" in file_info, f"{file_name} should have size"
        assert len(file_info["sha256"]) == 64, f"{file_name} sha256 should be 64 chars"


def test_fingerprints_has_latex_snippets():
    """Test that LaTeX snippets are fingerprinted."""
    fingerprints_path = monitoring_dir / "fingerprints.json"
    
    with open(fingerprints_path) as f:
        data = json.load(f)
    
    snippets = data.get("latex_snippets", {})
    
    assert len(snippets) > 0, "Should have LaTeX snippets"
    
    # Check for key snippets
    expected_snippets = [
        "vacuum_energy",
        "adelic_operator",
        "spectral_theorem",
        "riemann_hypothesis",
        "discrete_symmetry"
    ]
    
    for snippet_name in expected_snippets:
        assert snippet_name in snippets, f"Should have {snippet_name} snippet"
        assert "content" in snippets[snippet_name]
        assert "sha256" in snippets[snippet_name]


def test_config_exists():
    """Test that config.json exists and is valid."""
    config_path = monitoring_dir / "config.json"
    
    assert config_path.exists(), "config.json should exist"
    
    with open(config_path) as f:
        config = json.load(f)
    
    # Check structure
    assert "monitoring" in config
    assert "thresholds" in config
    assert "search_queries" in config
    
    # Check monitoring is enabled
    assert config["monitoring"]["enabled"] is True


def test_monitoring_scripts_exist():
    """Test that all monitoring scripts exist."""
    required_scripts = [
        "fingerprints_create.py",
        "search_github.py",
        "search_crossref.py",
        "check_url_similarity.py",
        "run_monitor.py"
    ]
    
    for script in required_scripts:
        script_path = monitoring_dir / script
        assert script_path.exists(), f"{script} should exist"
        assert script_path.stat().st_size > 0, f"{script} should not be empty"


def test_readme_exists():
    """Test that monitoring README exists."""
    readme_path = monitoring_dir / "README.md"
    assert readme_path.exists(), "monitoring/README.md should exist"
    
    content = readme_path.read_text()
    assert "Plagiarism Monitoring" in content
    assert "fingerprints" in content.lower()


def test_directories_exist():
    """Test that required directories exist."""
    alerts_dir = monitoring_dir / "alerts"
    evidence_dir = monitoring_dir / "evidence"
    
    assert alerts_dir.exists(), "alerts directory should exist"
    assert evidence_dir.exists(), "evidence directory should exist"


def test_security_md_exists():
    """Test that SECURITY.md exists in repo root."""
    repo_root = Path(__file__).resolve().parents[1]
    security_path = repo_root / "SECURITY.md"
    
    assert security_path.exists(), "SECURITY.md should exist"
    
    content = security_path.read_text()
    assert "monitoring" in content.lower()
    assert "plagiarism" in content.lower()


def test_copyright_md_exists():
    """Test that COPYRIGHT.md exists in repo root."""
    repo_root = Path(__file__).resolve().parents[1]
    copyright_path = repo_root / "COPYRIGHT.md"
    
    assert copyright_path.exists(), "COPYRIGHT.md should exist"
    
    content = copyright_path.read_text()
    assert "José Manuel Mota Burruezo" in content
    assert "10.5281/zenodo.17116291" in content


def test_github_workflow_exists():
    """Test that monitoring workflow exists."""
    repo_root = Path(__file__).resolve().parents[1]
    workflow_path = repo_root / ".github" / "workflows" / "monitor.yml"
    
    assert workflow_path.exists(), "monitor.yml workflow should exist"
    
    content = workflow_path.read_text()
    assert "Plagiarism Monitoring" in content
    assert "fingerprints_create.py" in content
    assert "run_monitor.py" in content


def test_sha256_calculation():
    """Test SHA256 calculation works correctly."""
    from fingerprints_create import sha256_of_text
    
    # Test known value
    result = sha256_of_text("test")
    expected = "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08"
    assert result == expected


def test_fingerprints_can_be_regenerated():
    """Test that fingerprints can be regenerated."""
    from fingerprints_create import create_fingerprints
    
    # This should not raise an exception
    fingerprints = create_fingerprints()
    
    assert fingerprints is not None
    assert "files" in fingerprints
    assert "latex_snippets" in fingerprints


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
