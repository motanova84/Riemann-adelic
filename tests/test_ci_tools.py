"""
Tests for CI tools: metadata verification and conversion smoke test.
"""

import json
import subprocess
import sys
from pathlib import Path


# Get the project root directory
PROJECT_ROOT = Path(__file__).parent.parent


def test_verify_metadata_tool_exists():
    """Test that the verify_metadata.py tool exists."""
    tool_path = PROJECT_ROOT / "tools" / "verify_metadata.py"
    assert tool_path.exists(), f"Tool not found: {tool_path}"


def test_convert_example_tool_exists():
    """Test that the convert_example.py tool exists."""
    tool_path = PROJECT_ROOT / "tools" / "convert_example.py"
    assert tool_path.exists(), f"Tool not found: {tool_path}"


def test_metadata_example_exists():
    """Test that the metadata example file exists."""
    metadata_path = PROJECT_ROOT / "schema" / "metadata_example.jsonld"
    assert metadata_path.exists(), f"Metadata file not found: {metadata_path}"


def test_metadata_example_is_valid_json():
    """Test that the metadata example is valid JSON."""
    metadata_path = PROJECT_ROOT / "schema" / "metadata_example.jsonld"
    with open(metadata_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    assert isinstance(data, dict), "Metadata should be a JSON object"
    assert "@context" in data, "Metadata should have @context"


def test_lean_example_exists():
    """Test that the Lean example file exists."""
    lean_path = PROJECT_ROOT / "tests" / "examples" / "example_lean.lean"
    assert lean_path.exists(), f"Lean example not found: {lean_path}"


def test_verify_metadata_script_runs():
    """Test that the verify_metadata.py script runs successfully."""
    tool_path = PROJECT_ROOT / "tools" / "verify_metadata.py"
    metadata_path = PROJECT_ROOT / "schema" / "metadata_example.jsonld"

    result = subprocess.run(
        [sys.executable, str(tool_path), str(metadata_path)],
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, f"Script failed: {result.stderr}"
    assert "✅" in result.stdout, "Expected success message in output"


def test_convert_example_script_runs():
    """Test that the convert_example.py script runs successfully."""
    tool_path = PROJECT_ROOT / "tools" / "convert_example.py"
    lean_path = PROJECT_ROOT / "tests" / "examples" / "example_lean.lean"

    result = subprocess.run(
        [sys.executable, str(tool_path), str(lean_path)],
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, f"Script failed: {result.stderr}"
    assert "✅" in result.stdout, "Expected success message in output"


def test_verify_metadata_fails_on_missing_file():
    """Test that verify_metadata.py fails on missing file."""
    tool_path = PROJECT_ROOT / "tools" / "verify_metadata.py"
    nonexistent_path = PROJECT_ROOT / "nonexistent.jsonld"

    result = subprocess.run(
        [sys.executable, str(tool_path), str(nonexistent_path)],
        capture_output=True,
        text=True,
    )

    assert result.returncode == 1, "Script should fail on missing file"
    assert "❌" in result.stdout, "Expected error message in output"


def test_convert_example_fails_on_missing_file():
    """Test that convert_example.py fails on missing file."""
    tool_path = PROJECT_ROOT / "tools" / "convert_example.py"
    nonexistent_path = PROJECT_ROOT / "nonexistent.lean"

    result = subprocess.run(
        [sys.executable, str(tool_path), str(nonexistent_path)],
        capture_output=True,
        text=True,
    )

    assert result.returncode == 1, "Script should fail on missing file"
    assert "❌" in result.stdout, "Expected error message in output"
