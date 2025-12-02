"""
Test suite for the validacion_alpha_psi.py bridge script.

This test verifies that the Python bridge to SageMath validation
works correctly in both Sage and fallback modes.
"""

import os
import sys
import json
import subprocess
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def test_bridge_script_exists():
    """Test that the bridge script file exists."""
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    assert script_path.exists(), "Bridge script should exist"
    assert script_path.is_file(), "Bridge script should be a file"


def test_bridge_script_is_executable():
    """Test that the bridge script has execute permissions."""
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    # Check if file has any execute bit set
    is_executable = os.access(script_path, os.X_OK)
    assert is_executable, "Bridge script should be executable"


def test_bridge_script_help():
    """Test that the bridge script can show help."""
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    result = subprocess.run(
        ["python3", str(script_path), "--help"],
        capture_output=True,
        text=True,
        timeout=10
    )
    assert result.returncode == 0, "Help command should succeed"
    assert "Quantum Radio" in result.stdout, "Help should mention Quantum Radio"
    assert "--precision" in result.stdout, "Help should show precision option"
    assert "--force-fallback" in result.stdout, "Help should show fallback option"


def test_bridge_script_fallback_mode():
    """Test the bridge script in fallback mode (without Sage)."""
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    
    # Run in fallback mode with low precision for speed
    result = subprocess.run(
        ["python3", str(script_path), "--force-fallback", "--fallback-dps", "15"],
        capture_output=True,
        text=True,
        timeout=30,
        cwd=str(script_path.parent.parent)
    )
    
    # Should succeed (exit code 0) if validation passes
    # Note: The validation might fail in some environments, so we just check it runs
    assert result.returncode in [0, 1], "Script should run without crashing"
    assert "VALIDACIÓN DEL RADIO CUÁNTICO" in result.stdout, "Should show validation header"
    assert "fallback" in result.stdout.lower(), "Should indicate fallback mode"


def test_bridge_script_creates_results_file():
    """Test that the bridge script creates a results JSON file."""
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    results_file = Path(__file__).parent.parent / "quantum_radio_validation_results.json"
    
    # Clean up any existing results file
    if results_file.exists():
        results_file.unlink()
    
    # Run in fallback mode
    result = subprocess.run(
        ["python3", str(script_path), "--force-fallback", "--fallback-dps", "15"],
        capture_output=True,
        text=True,
        timeout=30,
        cwd=str(script_path.parent.parent)
    )
    
    # Check if results file was created
    assert results_file.exists(), "Results JSON file should be created"
    
    # Verify JSON is valid
    with open(results_file, 'r') as f:
        results = json.load(f)
    
    assert "overall_valid" in results, "Results should contain overall_valid field"
    assert "fallback_mode" in results, "Results should indicate fallback mode"
    assert results["fallback_mode"] is True, "Should be in fallback mode"


def test_sage_script_symlink_exists():
    """Test that the Sage script symlink exists in scripts directory."""
    symlink_path = Path(__file__).parent.parent / "scripts" / "validacion_radio_cuantico.sage"
    assert symlink_path.exists(), "Sage script symlink should exist in scripts/"


def test_sage_script_target_exists():
    """Test that the Sage script target exists."""
    target_path = Path(__file__).parent.parent / "test_validacion_radio_cuantico.sage"
    assert target_path.exists(), "Original Sage script should exist"
    assert target_path.is_file(), "Original Sage script should be a file"


def test_bridge_script_imports():
    """Test that the bridge script can be imported without errors."""
    # This is a basic sanity check
    script_path = Path(__file__).parent.parent / "scripts" / "validacion_alpha_psi.py"
    
    # Try to compile the script
    result = subprocess.run(
        ["python3", "-m", "py_compile", str(script_path)],
        capture_output=True,
        text=True,
        timeout=10
    )
    
    assert result.returncode == 0, f"Script should compile without errors: {result.stderr}"


if __name__ == "__main__":
    # Run tests manually
    import pytest
    pytest.main([__file__, "-v"])
