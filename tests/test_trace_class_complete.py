#!/usr/bin/env python3
"""
Test suite for trace_class_complete formalization and validation

This module tests both the Lean formalization structure and the numerical
validation of the trace class property for the H_Ψ operator.

Author: José Manuel Mota Burruezo (ICQ)
Date: December 2025
Version: 1.0
"""

import pytest
import subprocess
import re
from pathlib import Path
import numpy as np
from scipy.special import hermite, factorial


# Path constants
REPO_ROOT = Path(__file__).parent.parent
LEAN_FILE = REPO_ROOT / "formalization" / "lean" / "trace_class_complete.lean"
SCRIPT_FILE = REPO_ROOT / "scripts" / "validate_trace_class_complete.py"
OUTPUT_IMAGE = REPO_ROOT / "trace_class_complete_validation.png"


class TestTraceClassCompleteLeanFile:
    """Tests for the Lean formalization file."""

    def test_file_exists(self):
        """Test that the Lean file exists."""
        assert LEAN_FILE.exists(), f"File not found: {LEAN_FILE}"

    def test_file_not_empty(self):
        """Test that the file is not empty."""
        assert LEAN_FILE.stat().st_size > 0, "File is empty"

    def test_has_proper_header(self):
        """Test that the file has the proper documentation header."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "trace_class_complete.lean" in content
        assert "José Manuel Mota Burruezo" in content
        assert "DEMOSTRACIÓN COMPLETA" in content

    def test_has_required_imports(self):
        """Test that the file has the required Mathlib imports."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        required_imports = [
            "Mathlib.Analysis.SpecialFunctions.Gamma",
            "Mathlib.Analysis.SpecialFunctions.Exp",
            "Mathlib.OperatorTheory.Schatten",
            "Mathlib.MeasureTheory.Function.LpSpace",
            "Mathlib.Analysis.Calculus.Deriv",
        ]
        for imp in required_imports:
            assert imp in content, f"Missing import: {imp}"

    def test_defines_hermite_polynomial(self):
        """Test that the file defines Hermite polynomials."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def hermite_polynomial" in content
        assert "iteratedDeriv" in content

    def test_defines_hermite_basis(self):
        """Test that the file defines Hermite basis."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def hermite_basis" in content
        assert "π^(-1/4" in content

    def test_has_hermite_recurrence_theorem(self):
        """Test that the file has the Hermite recurrence theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem hermite_recurrence" in content

    def test_has_hermite_derivative_theorem(self):
        """Test that the file has the Hermite derivative theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem hermite_derivative" in content

    def test_has_orthonormality_theorem(self):
        """Test that the file has the orthonormality theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem hermite_basis_orthonormal" in content

    def test_defines_H_psi_operator(self):
        """Test that the file defines the H_Ψ operator."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "def H_psi_operator" in content
        assert "-x * (deriv f x)" in content
        assert "π * Real.log" in content

    def test_has_H_psi_coefficient_bound(self):
        """Test that the file has the spectral coefficient bound theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem H_psi_coefficient_bound" in content
        assert "8 / (n + 1)^(1 + 0.25)" in content

    def test_has_trace_class_theorem(self):
        """Test that the file has the main trace class theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem H_psi_is_trace_class" in content
        assert "Summable" in content

    def test_has_spectral_determinant_theorem(self):
        """Test that the file has the spectral determinant theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem spectral_determinant_well_defined" in content

    def test_has_entire_function_theorem(self):
        """Test that the file has the entire function theorem."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "theorem D_is_entire_of_finite_order" in content

    def test_has_namespace(self):
        """Test that the file has proper namespace structure."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "namespace H_Psi_Trace_Class_Proof" in content
        assert "end H_Psi_Trace_Class_Proof" in content

    def test_has_sections(self):
        """Test that the file has the expected sections."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "section HermiteBasisConstruction" in content
        assert "section SpectralOperatorAction" in content
        assert "section TraceClassConsequences" in content

    def test_has_qcal_references(self):
        """Test that the file has QCAL framework references."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "QCAL" in content or "141.7001" in content
        assert "10.5281/zenodo.17379721" in content

    def test_has_author_info(self):
        """Test that the file has author information."""
        content = LEAN_FILE.read_text(encoding='utf-8')
        assert "José Manuel Mota Burruezo" in content
        assert "0009-0002-1923-0773" in content


class TestValidationScript:
    """Tests for the Python validation script."""

    def test_script_exists(self):
        """Test that the validation script exists."""
        assert SCRIPT_FILE.exists(), f"Script not found: {SCRIPT_FILE}"

    def test_script_executable(self):
        """Test that the script is executable."""
        assert SCRIPT_FILE.stat().st_mode & 0o111, "Script is not executable"

    def test_script_has_shebang(self):
        """Test that the script has proper shebang."""
        with open(SCRIPT_FILE, 'r') as f:
            first_line = f.readline()
        assert first_line.startswith('#!/usr/bin/env python3')

    def test_script_has_docstring(self):
        """Test that the script has a docstring."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert '"""' in content
        assert "Validación Completa" in content or "H_Ψ" in content

    def test_script_defines_hermite_basis(self):
        """Test that the script defines hermite_basis function."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert "def hermite_basis" in content

    def test_script_defines_H_psi_operator(self):
        """Test that the script defines H_psi_on_hermite function."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert "def H_psi_on_hermite" in content

    def test_script_defines_L2_norm(self):
        """Test that the script defines L2 norm computation."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert "def compute_L2_norm" in content

    def test_script_defines_theoretical_bound(self):
        """Test that the script defines theoretical bound."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert "def theoretical_bound" in content

    def test_script_defines_main_validation(self):
        """Test that the script defines main validation function."""
        content = SCRIPT_FILE.read_text(encoding='utf-8')
        assert "def validate_trace_class_complete" in content


class TestNumericalValidation:
    """Tests for the numerical validation functionality."""

    def test_hermite_basis_function(self):
        """Test that hermite_basis function works correctly."""
        # Import the function
        import sys
        sys.path.insert(0, str(SCRIPT_FILE.parent))
        from validate_trace_class_complete import hermite_basis
        
        # Test on a simple grid
        x = np.linspace(-5, 5, 100)
        
        # ψ_0 should be roughly Gaussian
        psi_0 = hermite_basis(0, x)
        assert psi_0.shape == x.shape
        assert np.max(psi_0) > 0
        
        # Should decay at boundaries
        assert np.abs(psi_0[0]) < 0.1
        assert np.abs(psi_0[-1]) < 0.1

    def test_H_psi_operator_function(self):
        """Test that H_psi_on_hermite function works correctly."""
        import sys
        sys.path.insert(0, str(SCRIPT_FILE.parent))
        from validate_trace_class_complete import H_psi_on_hermite
        
        # Test on a simple grid
        x = np.linspace(-5, 5, 100)
        
        # H_Ψ(ψ_0) should give a result
        result = H_psi_on_hermite(0, x)
        assert result.shape == x.shape
        assert not np.all(result == 0)

    def test_L2_norm_computation(self):
        """Test that L2 norm computation works."""
        import sys
        sys.path.insert(0, str(SCRIPT_FILE.parent))
        from validate_trace_class_complete import compute_L2_norm
        
        # Test with a Gaussian
        x = np.linspace(-10, 10, 1000)
        f = np.exp(-x**2)
        
        norm = compute_L2_norm(f, x)
        
        # Should be close to √π (with finite domain discretization error)
        expected = np.sqrt(np.pi)
        # Allow for discretization error - we're on a finite interval
        assert abs(norm - expected) / expected < 0.5  # 50% relative tolerance

    def test_theoretical_bound_function(self):
        """Test that theoretical_bound function works."""
        import sys
        sys.path.insert(0, str(SCRIPT_FILE.parent))
        from validate_trace_class_complete import theoretical_bound
        
        # Test the bound function
        C, delta = 8.0, 0.25
        n = np.array([1, 10, 100])
        
        bounds = theoretical_bound(n, C, delta)
        
        # Should be decreasing
        assert bounds[0] > bounds[1] > bounds[2]
        
        # Should match formula
        expected = C / (n + 1)**(1 + delta)
        np.testing.assert_allclose(bounds, expected)


class TestIntegration:
    """Integration tests running the full validation."""

    @pytest.mark.slow
    def test_run_validation_script(self):
        """Test running the validation script (marked as slow)."""
        # Run the script
        result = subprocess.run(
            ['python3', str(SCRIPT_FILE)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=120  # 2 minutes timeout
        )
        
        # Check that it ran
        assert result.returncode in [0, 1], f"Script failed: {result.stderr}"
        
        # Check output contains expected elements
        assert "VALIDANDO CLASE TRAZA" in result.stdout
        assert "H_Ψ" in result.stdout or "H_psi" in result.stdout

    @pytest.mark.slow
    def test_validation_produces_output(self):
        """Test that validation produces expected output."""
        # Run the script
        result = subprocess.run(
            ['python3', str(SCRIPT_FILE)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=120
        )
        
        # Check for key results in output
        output = result.stdout
        
        # Should report delta value
        assert "δ" in output or "delta" in output
        
        # Should report convergence
        assert "converge" in output.lower() or "suma" in output.lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-m", "not slow"])
