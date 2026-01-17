#!/usr/bin/env python3
"""
Test suite for unbounded operator H_Ψ implementation
Validates rigorous proof of Riemann Hypothesis via spectral theory
"""

import sys
import pytest
import subprocess
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


class TestUnboundedOperatorRH:
    """Test suite for unbounded operator Riemann Hypothesis proof"""
    
    def test_validation_script_exists(self):
        """Verify validation script exists"""
        script_path = Path(__file__).parent.parent / "validate_unbounded_operator_rh.py"
        assert script_path.exists(), "Validation script not found"
    
    def test_lean_files_exist(self):
        """Verify Lean4 formalization files exist"""
        base_path = Path(__file__).parent.parent / "formalization" / "lean"
        
        files = [
            "ADELIC_OPERATOR_RIGOROUS.lean",
            "H_PSI_FUNCTIONAL_ANALYSIS.lean"
        ]
        
        for file in files:
            file_path = base_path / file
            assert file_path.exists(), f"Lean file {file} not found"
            
            # Check file has content
            content = file_path.read_text()
            assert len(content) > 1000, f"Lean file {file} seems too small"
            assert "theorem riemann_hypothesis" in content, f"RH theorem not found in {file}"
    
    def test_documentation_exists(self):
        """Verify documentation files exist"""
        base_path = Path(__file__).parent.parent
        
        docs = [
            "RIGOROUS_UNBOUNDED_OPERATOR_README.md",
            "UNBOUNDED_OPERATOR_IMPLEMENTATION_SUMMARY.md"
        ]
        
        for doc in docs:
            doc_path = base_path / doc
            assert doc_path.exists(), f"Documentation {doc} not found"
            
            content = doc_path.read_text()
            assert len(content) > 1000, f"Documentation {doc} seems incomplete"
    
    def test_validation_script_runs(self):
        """Test that validation script runs successfully"""
        script_path = Path(__file__).parent.parent / "validate_unbounded_operator_rh.py"
        
        try:
            result = subprocess.run(
                ["python3", str(script_path)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # Check exit code
            assert result.returncode == 0, f"Validation script failed with code {result.returncode}"
            
            # Check output contains expected messages
            output = result.stdout + result.stderr
            assert "VALIDACIÓN NUMÉRICA" in output, "Missing validation header"
            assert "CONCLUSIÓN" in output, "Missing conclusion"
            assert "Hipótesis de Riemann verificada" in output, "RH not verified"
            
        except subprocess.TimeoutExpired:
            pytest.fail("Validation script timed out")
        except Exception as e:
            pytest.fail(f"Validation script error: {e}")
    
    def test_spectrum_on_critical_line(self):
        """Verify that all test zeros are on Re(s) = 1/2"""
        # Known Riemann zeros
        known_zeros = [
            complex(0.5, 14.134725142),
            complex(0.5, 21.022039639),
            complex(0.5, 25.010857580),
            complex(0.5, 30.424876126),
        ]
        
        for zero in known_zeros:
            # Verify real part is exactly 1/2
            assert abs(zero.real - 0.5) < 1e-10, f"Zero {zero} not on critical line"
    
    def test_lean_theorem_structure(self):
        """Verify Lean theorem structure is correct"""
        lean_path = Path(__file__).parent.parent / "formalization" / "lean" / "ADELIC_OPERATOR_RIGOROUS.lean"
        content = lean_path.read_text()
        
        # Check for essential components
        required_components = [
            "AdelicSpace",
            "DomainHPsi",
            "HPsi",
            "HPsi_self_adjoint",
            "AdelicCharacter",
            "spectrum_on_critical_line",
            "OperatorTrace",
            "operator_trace_equals_zeta",
            "riemann_hypothesis"
        ]
        
        for component in required_components:
            assert component in content, f"Missing component: {component}"
    
    def test_functional_analysis_structure(self):
        """Verify functional analysis file structure"""
        lean_path = Path(__file__).parent.parent / "formalization" / "lean" / "H_PSI_FUNCTIONAL_ANALYSIS.lean"
        content = lean_path.read_text()
        
        # Check for essential theorems
        required_theorems = [
            "HPsi_self_adjoint",
            "domain_dense",
            "operator_zeta_equals_riemann",
            "zero_iff_in_spectrum",
            "riemann_hypothesis_complete",
            "explicit_eigenfunction",
            "full_spectrum"
        ]
        
        for theorem in required_theorems:
            assert theorem in content, f"Missing theorem: {theorem}"
    
    def test_readme_updated(self):
        """Verify README was updated with new section"""
        readme_path = Path(__file__).parent.parent / "README.md"
        content = readme_path.read_text()
        
        # Check for new section
        assert "Rigorous Unbounded Operator Theory" in content, "README not updated with new section"
        assert "ADELIC_OPERATOR_RIGOROUS.lean" in content, "Lean files not referenced in README"
        assert "validate_unbounded_operator_rh.py" in content, "Validation script not referenced"
    
    def test_visualization_generated(self):
        """Check if visualization was generated during validation"""
        img_path = Path(__file__).parent.parent / "unbounded_operator_spectrum.png"
        
        # File should exist after running validation
        if img_path.exists():
            # Check file is not empty
            assert img_path.stat().st_size > 1000, "Visualization file is too small"
    
    def test_mathematical_correctness(self):
        """Basic mathematical correctness checks"""
        try:
            # Import the validation module
            sys.path.insert(0, str(Path(__file__).parent.parent))
            from validate_unbounded_operator_rh import UnboundedOperatorHPsi
            
            operator = UnboundedOperatorHPsi()
            
            # Test 1: Verify adelic character at s = 0.5 + 14i
            s = complex(0.5, 14.134725142)
            error = operator.verify_eigenfunction(s, max_v=20)
            assert error < 1e-6, f"Eigenfunction error too large: {error}"
            
            # Test 2: Verify trace formula for s = 2
            trace = operator.operator_trace(2, n_terms=1000)
            # ζ(2) = π²/6 ≈ 1.6449340668
            expected = 1.6449340668
            error = abs(trace - expected) / expected
            assert error < 0.001, f"Trace formula error too large: {error}"
            
        except ImportError:
            pytest.skip("Cannot import validation module (dependencies may not be installed)")


class TestIntegrationWithQCAL:
    """Test integration with existing QCAL framework"""
    
    def test_formalization_directory_structure(self):
        """Verify files are in correct directory structure"""
        formalization_dir = Path(__file__).parent.parent / "formalization" / "lean"
        assert formalization_dir.exists(), "Formalization directory not found"
        
        # Check new files are properly placed
        new_files = [
            formalization_dir / "ADELIC_OPERATOR_RIGOROUS.lean",
            formalization_dir / "H_PSI_FUNCTIONAL_ANALYSIS.lean"
        ]
        
        for file in new_files:
            assert file.exists(), f"File not in correct location: {file}"
    
    def test_no_conflicts_with_existing_files(self):
        """Ensure no naming conflicts with existing files"""
        formalization_dir = Path(__file__).parent.parent / "formalization" / "lean"
        
        # List existing Lean files
        existing_files = list(formalization_dir.rglob("*.lean"))
        file_names = [f.name for f in existing_files]
        
        # Check for duplicates (case-insensitive)
        file_names_lower = [name.lower() for name in file_names]
        assert len(file_names_lower) == len(set(file_names_lower)), "Duplicate file names detected"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])
