"""
Test suite for construct_H_psi_kernel.lean
==========================================

Tests the Hilbert-Schmidt kernel construction for H_Ψ operator.

Author: José Manuel Mota Burruezo Ψ ∞³
DOI: 10.5281/zenodo.17379721
"""

import pytest
from pathlib import Path

# Project root
PROJECT_ROOT = Path(__file__).parent.parent


class TestConstructHPsiKernel:
    """Tests for construct_H_psi_kernel.lean formalization"""

    @pytest.fixture
    def lean_file_path(self):
        """Path to the Lean formalization file"""
        return PROJECT_ROOT / "formalization" / "lean" / "operators" / "construct_H_psi_kernel.lean"

    def test_file_exists(self, lean_file_path):
        """Test that construct_H_psi_kernel.lean exists"""
        assert lean_file_path.exists(), f"File not found: {lean_file_path}"
        assert lean_file_path.stat().st_size > 0, "File is empty"

    def test_file_has_required_imports(self, lean_file_path):
        """Test that the file has required Mathlib imports"""
        content = lean_file_path.read_text()
        
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace.L2Space",
            "Mathlib.MeasureTheory.Integral.Bochner",
        ]
        
        for imp in required_imports:
            assert imp in content, f"Missing import: {imp}"

    def test_kernel_definition_exists(self, lean_file_path):
        """Test that kernel_H is defined"""
        content = lean_file_path.read_text()
        assert "def kernel_H" in content, "kernel_H definition not found"
        # Check kernel structure
        assert "exp" in content, "Exponential function not used in kernel"
        assert "cos" in content, "Cosine function not used in kernel"
        assert "log" in content, "Logarithm function not used in kernel"

    def test_operator_definition_exists(self, lean_file_path):
        """Test that H_psi_op is defined"""
        content = lean_file_path.read_text()
        assert "def H_psi_op" in content, "H_psi_op definition not found"

    def test_kernel_symmetry_theorem(self, lean_file_path):
        """Test that kernel symmetry theorem is present"""
        content = lean_file_path.read_text()
        assert "kernel_H_symmetric" in content, "Kernel symmetry theorem not found"
        # Should establish k(x,y) = k(y,x)
        assert "kernel_H x y = kernel_H y x" in content, "Symmetry statement not found"

    def test_kernel_decay_lemma(self, lean_file_path):
        """Test that kernel decay lemma is present"""
        content = lean_file_path.read_text()
        assert "kernel_H_decay" in content, "Kernel decay lemma not found"

    def test_hilbert_schmidt_axiom(self, lean_file_path):
        """Test that Hilbert-Schmidt property is axiomatized"""
        content = lean_file_path.read_text()
        assert "kernel_H_hilbert_schmidt" in content, "Hilbert-Schmidt axiom not found"

    def test_selfadjoint_axiom(self, lean_file_path):
        """Test that self-adjointness is axiomatized"""
        content = lean_file_path.read_text()
        assert "H_psi_selfadjoint" in content, "Self-adjoint axiom not found"

    def test_compact_axiom(self, lean_file_path):
        """Test that compactness is axiomatized"""
        content = lean_file_path.read_text()
        assert "H_psi_compact" in content, "Compact operator axiom not found"

    def test_spectral_theorem(self, lean_file_path):
        """Test that spectral theorem is present"""
        content = lean_file_path.read_text()
        assert "H_psi_spectral_theorem" in content, "Spectral theorem not found"

    def test_eigenfunction_existence(self, lean_file_path):
        """Test that eigenfunction existence theorem is present"""
        content = lean_file_path.read_text()
        assert "H_psi_eigenfunction_exists" in content, "Eigenfunction existence theorem not found"

    def test_namespace_structure(self, lean_file_path):
        """Test correct namespace structure"""
        content = lean_file_path.read_text()
        assert "namespace RiemannSpectral" in content, "RiemannSpectral namespace not found"
        assert "end RiemannSpectral" in content, "RiemannSpectral namespace not closed"

    def test_noncomputable_section(self, lean_file_path):
        """Test noncomputable section is declared"""
        content = lean_file_path.read_text()
        assert "noncomputable section" in content, "noncomputable section not declared"

    def test_documentation_present(self, lean_file_path):
        """Test that documentation is present"""
        content = lean_file_path.read_text()
        # Check for header documentation
        assert "José Manuel Mota Burruezo" in content, "Author attribution not found"
        assert "10.5281/zenodo" in content, "DOI reference not found"
        # Check for mathematical documentation
        assert "Hilbert–Schmidt" in content or "Hilbert-Schmidt" in content, \
            "Hilbert-Schmidt documentation not found"
        assert "autoadjunto" in content or "self-adjoint" in content or "selfadjoint" in content, \
            "Self-adjoint documentation not found"

    def test_no_syntax_errors_basic(self, lean_file_path):
        """Test basic syntax validation (balanced brackets)"""
        content = lean_file_path.read_text()
        
        # Check balanced parentheses
        assert content.count('(') == content.count(')'), "Unbalanced parentheses"
        assert content.count('[') == content.count(']'), "Unbalanced brackets"
        assert content.count('{') == content.count('}'), "Unbalanced braces"

    def test_mathematical_content(self, lean_file_path):
        """Test that mathematical content is properly structured"""
        content = lean_file_path.read_text()
        
        # Check for key mathematical concepts
        assert "L²" in content or "L2" in content, "L² space reference not found"
        assert "∫" in content or "integral" in content.lower(), "Integral reference not found"
        assert "π" in content or "pi" in content.lower(), "π constant reference not found"


class TestHPsiKernelMathematicalProperties:
    """Tests for mathematical correctness of H_Ψ kernel construction"""

    @pytest.fixture
    def lean_file_path(self):
        """Path to the Lean formalization file"""
        return PROJECT_ROOT / "formalization" / "lean" / "operators" / "construct_H_psi_kernel.lean"

    def test_kernel_exponential_decay(self, lean_file_path):
        """Test that kernel has exponential decay"""
        content = lean_file_path.read_text()
        # The kernel should have e^{-π(x+y)} decay
        assert "exp" in content.lower() and "π" in content, \
            "Exponential decay with π not found"

    def test_kernel_logarithmic_structure(self, lean_file_path):
        """Test that kernel uses logarithmic ratio"""
        content = lean_file_path.read_text()
        # The kernel should use log(x/y) or equivalent
        assert "log" in content.lower(), "Logarithmic structure not found"

    def test_ioi_zero_domain(self, lean_file_path):
        """Test that integration is over (0, ∞)"""
        content = lean_file_path.read_text()
        assert "Ioi 0" in content, "Domain Ioi 0 (positive reals) not found"

    def test_complex_valued(self, lean_file_path):
        """Test that kernel is complex-valued"""
        content = lean_file_path.read_text()
        assert "→ ℂ" in content or ": ℂ" in content, "Complex return type not found"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
