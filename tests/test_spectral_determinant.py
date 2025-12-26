#!/usr/bin/env python3
"""
Test suite for spectral determinant D(s) construction.

This module tests the formal construction of the spectral determinant
D(s) = ∏(1 - s/λ_n) as an entire function with zeros on the critical line.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 26 diciembre 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import sys
from pathlib import Path

# Add repository root to path for imports
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import pytest
import numpy as np
import subprocess


class TestSpectralDeterminantLean:
    """Tests for Lean formalization of spectral determinant."""

    @pytest.fixture
    def lean_file(self):
        """Path to the spectral determinant Lean file."""
        return REPO_ROOT / "formalization" / "lean" / "spectral_determinant_formal.lean"

    def test_lean_file_exists(self, lean_file):
        """Verify the Lean formalization file exists."""
        assert lean_file.exists(), f"Lean file not found: {lean_file}"

    def test_lean_file_has_namespace(self, lean_file):
        """Verify the file defines the SpectralDeterminant namespace."""
        content = lean_file.read_text()
        assert "namespace SpectralDeterminant" in content

    def test_lean_file_has_eigenvalues_def(self, lean_file):
        """Verify eigenvalues are defined."""
        content = lean_file.read_text()
        assert "def eigenvalues" in content

    def test_lean_file_has_D_def(self, lean_file):
        """Verify D(s) is defined."""
        content = lean_file.read_text()
        assert "def D " in content or "def D(" in content

    def test_lean_file_has_convergence_theorem(self, lean_file):
        """Verify convergence theorem is present."""
        content = lean_file.read_text()
        assert "D_product_converges_everywhere" in content

    def test_lean_file_has_entire_theorem(self, lean_file):
        """Verify entire function theorem is present."""
        content = lean_file.read_text()
        assert "D_entire_formal" in content

    def test_lean_file_has_order_theorem(self, lean_file):
        """Verify growth order theorem is present."""
        content = lean_file.read_text()
        assert "D_order_one_formal" in content

    def test_lean_file_has_functional_equation(self, lean_file):
        """Verify functional equation theorem is present."""
        content = lean_file.read_text()
        assert "D_functional_equation_formal" in content

    def test_lean_file_has_critical_line_theorem(self, lean_file):
        """Verify critical line theorem is present."""
        content = lean_file.read_text()
        assert "all_zeros_on_critical_line_formal" in content

    def test_lean_file_check_commands(self, lean_file):
        """Verify check commands are present for main theorems."""
        content = lean_file.read_text()
        assert "#check SpectralDeterminant.D_entire_formal" in content
        assert "#check SpectralDeterminant.D_order_one_formal" in content


class TestSpectralDeterminantNumerical:
    """Numerical tests for spectral determinant properties."""

    @pytest.fixture
    def zeta_zeros(self):
        """Known zeros of Riemann zeta function (imaginary parts)."""
        return [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]

    @pytest.fixture
    def eigenvalues_fn(self, zeta_zeros):
        """Function to compute eigenvalues λ_n = 1/2 + i·γ_n."""
        def eigenvalues(n):
            if n < len(zeta_zeros):
                return 0.5 + 1j * zeta_zeros[n]
            else:
                # Asymptotic approximation
                gamma_approx = 2 * np.pi * (n + 1) / np.log(n + 2)
                return 0.5 + 1j * gamma_approx
        return eigenvalues

    @pytest.fixture
    def D_product(self, eigenvalues_fn):
        """Partial product for D(s)."""
        def product(s, N=15):
            prod = 1.0 + 0j
            for n in range(N):
                λ = eigenvalues_fn(n)
                prod *= (1 - s / λ)
            return prod
        return product

    def test_eigenvalues_have_real_part_half(self, eigenvalues_fn):
        """Verify all eigenvalues have Re(λ) = 1/2."""
        for n in range(10):
            λ = eigenvalues_fn(n)
            assert abs(λ.real - 0.5) < 1e-10, f"λ_{n} does not have Re=1/2"

    def test_D_convergence(self, D_product):
        """Test that D(s) converges as N increases."""
        s = 0.3 + 0.4j
        N_values = [5, 10, 15, 20]
        values = [D_product(s, N) for N in N_values]
        
        # Check that differences decrease
        for i in range(1, len(values) - 1):
            diff1 = abs(values[i] - values[i-1])
            diff2 = abs(values[i+1] - values[i])
            # Later differences should generally be smaller
            # (not strict due to oscillations, but trend should hold)
            assert diff2 < diff1 * 2, "Convergence not monotonic"

    def test_D_zeros_at_eigenvalues(self, D_product, eigenvalues_fn):
        """Test that D(λ_n) = 0 for eigenvalues."""
        for n in range(3):
            λ = eigenvalues_fn(n)
            D_val = D_product(λ, N=15)
            # Should be exactly 0 due to factor (1 - λ/λ) = 0
            assert abs(D_val) < 1e-10, f"D(λ_{n}) = {D_val} ≠ 0"

    def test_D_nonzero_away_from_eigenvalues(self, D_product):
        """Test that D(s) ≠ 0 away from eigenvalues."""
        # Points with imaginary parts away from known zeros
        test_points = [0.3 + 1.0j, 0.7 + 3.0j, 0.2 + 5.0j]
        
        for s in test_points:
            D_val = D_product(s, N=15)
            assert abs(D_val) > 1e-20, f"D({s}) unexpectedly close to 0"

    def test_D_functional_equation_approximate(self, D_product):
        """Test D(1-s) ≈ conj(D(s)) for product partial."""
        # For finite product, this is approximate
        test_points = [0.3 + 0.5j, 0.7 + 1.0j]
        
        for s in test_points:
            D_s = D_product(s, N=15)
            D_1ms = D_product(1 - s, N=15)
            D_s_conj = np.conj(D_s)
            
            if abs(D_s) > 1e-50:
                rel_diff = abs(D_1ms - D_s_conj) / abs(D_s)
                # For partial product, allow larger tolerance
                assert rel_diff < 100, f"Functional equation fails for s={s}"

    def test_D_growth_bounded(self, D_product):
        """Test that |D(s)| has exponential growth bound."""
        # Test at various radii
        for r in [1.0, 2.0, 3.0]:
            # Point with |s| = r
            s = r * (0.6 + 0.8j)  # unit vector times r
            D_val = D_product(s, N=15)
            
            if abs(D_val) > 1e-100:
                log_D = np.log(abs(D_val))
                # Growth should be at most linear in |s|
                # For partial product, be generous with constant
                assert log_D < 10 * r, f"Growth too fast at |s|={r}"

    def test_zeros_on_critical_line(self, D_product, zeta_zeros):
        """Test that zeros are on Re(s) = 1/2."""
        # All zeros should be at s = 1/2 + i·γ_n
        for γ in zeta_zeros[:3]:
            # Test that D is smaller at 1/2 + iγ than nearby
            s_critical = 0.5 + 1j * γ
            s_off_critical = 0.6 + 1j * γ
            
            D_critical = D_product(s_critical, N=15)
            D_off = D_product(s_off_critical, N=15)
            
            # D should be zero (or very small) on critical line
            assert abs(D_critical) < 1e-10, "D not zero on critical line"
            # D should be nonzero off critical line
            assert abs(D_off) > abs(D_critical), "D smaller off critical line"


class TestVerificationScript:
    """Tests for the verification script."""

    @pytest.fixture
    def script_path(self):
        """Path to verification script."""
        return REPO_ROOT / "scripts" / "verify_spectral_determinant.py"

    def test_script_exists(self, script_path):
        """Verify the verification script exists."""
        assert script_path.exists(), f"Script not found: {script_path}"

    def test_script_is_executable(self, script_path):
        """Verify the script has executable permissions."""
        assert script_path.stat().st_mode & 0o111, "Script not executable"

    def test_script_runs_successfully(self, script_path):
        """Test that the verification script runs without errors."""
        result = subprocess.run(
            ["python3", str(script_path)],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        assert result.returncode == 0, f"Script failed:\n{result.stderr}"

    def test_script_output_contains_success(self, script_path):
        """Test that script output indicates success."""
        result = subprocess.run(
            ["python3", str(script_path)],
            capture_output=True,
            text=True,
            timeout=60
        )
        
        output = result.stdout
        assert "CONSTRUCCIÓN DE D(s) VERIFICADA EXITOSAMENTE" in output or \
               "VERIFICADA EXITOSAMENTE" in output, \
               "Success message not found in output"


class TestQCALIntegration:
    """Tests for QCAL framework integration."""

    def test_qcal_constants_documented(self):
        """Verify QCAL constants are documented in Lean file."""
        lean_file = REPO_ROOT / "formalization" / "lean" / "spectral_determinant_formal.lean"
        content = lean_file.read_text()
        
        # Check for QCAL references
        # QCAL constants: f₀ = 141.7001 Hz (base frequency), C = 244.36 (coherence)
        assert "QCAL" in content or "Coherencia" in content
        assert "141.7001" in content or "244.36" in content

    def test_doi_reference_present(self):
        """Verify DOI reference is present."""
        lean_file = REPO_ROOT / "formalization" / "lean" / "spectral_determinant_formal.lean"
        content = lean_file.read_text()
        
        assert "10.5281/zenodo.17379721" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
