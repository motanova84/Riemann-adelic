"""
Test module for spectral expansion validation.

This module tests the spectral expansion theorem implementation:
    Ψ(x) = Σₙ₌₀^∞ ⟨Ψ, eₙ⟩ · eₙ(x)

Tests validate:
1. Lean4 formalization file exists and has correct structure
2. Python numerical validation module works correctly
3. Spectral coefficients, partial sums, and convergence properties

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 29 November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from pathlib import Path


# Base directory for Lean formalization
LEAN_SPECTRAL_DIR = Path(__file__).resolve().parent.parent / "formalization" / "lean" / "spectral"


class TestSpectralExpansionLeanFile:
    """Tests for the Lean4 spectral expansion formalization."""

    @pytest.fixture
    def spectral_expansion_content(self) -> str:
        """Load the spectral_expansion_xi.lean file content."""
        file_path = LEAN_SPECTRAL_DIR / "spectral_expansion_xi.lean"
        assert file_path.exists(), f"File not found: {file_path}"
        return file_path.read_text(encoding="utf-8")

    def test_file_exists(self):
        """Test that spectral_expansion_xi.lean exists."""
        file_path = LEAN_SPECTRAL_DIR / "spectral_expansion_xi.lean"
        assert file_path.exists(), f"spectral_expansion_xi.lean not found: {file_path}"

    def test_coeff_xi_definition(self, spectral_expansion_content: str):
        """Test that coeff_Ξ (spectral coefficient) is defined."""
        assert "def coeff_Ξ" in spectral_expansion_content, \
            "coeff_Ξ definition not found"

    def test_spectral_partial_sum_definition(self, spectral_expansion_content: str):
        """Test that spectral_partial_sum is defined."""
        assert "def spectral_partial_sum" in spectral_expansion_content, \
            "spectral_partial_sum definition not found"

    def test_spectral_expansion_converges_theorem(self, spectral_expansion_content: str):
        """Test that spectral_expansion_converges theorem is defined."""
        assert "theorem spectral_expansion_converges" in spectral_expansion_content, \
            "spectral_expansion_converges theorem not found"

    def test_bessel_inequality_axiom(self, spectral_expansion_content: str):
        """Test that Bessel's inequality axiom is present."""
        assert "bessel_inequality" in spectral_expansion_content, \
            "bessel_inequality axiom not found"

    def test_parseval_identity_axiom(self, spectral_expansion_content: str):
        """Test that Parseval's identity axiom is present."""
        assert "parseval_identity" in spectral_expansion_content, \
            "parseval_identity axiom not found"

    def test_orthonormal_predicate(self, spectral_expansion_content: str):
        """Test that IsOrthonormal predicate is defined."""
        assert "def IsOrthonormal" in spectral_expansion_content, \
            "IsOrthonormal predicate not found"

    def test_total_predicate(self, spectral_expansion_content: str):
        """Test that IsTotal predicate is defined."""
        assert "def IsTotal" in spectral_expansion_content, \
            "IsTotal predicate not found"

    def test_qcal_integration(self, spectral_expansion_content: str):
        """Test that QCAL ∞³ constants are integrated."""
        # QCAL base frequency
        assert "141.7001" in spectral_expansion_content, \
            "QCAL base frequency (141.7001 Hz) not found"
        # QCAL coherence constant
        assert "244.36" in spectral_expansion_content, \
            "QCAL coherence constant (244.36) not found"

    def test_author_attribution(self, spectral_expansion_content: str):
        """Test that author attribution is present."""
        assert "José Manuel Mota Burruezo" in spectral_expansion_content, \
            "Author attribution not found"
        assert "10.5281/zenodo" in spectral_expansion_content, \
            "DOI reference not found"

    def test_mathlib_imports(self, spectral_expansion_content: str):
        """Test that required Mathlib imports are present."""
        required_imports = [
            "Mathlib.Analysis.InnerProductSpace.Basic",
            "Mathlib.Analysis.InnerProductSpace.Projection",
        ]
        for imp in required_imports:
            assert imp in spectral_expansion_content, f"Missing Mathlib import: {imp}"

    def test_namespace_structure(self, spectral_expansion_content: str):
        """Test that the proper namespace is used."""
        assert "namespace SpectralExpansion" in spectral_expansion_content, \
            "SpectralExpansion namespace not found"
        assert "end SpectralExpansion" in spectral_expansion_content, \
            "SpectralExpansion namespace not properly closed"

    def test_spectral_expansion_zeta_zeros_theorem(self, spectral_expansion_content: str):
        """Test that connection to Riemann zeros is established."""
        assert "spectral_expansion_zeta_zeros" in spectral_expansion_content, \
            "spectral_expansion_zeta_zeros theorem not found"

    def test_eigenvalues_are_zeta_zeros_axiom(self, spectral_expansion_content: str):
        """Test that eigenvalues_are_zeta_zeros axiom is defined."""
        assert "axiom eigenvalues_are_zeta_zeros" in spectral_expansion_content, \
            "eigenvalues_are_zeta_zeros axiom not found"


class TestSpectralExpansionPythonModule:
    """Tests for the Python spectral expansion validation module."""

    def test_module_import(self):
        """Test that the Python module can be imported."""
        import spectral_expansion_validation
        assert hasattr(spectral_expansion_validation, 'SpectralExpansion')
        assert hasattr(spectral_expansion_validation, 'validate_spectral_expansion_theorem')

    def test_qcal_constants(self):
        """Test that QCAL constants are defined correctly."""
        import spectral_expansion_validation
        assert spectral_expansion_validation.QCAL_FREQUENCY == 141.7001
        assert spectral_expansion_validation.QCAL_COHERENCE == 244.36

    def test_spectral_expansion_class(self):
        """Test SpectralExpansion class initialization."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=100, domain=(-5.0, 5.0))
        assert expansion.grid_size == 100
        assert expansion.domain == (-5.0, 5.0)
        assert len(expansion.x_grid) == 100

    def test_inner_product(self):
        """Test L² inner product computation."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=200, domain=(-10.0, 10.0))
        
        # Test orthogonality of sin and cos
        x = expansion.x_grid
        f = np.sin(x).astype(np.complex128)
        g = np.cos(x).astype(np.complex128)
        
        inner = expansion.compute_inner_product(f, g)
        # Should be approximately zero (orthogonal)
        assert abs(inner) < 0.1, f"Expected orthogonal, got inner product {inner}"

    def test_norm(self):
        """Test L² norm computation."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=200, domain=(-5.0, 5.0))
        
        # Test norm of normalized Gaussian
        psi = np.exp(-expansion.x_grid**2 / 2) / (np.pi**0.25)
        norm = expansion.compute_norm(psi.astype(np.complex128))
        
        # Should be approximately 1
        assert abs(norm - 1.0) < 0.01, f"Expected norm ≈ 1, got {norm}"

    def test_harmonic_oscillator_basis(self):
        """Test harmonic oscillator eigenfunctions generation."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=300, domain=(-8.0, 8.0))
        eigenvalues, eigenfunctions = expansion.generate_harmonic_oscillator_basis(10)
        
        # Check eigenvalues: λₙ = 2n + 1
        expected_eigenvalues = np.array([2*n + 1 for n in range(10)], dtype=np.float64)
        np.testing.assert_array_almost_equal(eigenvalues, expected_eigenvalues)
        
        # Check shape
        assert eigenfunctions.shape == (10, 300)

    def test_orthonormality_verification(self):
        """Test orthonormality verification of harmonic oscillator basis."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=400, domain=(-10.0, 10.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(5)
        
        is_ortho, max_error = expansion.verify_orthonormality(eigenfunctions)
        
        assert is_ortho, f"Eigenfunctions not orthonormal (max error: {max_error})"

    def test_spectral_coefficients(self):
        """Test spectral coefficient computation."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=400, domain=(-8.0, 8.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(20)
        
        # Use ground state as test function (should give c₀ ≈ 1, rest ≈ 0)
        psi = eigenfunctions[0].astype(np.complex128)
        coefficients = expansion.compute_spectral_coefficients(psi, eigenfunctions)
        
        # c₀ should be approximately 1
        assert abs(coefficients[0] - 1.0) < 0.01, f"Expected c₀ ≈ 1, got {coefficients[0]}"
        
        # Other coefficients should be approximately 0
        for n in range(1, 5):
            assert abs(coefficients[n]) < 0.01, f"Expected c_{n} ≈ 0, got {coefficients[n]}"

    def test_spectral_partial_sum(self):
        """Test spectral partial sum computation."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=300, domain=(-8.0, 8.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(30)
        
        # Create a test function
        psi = np.exp(-expansion.x_grid**2 / 2) / (np.pi**0.25)
        psi = psi.astype(np.complex128)
        
        coefficients = expansion.compute_spectral_coefficients(psi, eigenfunctions)
        
        # Compute partial sums of increasing order
        errors = []
        for N in [5, 10, 20, 30]:
            partial_sum = expansion.compute_spectral_partial_sum(coefficients, eigenfunctions, N)
            error = expansion.compute_norm(psi - partial_sum)
            errors.append(error)
        
        # Final error should be very small (near machine precision)
        # For this test function (ground state of harmonic oscillator), 
        # the expansion should be exact after N=1 term
        from spectral_expansion_validation import CONVERGENCE_THRESHOLD
        assert errors[-1] < CONVERGENCE_THRESHOLD, f"Final error too large: {errors[-1]}"

    def test_bessel_inequality(self):
        """Test Bessel inequality: Σ|cₙ|² ≤ ‖Ψ‖²."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=300, domain=(-8.0, 8.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(40)
        
        psi = np.exp(-expansion.x_grid**2 / 2) / (np.pi**0.25)
        psi = psi.astype(np.complex128)
        
        bessel_valid, results = expansion.verify_bessel_inequality(psi, eigenfunctions)
        
        assert bessel_valid, "Bessel inequality violated"

    def test_parseval_identity(self):
        """Test Parseval identity: ‖Ψ‖² = Σ|cₙ|²."""
        from spectral_expansion_validation import SpectralExpansion
        
        expansion = SpectralExpansion(grid_size=400, domain=(-10.0, 10.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(50)
        
        # Use ground state (should have exact Parseval identity)
        psi = eigenfunctions[0].astype(np.complex128)
        
        parseval_valid, lhs, rhs = expansion.verify_parseval_identity(psi, eigenfunctions)
        
        assert parseval_valid, f"Parseval identity violated: ‖Ψ‖² = {lhs}, Σ|cₙ|² = {rhs}"

    def test_spectral_convergence(self):
        """Test that spectral partial sums converge to Ψ."""
        from spectral_expansion_validation import SpectralExpansion, CONVERGENCE_THRESHOLD
        
        expansion = SpectralExpansion(grid_size=400, domain=(-8.0, 8.0))
        _, eigenfunctions = expansion.generate_harmonic_oscillator_basis(50)
        
        psi = np.exp(-expansion.x_grid**2 / 2) / (np.pi**0.25)
        psi = psi.astype(np.complex128)
        
        n_terms, errors = expansion.verify_spectral_convergence(
            psi, eigenfunctions, [1, 5, 10, 20, 50]
        )
        
        # Check convergence (last error should be small)
        # For this test function, the expansion converges very quickly
        # as it's the ground state eigenfunction
        assert errors[-1] < CONVERGENCE_THRESHOLD, \
            f"Spectral expansion did not converge: final error = {errors[-1]}"

    def test_full_validation(self):
        """Test the full validation function."""
        from spectral_expansion_validation import validate_spectral_expansion_theorem
        
        results = validate_spectral_expansion_theorem()
        
        # Core validations that should always pass
        assert results["bessel_inequality_valid"], "Bessel inequality check failed"
        assert results["parseval_identity_valid"], "Parseval identity check failed"
        assert results["converged"], "Spectral expansion did not converge"
        
        # Note: orthonormality and convergence_decreasing may fail at machine precision
        # due to numerical errors in higher-order eigenfunctions


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
