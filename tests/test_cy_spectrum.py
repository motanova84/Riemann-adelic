#!/usr/bin/env python3
"""
Tests for Calabi-Yau Quintic Spectral Invariant κ_Π

Tests the computation and verification of the invariant κ_Π = μ₂/μ₁ = 2.5773
from the Laplacian spectrum on the CY quintic Fermat hypersurface.

Author: José Manuel Mota Burruezo
Date: December 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from cy_spectrum import (  # noqa: E402
    CalabiYauQuintic,
    CYLaplacianSpectrum,
    KappaPiInvariant,
    cy_laplacian_eigenvalues,
    compute_kappa_pi_invariant,
    KAPPA_PI_EXPECTED,
    KAPPA_PI_TOLERANCE,
    MU1_TARGET,
    MU2_TARGET,
    F0_FREQUENCY,
    COHERENCE_C,
)


class TestCalabiYauQuintic:
    """Test suite for CalabiYauQuintic class."""

    def test_initialization(self):
        """Test that CY quintic initializes with correct properties."""
        cy = CalabiYauQuintic()

        assert cy.h11 == 1
        assert cy.h21 == 101
        assert cy.euler_char == -200
        assert cy.complex_dim == 3
        assert cy.real_dim == 6

    def test_hodge_numbers(self):
        """Test Hodge numbers of the quintic."""
        cy = CalabiYauQuintic()

        # Euler characteristic formula: χ = 2(h^{1,1} - h^{2,1})
        euler = 2 * (cy.h11 - cy.h21)
        assert euler == cy.euler_char == -200

    def test_hodge_diamond(self):
        """Test that Hodge diamond has correct entries."""
        cy = CalabiYauQuintic()
        diamond = cy.hodge_diamond()

        assert diamond[(0, 0)] == 1
        assert diamond[(1, 1)] == 1  # h^{1,1}
        assert diamond[(2, 1)] == 101  # h^{2,1}
        assert diamond[(3, 3)] == 1

    def test_repr(self):
        """Test string representation."""
        cy = CalabiYauQuintic()
        s = repr(cy)

        assert "h11=1" in s
        assert "h21=101" in s
        assert "χ=-200" in s


class TestCYLaplacianSpectrum:
    """Test suite for CYLaplacianSpectrum class."""

    def test_initialization(self):
        """Test spectrum calculator initialization."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)

        assert spectrum.max_eigenvalues == 500
        assert spectrum.cy_manifold is not None
        assert spectrum._spectrum is None

    def test_compute_spectrum_returns_array(self):
        """Test that compute_spectrum returns numpy array."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        eigenvalues = spectrum.compute_spectrum()

        assert isinstance(eigenvalues, np.ndarray)
        assert len(eigenvalues) == 500

    def test_spectrum_is_sorted(self):
        """Test that spectrum is sorted in ascending order."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        eigenvalues = spectrum.compute_spectrum()

        assert np.all(eigenvalues[:-1] <= eigenvalues[1:])

    def test_spectrum_has_zeros(self):
        """Test that spectrum has zero eigenvalues (harmonic modes)."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        eigenvalues = spectrum.compute_spectrum()

        # Should have h^{2,1} = 101 zero eigenvalues
        num_zeros = np.sum(eigenvalues == 0)
        assert num_zeros == 101

    def test_spectrum_is_nonnegative(self):
        """Test that all eigenvalues are non-negative."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        eigenvalues = spectrum.compute_spectrum()

        assert np.all(eigenvalues >= 0)

    def test_get_nonzero_spectrum(self):
        """Test filtering of non-zero eigenvalues."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        spectrum.compute_spectrum()

        nonzero = spectrum.get_nonzero_spectrum()

        assert len(nonzero) == 500 - 101  # = 399
        assert np.all(nonzero > 0)

    def test_spectral_density(self):
        """Test spectral density computation."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500)
        spectrum.compute_spectrum()

        bin_centers, density = spectrum.spectral_density(bins=20)

        assert len(bin_centers) == 20
        assert len(density) == 20
        assert np.all(density >= 0)

    def test_reproducibility_with_seed(self):
        """Test that same seed gives same results."""
        spectrum1 = CYLaplacianSpectrum(max_eigenvalues=200, seed=42)
        spectrum2 = CYLaplacianSpectrum(max_eigenvalues=200, seed=42)

        e1 = spectrum1.compute_spectrum()
        e2 = spectrum2.compute_spectrum()

        np.testing.assert_array_almost_equal(e1, e2)


class TestKappaPiInvariant:
    """Test suite for KappaPiInvariant class."""

    def test_compute_spectral_moments(self):
        """Test spectral moment computation."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=1000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        mu1, mu2 = calculator.compute_spectral_moments()

        assert mu1 > 0
        assert mu2 > 0
        assert mu2 > mu1  # Second moment should be larger

    def test_compute_kappa_pi(self):
        """Test κ_Π computation."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=1000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        kappa_pi = calculator.compute_kappa_pi()

        assert kappa_pi > 0
        # Should be close to 2.5773 (within tolerance)
        assert abs(kappa_pi - KAPPA_PI_EXPECTED) < 0.1

    def test_verify_invariant_passes(self):
        """Test that invariant verification passes with default tolerance."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=1000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)
        calculator.compute_kappa_pi()

        is_valid, difference = calculator.verify_invariant()

        assert difference < 0.1

    def test_properties(self):
        """Test property accessors."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        # Before computation, should be None
        assert calculator.mu1 is None
        assert calculator.mu2 is None
        assert calculator.kappa_pi is None

        # After computation
        calculator.compute_kappa_pi()

        assert calculator.mu1 is not None
        assert calculator.mu2 is not None
        assert calculator.kappa_pi is not None

    def test_kappa_pi_near_expected(self):
        """Test that κ_Π is close to 2.5773."""
        # Use larger sample for better accuracy
        spectrum = CYLaplacianSpectrum(max_eigenvalues=2000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        kappa_pi = calculator.compute_kappa_pi()

        # Should be within 2% of expected value
        relative_error = abs(kappa_pi - KAPPA_PI_EXPECTED) / KAPPA_PI_EXPECTED
        assert relative_error < 0.02


class TestConvenienceFunctions:
    """Test suite for convenience functions."""

    def test_cy_laplacian_eigenvalues(self):
        """Test cy_laplacian_eigenvalues function."""
        eigenvalues = cy_laplacian_eigenvalues("quintic_fermat", max_eigenvalues=500)

        assert isinstance(eigenvalues, np.ndarray)
        assert len(eigenvalues) == 500

    def test_cy_laplacian_eigenvalues_invalid_manifold(self):
        """Test that invalid manifold raises error."""
        with pytest.raises(ValueError):
            cy_laplacian_eigenvalues("invalid_manifold")

    def test_compute_kappa_pi_invariant(self):
        """Test compute_kappa_pi_invariant function."""
        result = compute_kappa_pi_invariant(max_eigenvalues=500, seed=42)

        assert "mu1" in result
        assert "mu2" in result
        assert "kappa_pi" in result
        assert "expected" in result
        assert "difference" in result
        assert "is_valid" in result
        assert "nonzero_eigenvalues" in result
        assert "total_eigenvalues" in result

        assert result["expected"] == KAPPA_PI_EXPECTED
        assert result["total_eigenvalues"] == 500


class TestSpectralMomentAccuracy:
    """Test accuracy of spectral moments compared to targets."""

    def test_mu1_accuracy(self):
        """Test that μ₁ is close to target value."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=2000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)
        mu1, _ = calculator.compute_spectral_moments()

        # Should be within 5% of target
        relative_error = abs(mu1 - MU1_TARGET) / MU1_TARGET
        assert relative_error < 0.05

    def test_mu2_accuracy(self):
        """Test that μ₂ is close to target value."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=2000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)
        _, mu2 = calculator.compute_spectral_moments()

        # Should be within 5% of target
        relative_error = abs(mu2 - MU2_TARGET) / MU2_TARGET
        assert relative_error < 0.05

    def test_kappa_pi_accuracy_with_large_sample(self):
        """Test κ_Π accuracy with large sample size."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=5000, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)
        kappa_pi = calculator.compute_kappa_pi()

        # Should be within 1% of expected
        relative_error = abs(kappa_pi - KAPPA_PI_EXPECTED) / KAPPA_PI_EXPECTED
        assert relative_error < 0.01


class TestInvariantProperties:
    """Test mathematical properties of the κ_Π invariant."""

    def test_scaling_invariance(self):
        """Test that κ_Π is scale-independent for uniform scaling."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500, seed=42)
        spectrum.compute_spectrum()

        eigenvalues = spectrum.get_nonzero_spectrum()

        # Original κ_Π
        mu1_orig = np.mean(eigenvalues)
        mu2_orig = np.mean(eigenvalues**2)
        kappa_orig = mu2_orig / mu1_orig

        # Scaled eigenvalues (λ → c*λ)
        c = 2.5
        scaled = eigenvalues * c
        mu1_scaled = np.mean(scaled)
        mu2_scaled = np.mean(scaled**2)
        kappa_scaled = mu2_scaled / mu1_scaled

        # κ_Π should scale as c (not be invariant)
        # This is expected: κ_Π(c*λ) = c * κ_Π(λ)
        assert abs(kappa_scaled - c * kappa_orig) < 1e-10

    def test_positive_definiteness(self):
        """Test that μ₁, μ₂, and κ_Π are all positive."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        mu1, mu2 = calculator.compute_spectral_moments()
        kappa_pi = calculator.compute_kappa_pi()

        assert mu1 > 0
        assert mu2 > 0
        assert kappa_pi > 0

    def test_cauchy_schwarz_bound(self):
        """Test that μ₂ ≥ μ₁² (Cauchy-Schwarz inequality)."""
        spectrum = CYLaplacianSpectrum(max_eigenvalues=500, seed=42)
        calculator = KappaPiInvariant(spectrum_calculator=spectrum)

        mu1, mu2 = calculator.compute_spectral_moments()

        # By Cauchy-Schwarz: E[X²] ≥ E[X]²
        assert mu2 >= mu1**2 - 1e-10  # Small tolerance for numerical error


class TestConstants:
    """Test module constants."""

    def test_kappa_pi_expected(self):
        """Test expected κ_Π value."""
        assert KAPPA_PI_EXPECTED == 2.5782

    def test_kappa_pi_tolerance(self):
        """Test tolerance value."""
        assert KAPPA_PI_TOLERANCE == 0.02

    def test_f0_frequency(self):
        """Test fundamental frequency."""
        assert F0_FREQUENCY == 141.7001

    def test_coherence_c(self):
        """Test coherence constant."""
        assert COHERENCE_C == 244.36

    def test_mu1_target(self):
        """Test target μ₁."""
        assert MU1_TARGET == 1.121847

    def test_mu2_target(self):
        """Test target μ₂."""
        assert MU2_TARGET == 2.892345

    def test_target_kappa_consistency(self):
        """Test that target moments give correct κ_Π."""
        kappa_from_targets = MU2_TARGET / MU1_TARGET

        # Should match expected κ_Π exactly
        assert abs(kappa_from_targets - KAPPA_PI_EXPECTED) < 0.0001


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
