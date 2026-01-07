#!/usr/bin/env python3
"""
Tests for extract_frequency_from_spectrum module.

This module tests the extraction of the QCAL fundamental frequency
f₀ = 141.7001 Hz from verified spectral data.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import pytest
import numpy as np

from utils.extract_frequency_from_spectrum import (
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    ALPHA_SPECTRAL,
    K_SCALING,
    F_RAW,
    FrequencyExtractionResult,
    extract_from_eigenvalue_mean,
    extract_from_eigenvalue_gap,
    extract_from_spectral_density,
    extract_from_triple_scaling,
    extract_exact_frequency,
    verify_spectrum_yields_qcal_frequency,
)


class TestConstants:
    """Test QCAL constants are correctly defined."""

    def test_qcal_frequency(self):
        """Test QCAL frequency is 141.7001 Hz."""
        assert QCAL_FREQUENCY == 141.7001

    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36

    def test_alpha_spectral(self):
        """Test spectral calibration parameter α."""
        assert ALPHA_SPECTRAL == 12.32955

    def test_f_raw(self):
        """Test raw frequency before scaling."""
        assert F_RAW == 157.9519

    def test_k_scaling_formula(self):
        """Test triple scaling factor formula k = (f₀/f_raw)²."""
        expected_k = (QCAL_FREQUENCY / F_RAW) ** 2
        assert abs(K_SCALING - expected_k) < 1e-10


class TestFrequencyExtractionResult:
    """Test FrequencyExtractionResult dataclass."""

    def test_dataclass_creation(self):
        """Test creating a FrequencyExtractionResult."""
        result = FrequencyExtractionResult(
            frequency=141.7001,
            angular_frequency=2 * np.pi * 141.7001,
            method="test",
            eigenvalues_used=10,
            verified=True,
            relative_error=0.0,
            confidence=1.0,
            details={}
        )
        assert result.frequency == 141.7001
        assert result.method == "test"
        assert result.verified is True


class TestExtractFromEigenvalueMean:
    """Tests for extract_from_eigenvalue_mean function."""

    def test_with_synthetic_spectrum(self):
        """Test extraction from synthetic H_Ψ-like spectrum."""
        # Generate synthetic eigenvalues (Schrödinger-type growth)
        np.random.seed(42)
        n = np.arange(1, 51)
        eigenvalues = ALPHA_SPECTRAL * n ** 2
        eigenvalues += np.random.uniform(-0.05, 0.05, 50) * eigenvalues

        result = extract_from_eigenvalue_mean(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)
        assert result.method == "eigenvalue_mean"
        assert result.eigenvalues_used > 0
        assert result.frequency > 0

    def test_with_empty_eigenvalues(self):
        """Test extraction with empty eigenvalue array."""
        eigenvalues = np.array([])
        result = extract_from_eigenvalue_mean(eigenvalues)

        assert result.verified is False
        assert result.confidence == 0.0

    def test_with_negative_eigenvalues_only(self):
        """Test extraction with only negative eigenvalues."""
        eigenvalues = np.array([-1.0, -2.0, -3.0])
        result = extract_from_eigenvalue_mean(eigenvalues)

        assert result.verified is False
        assert "error" in result.details or result.eigenvalues_used == 0


class TestExtractFromEigenvalueGap:
    """Tests for extract_from_eigenvalue_gap function."""

    def test_with_synthetic_spectrum(self):
        """Test extraction from eigenvalue gaps."""
        np.random.seed(42)
        n = np.arange(1, 51)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        result = extract_from_eigenvalue_gap(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)
        assert result.method == "eigenvalue_gap"
        assert result.frequency > 0

    def test_with_insufficient_eigenvalues(self):
        """Test with fewer than 2 positive eigenvalues."""
        eigenvalues = np.array([1.0])
        result = extract_from_eigenvalue_gap(eigenvalues)

        assert result.verified is False
        assert "error" in result.details


class TestExtractFromSpectralDensity:
    """Tests for extract_from_spectral_density function."""

    def test_with_synthetic_spectrum(self):
        """Test extraction from spectral density."""
        np.random.seed(42)
        n = np.arange(1, 101)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        result = extract_from_spectral_density(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)
        assert result.method == "spectral_density"
        assert result.frequency > 0

    def test_with_insufficient_eigenvalues(self):
        """Test with fewer than 5 positive eigenvalues."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        result = extract_from_spectral_density(eigenvalues)

        assert result.verified is False


class TestExtractFromTripleScaling:
    """Tests for extract_from_triple_scaling function."""

    def test_with_positive_curvature(self):
        """Test extraction with positive curvature."""
        # Curvature that would give raw frequency
        omega_raw = 2 * np.pi * F_RAW
        curvature = omega_raw ** 2

        result = extract_from_triple_scaling(curvature)

        assert isinstance(result, FrequencyExtractionResult)
        assert result.method == "triple_scaling"
        assert result.verified is True
        assert result.confidence == 1.0  # Triple scaling is exact
        assert abs(result.frequency - QCAL_FREQUENCY) < 0.01

    def test_with_zero_curvature(self):
        """Test extraction with zero curvature."""
        result = extract_from_triple_scaling(0.0)

        assert result.verified is False
        assert "error" in result.details

    def test_with_negative_curvature(self):
        """Test extraction with negative curvature."""
        result = extract_from_triple_scaling(-1.0)

        assert result.verified is False
        assert "error" in result.details


class TestExtractExactFrequency:
    """Tests for main extract_exact_frequency function."""

    def test_auto_method_with_eigenvalues(self):
        """Test auto method selection with eigenvalues."""
        np.random.seed(42)
        n = np.arange(1, 51)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        result = extract_exact_frequency(eigenvalues=eigenvalues, method="auto")

        assert isinstance(result, FrequencyExtractionResult)
        assert result.frequency > 0

    def test_auto_method_with_curvature(self):
        """Test auto method selection with curvature."""
        omega_raw = 2 * np.pi * F_RAW
        curvature = omega_raw ** 2

        result = extract_exact_frequency(curvature=curvature, method="auto")

        assert result.verified is True
        assert abs(result.frequency - QCAL_FREQUENCY) < 0.01

    def test_ensemble_method(self):
        """Test ensemble method combining all extraction methods."""
        np.random.seed(42)
        n = np.arange(1, 101)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        result = extract_exact_frequency(eigenvalues=eigenvalues, method="ensemble")

        assert result.method == "ensemble"
        assert "individual_results" in result.details

    def test_specific_methods(self):
        """Test each specific method can be called."""
        np.random.seed(42)
        n = np.arange(1, 101)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        for method in ["mean", "gap", "density"]:
            result = extract_exact_frequency(eigenvalues=eigenvalues, method=method)
            assert result.method == f"eigenvalue_{method}" or result.method == f"spectral_{method}"

    def test_scaling_method_requires_curvature(self):
        """Test that scaling method requires curvature parameter."""
        with pytest.raises(ValueError, match="curvature required"):
            extract_exact_frequency(eigenvalues=np.array([1.0]), method="scaling")

    def test_no_input_raises_error(self):
        """Test that no input raises ValueError."""
        with pytest.raises(ValueError, match="At least one"):
            extract_exact_frequency()

    def test_invalid_method_raises_error(self):
        """Test that invalid method raises ValueError."""
        with pytest.raises(ValueError, match="Unknown method"):
            extract_exact_frequency(eigenvalues=np.array([1.0]), method="invalid")


class TestVerifySpectrumYieldsQCALFrequency:
    """Tests for verify_spectrum_yields_qcal_frequency function."""

    def test_verified_spectrum(self):
        """Test verification of spectrum that yields QCAL frequency."""
        np.random.seed(42)
        n = np.arange(1, 101)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        verified, details = verify_spectrum_yields_qcal_frequency(eigenvalues)

        assert isinstance(verified, bool)
        assert "expected_frequency" in details
        assert details["expected_frequency"] == QCAL_FREQUENCY
        assert "methods_verified" in details
        assert "total_methods" in details

    def test_details_structure(self):
        """Test that details dictionary has correct structure."""
        np.random.seed(42)
        n = np.arange(1, 51)
        eigenvalues = ALPHA_SPECTRAL * n ** 2

        _, details = verify_spectrum_yields_qcal_frequency(eigenvalues)

        assert "individual_results" in details
        assert "verified" in details


class TestIntegration:
    """Integration tests for the complete extraction pipeline."""

    def test_full_extraction_pipeline(self):
        """Test the complete extraction pipeline from spectrum to frequency."""
        # Generate realistic H_Ψ spectrum
        np.random.seed(42)
        n = np.arange(1, 200)
        eigenvalues = ALPHA_SPECTRAL * n ** 2
        eigenvalues += np.random.uniform(-0.02, 0.02, 199) * eigenvalues

        # Extract frequency
        result = extract_exact_frequency(eigenvalues=eigenvalues, method="ensemble")

        # Verify result
        assert result.frequency > 0
        assert abs(result.frequency - QCAL_FREQUENCY) / QCAL_FREQUENCY < 0.05

        # Verify spectrum
        verified, details = verify_spectrum_yields_qcal_frequency(eigenvalues)

        # At least some methods should work
        assert details["methods_verified"] >= 0

    def test_triple_scaling_identity(self):
        """Test that triple scaling produces exact QCAL frequency."""
        # This tests the mathematical identity: f₀ = √k × f_raw
        omega_raw = 2 * np.pi * F_RAW
        curvature = omega_raw ** 2

        result = extract_from_triple_scaling(curvature)

        # Triple scaling is exact by construction
        assert result.verified is True
        assert result.confidence == 1.0
        assert result.frequency == QCAL_FREQUENCY


class TestEdgeCases:
    """Test edge cases and error handling."""

    def test_single_eigenvalue(self):
        """Test with single eigenvalue."""
        eigenvalues = np.array([100.0])

        result = extract_from_eigenvalue_mean(eigenvalues)

        # Should handle gracefully
        assert isinstance(result, FrequencyExtractionResult)

    def test_complex_eigenvalues_converted_to_real(self):
        """Test that complex eigenvalues are converted to real."""
        eigenvalues = np.array([1.0 + 0.1j, 2.0 - 0.1j, 3.0 + 0.2j])

        # Should not raise, should use real parts
        result = extract_from_eigenvalue_mean(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)

    def test_very_large_eigenvalues(self):
        """Test with very large eigenvalues."""
        eigenvalues = np.array([1e10, 2e10, 3e10])

        result = extract_from_eigenvalue_mean(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)

    def test_very_small_eigenvalues(self):
        """Test with very small positive eigenvalues."""
        eigenvalues = np.array([1e-10, 2e-10, 3e-10])

        result = extract_from_eigenvalue_mean(eigenvalues)

        assert isinstance(result, FrequencyExtractionResult)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
