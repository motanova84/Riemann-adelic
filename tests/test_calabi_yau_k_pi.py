#!/usr/bin/env python3
"""
Tests for Universal Invariant k_Π Validation on Calabi-Yau Varieties

This test suite validates the computational framework for the universal
spectral invariant k_Π ≈ 2.5773 across different Calabi-Yau manifolds.

Author: José Manuel Mota Burruezo
Date: 2025
"""

import pytest
import sys
from pathlib import Path
import numpy as np

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_calabi_yau_k_pi import (
    CYModel,
    euler_characteristic,
    generate_spectral_data,
    compute_k_pi,
    get_calabi_yau_models,
    validate_k_pi_universality,
    display_model_table
)


class TestCYModel:
    """Test CYModel dataclass and properties."""

    def test_cymodel_creation(self):
        """Test that CYModel can be created with required fields."""
        model = CYModel(
            name="Test Model",
            key="test",
            h11=1,
            h21=50,
            equation="test equation",
            reference="Test"
        )
        assert model.name == "Test Model"
        assert model.key == "test"
        assert model.h11 == 1
        assert model.h21 == 50

    def test_euler_characteristic_quintic(self):
        """Test Euler characteristic for quintic (h11=1, h21=101)."""
        chi = euler_characteristic(1, 101)
        assert chi == -200

    def test_euler_characteristic_bicubic(self):
        """Test Euler characteristic for bicubic (h11=2, h21=83)."""
        chi = euler_characteristic(2, 83)
        assert chi == -162

    def test_euler_characteristic_octic(self):
        """Test Euler characteristic for octic (h11=1, h21=145)."""
        chi = euler_characteristic(1, 145)
        assert chi == -288

    def test_euler_characteristic_pfaffian(self):
        """Test Euler characteristic for Pfaffian (h11=2, h21=59)."""
        chi = euler_characteristic(2, 59)
        assert chi == -114


class TestSpectralDataGeneration:
    """Test spectral data generation for Calabi-Yau models."""

    def test_generate_spectral_data_returns_positive(self):
        """Test that generated eigenvalues are positive."""
        model = get_calabi_yau_models()[0]  # Quintic Fermat
        spectrum, _ = generate_spectral_data(model, seed=42)
        assert all(lam > 0 for lam in spectrum)

    def test_generate_spectral_data_reproducible(self):
        """Test that spectral data generation is reproducible with same seed."""
        model = get_calabi_yau_models()[0]
        spectrum1, _ = generate_spectral_data(model, seed=42)
        spectrum2, _ = generate_spectral_data(model, seed=42)
        np.testing.assert_array_almost_equal(spectrum1, spectrum2)

    def test_generate_spectral_data_different_seeds(self):
        """Test that different seeds produce different spectra."""
        model = get_calabi_yau_models()[0]
        spectrum1, _ = generate_spectral_data(model, seed=42)
        spectrum2, _ = generate_spectral_data(model, seed=123)
        assert not np.allclose(spectrum1, spectrum2)

    def test_generate_spectral_data_reference_modes(self):
        """Test that reference mode counts match expected values."""
        models = get_calabi_yau_models()
        expected_modes = {
            'quintic_fermat': 892, 'bicubic': 743,
            'octic_fermat': 1121, 'pfaffian_cy': 634
        }

        for model in models:
            _, ref_modes = generate_spectral_data(model, seed=42)
            assert ref_modes == expected_modes[model.key]


class TestKPiComputation:
    """Test k_Π invariant computation."""

    def test_compute_k_pi_basic(self):
        """Test basic k_Π computation."""
        # Create simple eigenvalue array
        eigenvalues = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
        k_pi, mu1, mu2 = compute_k_pi(eigenvalues)

        # mu1 = (1+2+3+4+5)/5 = 3.0
        assert mu1 == pytest.approx(3.0)

        # mu2 = (1+4+9+16+25)/5 = 11.0
        assert mu2 == pytest.approx(11.0)

        # k_Pi = 11.0/3.0
        assert k_pi == pytest.approx(11.0 / 3.0)

    def test_compute_k_pi_empty_raises(self):
        """Test that empty spectrum raises ValueError."""
        with pytest.raises(ValueError):
            compute_k_pi(np.array([]))

    def test_compute_k_pi_returns_tuple(self):
        """Test that compute_k_pi returns a tuple of three values."""
        eigenvalues = np.array([1.0, 2.0, 3.0])
        result = compute_k_pi(eigenvalues)
        assert isinstance(result, tuple)
        assert len(result) == 3

    def test_k_pi_near_expected_for_quintic(self):
        """Test that k_Π for quintic is near 2.5773."""
        model = get_calabi_yau_models()[0]  # Quintic Fermat
        spectrum, _ = generate_spectral_data(model, seed=42)
        k_pi, _, _ = compute_k_pi(spectrum)

        # Should be within 2% of 2.5773
        assert abs(k_pi - 2.5773) < 0.05


class TestCalabiYauModels:
    """Test the Calabi-Yau model definitions."""

    def test_get_calabi_yau_models_count(self):
        """Test that we have exactly 4 models."""
        models = get_calabi_yau_models()
        assert len(models) == 4

    def test_model_names(self):
        """Test that model names match expected values."""
        models = get_calabi_yau_models()
        names = [m.name for m in models]
        assert "Quintic Fermat" in names
        assert "Bicúbica" in names
        assert "Octic" in names
        assert "Pfaffian CY" in names

    def test_hodge_numbers(self):
        """Test Hodge numbers for each model."""
        models = get_calabi_yau_models()
        hodge = {m.name: (m.h11, m.h21) for m in models}

        assert hodge["Quintic Fermat"] == (1, 101)
        assert hodge["Bicúbica"] == (2, 83)
        assert hodge["Octic"] == (1, 145)
        assert hodge["Pfaffian CY"] == (2, 59)


class TestKPiUniversality:
    """Test the universality of k_Π across all models."""

    def test_validate_k_pi_returns_dict(self):
        """Test that validation returns expected structure."""
        results = validate_k_pi_universality(verbose=False, seed=42)

        assert isinstance(results, dict)
        assert 'models' in results
        assert 'k_pi_mean' in results
        assert 'k_pi_std' in results
        assert 'is_universal' in results

    def test_all_models_validated(self):
        """Test that all 4 models are validated."""
        results = validate_k_pi_universality(verbose=False, seed=42)
        assert len(results['models']) == 4

    def test_k_pi_mean_near_expected(self):
        """Test that mean k_Π is near 2.5773."""
        results = validate_k_pi_universality(verbose=False, seed=42)

        # Mean should be within 2% of 2.5773
        assert abs(results['k_pi_mean'] - 2.5773) < 0.05

    def test_k_pi_std_small(self):
        """Test that standard deviation of k_Π is small."""
        results = validate_k_pi_universality(verbose=False, seed=42)

        # Std should be less than 0.05 (indicating universality)
        assert results['k_pi_std'] < 0.05

    def test_universality_holds(self):
        """Test that universality criterion is satisfied."""
        results = validate_k_pi_universality(verbose=False, seed=42)
        assert results['is_universal']

    def test_model_results_have_required_fields(self):
        """Test that each model result has required fields."""
        results = validate_k_pi_universality(verbose=False, seed=42)

        required_fields = [
            'name', 'key', 'h11', 'h21', 'euler',
            'k_pi', 'delta', 'mu1', 'mu2', 'n_modes'
        ]

        for model_result in results['models']:
            for field in required_fields:
                assert field in model_result


class TestDisplayFunctions:
    """Test display and output functions."""

    def test_display_model_table_runs(self):
        """Test that display_model_table runs without error."""
        # Should not raise any exceptions
        display_model_table()

    def test_validate_k_pi_verbose_runs(self):
        """Test that verbose validation runs without error."""
        # Should not raise any exceptions
        results = validate_k_pi_universality(verbose=True, seed=42)
        assert results is not None


class TestMathematicalProperties:
    """Test mathematical properties of k_Π."""

    def test_k_pi_independent_of_h11(self):
        """Test that k_Π doesn't significantly depend on h11."""
        models = get_calabi_yau_models()
        h11_1 = [m for m in models if m.h11 == 1]
        h11_2 = [m for m in models if m.h11 == 2]

        k_pi_h11_1 = []
        k_pi_h11_2 = []

        for i, model in enumerate(h11_1):
            spectrum, _ = generate_spectral_data(model, seed=42 + i)
            k_pi, _, _ = compute_k_pi(spectrum)
            k_pi_h11_1.append(k_pi)

        for i, model in enumerate(h11_2):
            spectrum, _ = generate_spectral_data(model, seed=42 + i + 100)
            k_pi, _, _ = compute_k_pi(spectrum)
            k_pi_h11_2.append(k_pi)

        # Both groups should have similar mean k_Π
        mean1 = np.mean(k_pi_h11_1)
        mean2 = np.mean(k_pi_h11_2)
        assert abs(mean1 - mean2) < 0.1

    def test_k_pi_convergence_large_sample(self):
        """Test that k_Π converges to theoretical value with large samples."""
        # Generate very large sample
        np.random.seed(42)
        alpha = 2.5773 - 1.0  # For k = alpha + 1
        large_sample = np.random.gamma(alpha, 1.0, 500000)

        k_pi, _, _ = compute_k_pi(large_sample)

        # Should be very close to 2.5773 with large sample
        assert abs(k_pi - 2.5773) < 0.01


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
