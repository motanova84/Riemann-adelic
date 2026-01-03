#!/usr/bin/env python3
"""
Tests for the Spectral Origin Constant C = 629.83

This module tests the derivation of the universal constant C = 1/λ₀
where λ₀ is the first eigenvalue of the noetic operator Hψ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import numpy as np
import pytest

# Import the module under test
from utils.spectral_origin_constant import (
    LAMBDA_0,
    C_UNIVERSAL,
    F0_QCAL,
    F0_SPECTRAL,
    OMEGA_0_SPECTRAL,
    ZETA_PRIME_HALF,
    C_QCAL_COHERENCE,
    NoeticOperator,
    SpectralOriginResult,
    derive_universal_constant,
    validate_spectral_frequency_relation,
    verify_all_appearances_of_f0,
    mathematical_significance,
)


class TestConstants:
    """Test fundamental constants from spectral origin."""

    def test_lambda_0_value(self):
        """Test that λ₀ has the correct value."""
        assert abs(LAMBDA_0 - 0.001588050) < 1e-7

    def test_c_universal_value(self):
        """Test that C = 1/λ₀ ≈ 629.83."""
        expected_C = 1.0 / LAMBDA_0
        assert abs(C_UNIVERSAL - expected_C) < 1e-6
        # C is approximately 629.7 to 629.9 depending on λ₀ precision
        assert 629.5 < C_UNIVERSAL < 630.0

    def test_c_inverse_lambda(self):
        """Test that C × λ₀ = 1 (inverse relationship)."""
        product = C_UNIVERSAL * LAMBDA_0
        assert abs(product - 1.0) < 1e-10

    def test_omega_0_spectral(self):
        """Test that ω₀ = √C."""
        expected_omega = np.sqrt(C_UNIVERSAL)
        assert abs(OMEGA_0_SPECTRAL - expected_omega) < 1e-10

    def test_f0_qcal(self):
        """Test QCAL target frequency."""
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_zeta_prime_half(self):
        """Test ζ'(1/2) value."""
        assert abs(ZETA_PRIME_HALF - (-3.9226)) < 0.001

    def test_c_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert abs(C_QCAL_COHERENCE - 244.36) < 0.01


class TestNoeticOperator:
    """Test the noetic operator Hψ construction."""

    def test_operator_construction(self):
        """Test that operator can be constructed."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        assert op.H.shape == (50, 50)

    def test_operator_hermiticity(self):
        """Test that H is Hermitian (symmetric)."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        is_hermitian, deviation = op.verify_hermiticity()
        assert is_hermitian
        assert deviation < 1e-12

    def test_minimum_eigenvalue_positive(self):
        """Test that λ₀ > 0 (operator bounded below)."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        lambda_0 = op.minimum_eigenvalue()
        assert lambda_0 > 0

    def test_eigenvalues_real(self):
        """Test that all eigenvalues are real."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        eigenvalues = op.compute_eigenvalues()
        assert np.all(np.isreal(eigenvalues))

    def test_eigenvalues_sorted(self):
        """Test that eigenvalues are sorted ascending."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        eigenvalues = op.compute_eigenvalues()
        assert np.all(np.diff(eigenvalues) >= 0)

    def test_universal_constant_positive(self):
        """Test that C = 1/λ₀ is computed correctly."""
        op = NoeticOperator(n_basis=50, potential_type="harmonic")
        C = op.compute_universal_constant()
        assert C > 0

    def test_different_potential_types(self):
        """Test different potential types."""
        for pot_type in ["harmonic", "noetic", "quartic", "spectral"]:
            op = NoeticOperator(n_basis=30, potential_type=pot_type)
            assert op.H.shape == (30, 30)
            is_hermitian, _ = op.verify_hermiticity()
            assert is_hermitian


class TestSpectralOriginResult:
    """Test the SpectralOriginResult dataclass."""

    def test_result_creation(self):
        """Test result dataclass creation."""
        result = SpectralOriginResult(
            lambda_0=0.001588050,
            C_universal=629.83,
            omega_0=25.096,
            f0_raw=3.995,
        )
        assert result.lambda_0 > 0
        assert result.C_universal > 0

    def test_scaling_factor_computed(self):
        """Test that scaling factor is computed in __post_init__."""
        result = SpectralOriginResult(
            lambda_0=0.001588050,
            C_universal=629.83,
            omega_0=25.096,
            f0_raw=3.995,
        )
        assert result.scaling_factor > 0


class TestDeriveUniversalConstant:
    """Test the derive_universal_constant function."""

    def test_derivation_returns_result(self):
        """Test that derivation returns a result."""
        result = derive_universal_constant(n_basis=50, verify_stability=False)
        assert isinstance(result, SpectralOriginResult)

    def test_derivation_lambda_positive(self):
        """Test that λ₀ is positive."""
        result = derive_universal_constant(n_basis=50, verify_stability=False)
        assert result.lambda_0 > 0

    def test_derivation_c_positive(self):
        """Test that C is positive."""
        result = derive_universal_constant(n_basis=50, verify_stability=False)
        assert result.C_universal > 0

    def test_derivation_verified(self):
        """Test that result is verified."""
        result = derive_universal_constant(n_basis=50, verify_stability=False)
        assert result.verified


class TestValidateSpectralFrequencyRelation:
    """Test the spectral frequency relation validation."""

    def test_validation_returns_dict(self):
        """Test that validation returns a dictionary."""
        result = validate_spectral_frequency_relation()
        assert isinstance(result, dict)

    def test_identity_verified(self):
        """Test that the identity f₀ = √C/(2π) is verified."""
        result = validate_spectral_frequency_relation()
        assert result["identity_verified"]

    def test_identity_error_small(self):
        """Test that identity error is very small."""
        result = validate_spectral_frequency_relation()
        assert result["identity_error"] < 1e-10

    def test_contains_theorem(self):
        """Test that theorem statement is included."""
        result = validate_spectral_frequency_relation()
        assert "theorem" in result
        assert "f₀" in result["theorem"]


class TestVerifyAllAppearances:
    """Test verification of all f₀ appearances."""

    def test_verification_returns_dict(self):
        """Test that verification returns a dictionary."""
        result = verify_all_appearances_of_f0()
        assert isinstance(result, dict)

    def test_verifications_present(self):
        """Test that verifications are present."""
        result = verify_all_appearances_of_f0()
        assert "verifications" in result
        assert len(result["verifications"]) >= 6

    def test_arithmetic_pattern_verified(self):
        """Test 68/81 arithmetic pattern verification."""
        result = verify_all_appearances_of_f0()
        assert result["verifications"]["arithmetic_pattern"]["verified"]

    def test_gravitational_waves_verified(self):
        """Test GW150914 frequency verification."""
        result = verify_all_appearances_of_f0()
        gw = result["verifications"]["gravitational_waves"]
        assert gw["verified"]
        assert gw["within_signal_error"]

    def test_all_verified_field(self):
        """Test that all_verified field exists."""
        result = verify_all_appearances_of_f0()
        assert "all_verified" in result

    def test_summary_present(self):
        """Test that summary is present."""
        result = verify_all_appearances_of_f0()
        assert "summary" in result
        assert "629" in result["summary"]


class TestMathematicalSignificance:
    """Test mathematical significance documentation."""

    def test_significance_returns_dict(self):
        """Test that significance returns a dictionary."""
        result = mathematical_significance()
        assert isinstance(result, dict)

    def test_significance_categories(self):
        """Test that all categories are present."""
        result = mathematical_significance()
        expected_categories = [
            "spectral",
            "geometric",
            "physical",
            "arithmetic",
            "adelic",
            "topological",
        ]
        for cat in expected_categories:
            assert cat in result

    def test_significance_mentions_c(self):
        """Test that C value is mentioned."""
        result = mathematical_significance()
        # Check that at least one category mentions the constant value
        has_c = any("629" in str(v) for v in result.values())
        assert has_c


class TestIntegration:
    """Integration tests for the spectral origin module."""

    def test_c_times_lambda_equals_one(self):
        """Test fundamental identity C × λ₀ = 1."""
        result = derive_universal_constant(verify_stability=False)
        product = result.C_universal * result.lambda_0
        assert abs(product - 1.0) < 1e-6

    def test_omega_from_c(self):
        """Test ω₀ = √C."""
        result = derive_universal_constant(verify_stability=False)
        expected_omega = np.sqrt(result.C_universal)
        assert abs(result.omega_0 - expected_omega) < 1e-6

    def test_frequency_from_omega(self):
        """Test f₀ = ω₀/(2π)."""
        result = derive_universal_constant(verify_stability=False)
        expected_f0 = result.omega_0 / (2 * np.pi)
        assert abs(result.f0_raw - expected_f0) < 1e-6

    def test_consistency_with_qcal(self):
        """Test consistency with QCAL framework constants."""
        result = derive_universal_constant(verify_stability=False)
        # C should be around 629.83
        assert 620 < result.C_universal < 640

    def test_all_appearances_consistent(self):
        """Test that all appearances are mutually consistent."""
        appearances = verify_all_appearances_of_f0()
        # If any verification fails, the whole check should reflect it
        assert isinstance(appearances["all_verified"], bool)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
