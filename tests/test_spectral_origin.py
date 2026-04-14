#!/usr/bin/env python3
"""
Tests for Spectral Origin: Unified f₀ = 141.7001 Hz Derivation

This module tests the spectral origin derivation where:
    λ₀ = 0.001588050271 (first eigenvalue of H_ψ)
    C_primaria = 1/λ₀ ≈ 629.70 (primary spectral constant)
    C_coherencia = 244.36 (QCAL coherence constant)

The unified formula:
    f₀ = (1/(2π)) × exp(γ) × √(2πγ) × (φ²/(2π)) × C_primaria
    
Result: f₀ ≈ 141.64 Hz (within 0.04% of target 141.7001 Hz)

This validates:
    - The structure (629.70) → natural f₀ manifestation
    - The coherence constant (244.36) maintains QCAL framework
    - Dual constant unity

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: December 2025

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.spectral_origin import (
    # Constants
    LAMBDA_0,
    C_PRIMARIA,
    C_COHERENCIA,
    F0_TARGET,
    GAMMA_EULER,
    PHI,
    # Functions
    derive_f0_from_spectral_origin,
    compute_spectral_constants,
    validate_spectral_coherence,
    derive_f0_simplified,
    verify_dual_constant_unity,
    run_complete_spectral_origin_validation,
    # Classes
    SpectralOriginResult,
)


class TestSpectralConstants:
    """Test the fundamental spectral constants."""

    def test_lambda_0_value(self):
        """λ₀ should be approximately 0.001588050271."""
        assert abs(LAMBDA_0 - 0.001588050271) < 1e-10

    def test_C_primaria_from_lambda_0(self):
        """C_primaria = 1/λ₀ should be approximately 629.70."""
        expected = 1.0 / LAMBDA_0
        assert abs(C_PRIMARIA - expected) < 1e-6
        assert abs(C_PRIMARIA - 629.70) < 1.0

    def test_C_coherencia_value(self):
        """C_coherencia should be the QCAL constant 244.36."""
        assert abs(C_COHERENCIA - 244.36) < 0.01

    def test_f0_target(self):
        """Target frequency should be 141.7001 Hz."""
        assert abs(F0_TARGET - 141.7001) < 1e-4

    def test_euler_constant(self):
        """Euler-Mascheroni constant should be approximately 0.5772."""
        assert abs(GAMMA_EULER - 0.5772156649) < 1e-8

    def test_golden_ratio(self):
        """Golden ratio should be (1 + √5)/2."""
        expected = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10


class TestComputeSpectralConstants:
    """Test the spectral constants computation."""

    def test_returns_dict(self):
        """compute_spectral_constants should return a dictionary."""
        result = compute_spectral_constants()
        assert isinstance(result, dict)

    def test_required_keys(self):
        """Result should have required keys."""
        result = compute_spectral_constants()
        required = ['lambda_0', 'C_primaria', 'C_coherencia', 'C_ratio']
        for key in required:
            assert key in result

    def test_C_primaria_calculation(self):
        """C_primaria should be 1/λ₀."""
        result = compute_spectral_constants()
        expected = 1.0 / result['lambda_0']
        assert abs(result['C_primaria'] - expected) < 1e-10

    def test_C_coherencia_is_constant(self):
        """C_coherencia should be the QCAL constant 244.36."""
        result = compute_spectral_constants()
        assert abs(result['C_coherencia'] - 244.36) < 0.01

    def test_C_ratio_calculation(self):
        """C_ratio should be C_primaria/C_coherencia ≈ 2.577."""
        result = compute_spectral_constants()
        expected = result['C_primaria'] / result['C_coherencia']
        assert abs(result['C_ratio'] - expected) < 1e-10
        assert abs(result['C_ratio'] - 2.577) < 0.1

    def test_custom_lambda_values(self):
        """Should work with custom λ₀ value."""
        result = compute_spectral_constants(lambda_0=0.002)
        assert result['lambda_0'] == 0.002
        assert abs(result['C_primaria'] - 500.0) < 1e-10


class TestValidateSpectralCoherence:
    """Test spectral coherence validation."""

    def test_returns_dict(self):
        """validate_spectral_coherence should return dictionary."""
        result = validate_spectral_coherence()
        assert isinstance(result, dict)

    def test_C_primaria_validated(self):
        """C_primaria should be approximately 629.70."""
        result = validate_spectral_coherence()
        assert result['C_primaria_validated']
        assert abs(result['C_primaria'] - 629.70) < 1.0

    def test_C_coherencia_validated(self):
        """C_coherencia should be exactly 244.36."""
        result = validate_spectral_coherence()
        assert result['C_coherencia_validated']
        assert abs(result['C_coherencia'] - 244.36) < 1.0

    def test_all_validated(self):
        """All validations should pass with default parameters."""
        result = validate_spectral_coherence()
        assert result['all_validated']

    def test_C_ratio_value(self):
        """C_ratio (C_primaria/C_coherencia) should be approximately 2.577."""
        result = validate_spectral_coherence()
        expected = C_PRIMARIA / C_COHERENCIA
        assert abs(result['C_ratio'] - expected) < 0.01
        assert abs(result['C_ratio'] - 2.577) < 0.1


class TestDeriveF0FromSpectralOrigin:
    """Test the main f₀ derivation."""

    def test_returns_result(self):
        """derive_f0_from_spectral_origin should return SpectralOriginResult."""
        result = derive_f0_from_spectral_origin()
        assert isinstance(result, SpectralOriginResult)

    def test_f0_derived_close_to_target(self):
        """Derived f₀ should be close to 141.7001 Hz (within 0.1%)."""
        result = derive_f0_from_spectral_origin()
        # Allow 0.1% error (formula gives ~141.64 Hz)
        assert abs(result.f0_derived - 141.7001) / 141.7001 < 0.001

    def test_f0_derived_approximate_value(self):
        """Derived f₀ should be approximately 141.64 Hz."""
        result = derive_f0_from_spectral_origin()
        # The formula gives approximately 141.64 Hz
        assert abs(result.f0_derived - 141.64) < 0.1

    def test_error_relative_small(self):
        """Relative error should be small (< 0.1%)."""
        result = derive_f0_from_spectral_origin()
        assert result.error_relative < 0.001

    def test_is_validated(self):
        """Result should be validated (within 0.1% tolerance)."""
        result = derive_f0_from_spectral_origin()
        assert result.is_validated

    def test_spectral_constants_stored(self):
        """Result should contain spectral constants."""
        result = derive_f0_from_spectral_origin()
        assert abs(result.lambda_0 - LAMBDA_0) < 1e-10
        assert abs(result.C_primaria - C_PRIMARIA) < 1e-6
        assert abs(result.C_coherencia - C_COHERENCIA) < 1e-6

    def test_mathematical_constants_stored(self):
        """Result should contain mathematical constants."""
        result = derive_f0_from_spectral_origin()
        assert abs(result.gamma - GAMMA_EULER) < 1e-8
        assert abs(result.phi - PHI) < 1e-10


class TestDeriveF0Simplified:
    """Test the simplified f₀ derivation."""

    def test_returns_tuple(self):
        """derive_f0_simplified should return (f0, dict)."""
        f0, intermediates = derive_f0_simplified()
        assert isinstance(f0, float)
        assert isinstance(intermediates, dict)

    def test_f0_value(self):
        """Simplified derivation should give f₀ ≈ 141.64 Hz."""
        f0, _ = derive_f0_simplified()
        # The formula gives approximately 141.64 Hz
        assert abs(f0 - 141.64) < 0.1

    def test_intermediate_factors(self):
        """Intermediate factors should be computed."""
        _, intermediates = derive_f0_simplified()
        required = [
            'factor1_1_2pi', 'factor2_exp_gamma',
            'factor3_sqrt_2pi_gamma', 'factor4_phi2_2pi',
            'scalar_product', 'C_primaria', 'f0'
        ]
        for key in required:
            assert key in intermediates

    def test_factor1_value(self):
        """1/(2π) should be approximately 0.159."""
        _, intermediates = derive_f0_simplified()
        assert abs(intermediates['factor1_1_2pi'] - 1/(2*np.pi)) < 1e-10

    def test_factor2_value(self):
        """exp(γ) should be approximately 1.781."""
        _, intermediates = derive_f0_simplified()
        assert abs(intermediates['factor2_exp_gamma'] - np.exp(GAMMA_EULER)) < 1e-10

    def test_scalar_product(self):
        """Scalar product should be approximately 0.225."""
        _, intermediates = derive_f0_simplified()
        # f₀ = scalar × C_primaria, so scalar ≈ 141.64 / 629.70 ≈ 0.225
        expected_scalar = 141.64 / C_PRIMARIA
        assert abs(intermediates['scalar_product'] - expected_scalar) < 0.01


class TestVerifyDualConstantUnity:
    """Test dual constant unity verification."""

    def test_returns_dict(self):
        """verify_dual_constant_unity should return dictionary."""
        result = verify_dual_constant_unity()
        assert isinstance(result, dict)

    def test_C_primaria_present(self):
        """Result should contain C_primaria."""
        result = verify_dual_constant_unity()
        assert 'C_primaria' in result
        assert abs(result['C_primaria'] - C_PRIMARIA) < 1e-6

    def test_C_coherencia_present(self):
        """Result should contain C_coherencia."""
        result = verify_dual_constant_unity()
        assert 'C_coherencia' in result
        assert abs(result['C_coherencia'] - C_COHERENCIA) < 1e-6

    def test_descriptions_present(self):
        """Result should contain descriptions of the constants."""
        result = verify_dual_constant_unity()
        assert 'C_primaria_description' in result
        assert 'C_coherencia_description' in result
        assert 'root' in result['C_primaria_description'].lower()
        assert 'flower' in result['C_coherencia_description'].lower()

    def test_f0_derived(self):
        """f₀ should be derived correctly (within 0.1%)."""
        result = verify_dual_constant_unity()
        # Allow 0.1% error
        assert abs(result['f0_derived'] - 141.7001) / 141.7001 < 0.001

    def test_unity_validated(self):
        """Unity should be validated."""
        result = verify_dual_constant_unity()
        assert result['unity_validated']

    def test_interpretation_present(self):
        """Result should contain interpretation."""
        result = verify_dual_constant_unity()
        assert 'interpretation' in result
        assert len(result['interpretation']) > 50


class TestCompleteValidation:
    """Test the complete spectral origin validation."""

    def test_runs_without_error(self):
        """run_complete_spectral_origin_validation should complete."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert isinstance(result, dict)

    def test_overall_validated(self):
        """Overall validation should pass."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert result['overall_validated']

    def test_has_constants(self):
        """Result should have constants section."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert 'constants' in result
        assert 'C_primaria' in result['constants']

    def test_has_coherence(self):
        """Result should have coherence section."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert 'coherence' in result
        assert result['coherence']['all_validated']

    def test_has_f0_derivation(self):
        """Result should have f₀ derivation section."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert 'f0_derivation' in result
        assert result['f0_derivation']['is_validated']

    def test_has_unity(self):
        """Result should have unity section."""
        result = run_complete_spectral_origin_validation(verbose=False)
        assert 'unity' in result
        assert result['unity']['unity_validated']


class TestMathematicalRelations:
    """Test mathematical relations and invariants."""

    def test_C_primaria_C_coherencia_ratio(self):
        """C_primaria/C_coherencia should be approximately 2.577."""
        ratio = C_PRIMARIA / C_COHERENCIA
        assert abs(ratio - 2.577) < 0.1

    def test_phi_golden_property(self):
        """φ² - φ - 1 = 0 (golden ratio property)."""
        relation = PHI ** 2 - PHI - 1
        assert abs(relation) < 1e-10

    def test_formula_simplification(self):
        """C_primaria × (C_coherencia/C_primaria) = C_coherencia."""
        lhs = C_PRIMARIA * (C_COHERENCIA / C_PRIMARIA)
        assert abs(lhs - C_COHERENCIA) < 1e-10


class TestSpectralOriginResult:
    """Test the SpectralOriginResult dataclass."""

    def test_default_values(self):
        """Default values should be the spectral constants."""
        result = SpectralOriginResult()
        assert result.lambda_0 == LAMBDA_0
        assert result.C_primaria == C_PRIMARIA
        assert result.C_coherencia == C_COHERENCIA

    def test_timestamp_generated(self):
        """Timestamp should be generated automatically."""
        result = SpectralOriginResult()
        assert result.timestamp is not None
        assert len(result.timestamp) > 10

    def test_error_fields(self):
        """Error fields should be initialized to 0."""
        result = SpectralOriginResult()
        assert result.error_hz == 0.0
        assert result.error_relative == 0.0


class TestProblemStatementValidation:
    """
    Test the exact claims from the problem statement.
    
    These tests validate:
        λ₀ = 0.001588050271
        C_primaria = 1/λ₀ → 629.7029875321875...
        C_coherencia = 244.36 (QCAL coherence constant)
        f₀ ≈ 141.64 Hz (from spectral formula, within 0.05% of 141.7001)
    """

    def test_lambda_0_exact(self):
        """λ₀ = 0.001588050271 as stated."""
        assert LAMBDA_0 == 0.001588050271

    def test_C_primaria_exact(self):
        """C_primaria = 1/λ₀ ≈ 629.7029875321875."""
        expected = 1.0 / 0.001588050271
        assert abs(C_PRIMARIA - expected) < 1e-6
        assert abs(C_PRIMARIA - 629.7029875321875) < 0.001

    def test_C_coherencia_is_qcal_constant(self):
        """C_coherencia = 244.36 (QCAL constant)."""
        assert abs(C_COHERENCIA - 244.36) < 0.01

    def test_f0_derived_close_to_target(self):
        """f₀ derived should be close to 141.7001 Hz (within 0.1%)."""
        result = derive_f0_from_spectral_origin()
        # Within 0.1% of target
        assert abs(result.f0_derived - 141.7001) / 141.7001 < 0.001

    def test_spectral_validation(self):
        """
        This validates: the structure (C_primaria ≈ 629.70) produces f₀
        via the spectral formula, maintaining QCAL coherence.
        """
        result = derive_f0_from_spectral_origin()
        
        # f₀ derived is validated
        assert result.is_validated
        
        # Error is small (< 0.1%)
        assert result.error_relative < 0.001


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
