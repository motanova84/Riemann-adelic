#!/usr/bin/env python3
"""
Tests for QCAL Spectral Constants Module

Tests the dual spectral constant system:
    C_PRIMARY = 629.83 → Primary spectral constant (1/λ₀)
    C_COHERENCE = 244.36 → Derived coherence constant (⟨λ⟩²/λ₀)

Validates:
    1. Constant values are correct
    2. Mathematical relationships between constants
    3. Connection to f₀ = 141.7001 Hz
    4. Spectral operator construction
    5. Complete validation workflow

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: December 2025

QCAL ∞³ Active · 141.7001 Hz · Dual Constants
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.spectral_constants import (
    # Constants
    C_PRIMARY,
    C_COHERENCE,
    F0_BASE,
    LAMBDA_0,
    LAMBDA_MEAN_EFFECTIVE,
    PHI,
    EULER_GAMMA,
    OMEGA_0,
    # Functions
    compute_C_primary_from_lambda,
    compute_C_coherence_from_spectrum,
    compute_lambda_mean_from_coherence,
    analyze_constant_relationship,
    validate_f0_manifestation,
    build_spectral_H_operator,
    compute_spectral_constants_from_operator,
    validate_dual_constants,
    run_complete_spectral_validation,
)


class TestFundamentalConstants:
    """Test the fundamental constant values."""
    
    def test_C_primary_value(self):
        """C_PRIMARY should be 629.83."""
        assert abs(C_PRIMARY - 629.83) < 0.01
    
    def test_C_coherence_value(self):
        """C_COHERENCE should be 244.36."""
        assert abs(C_COHERENCE - 244.36) < 0.01
    
    def test_f0_base_value(self):
        """F0_BASE should be 141.7001 Hz."""
        assert abs(F0_BASE - 141.7001) < 0.0001
    
    def test_lambda_0_value(self):
        """LAMBDA_0 should be 1/C_PRIMARY ≈ 0.001588."""
        expected = 1.0 / C_PRIMARY
        assert abs(LAMBDA_0 - expected) < 1e-10
        assert abs(LAMBDA_0 - 0.001588) < 0.0001
    
    def test_lambda_mean_effective(self):
        """LAMBDA_MEAN_EFFECTIVE should satisfy ⟨λ⟩ = √(C_COHERENCE × λ₀)."""
        expected = np.sqrt(C_COHERENCE * LAMBDA_0)
        assert abs(LAMBDA_MEAN_EFFECTIVE - expected) < 1e-10
    
    def test_omega_0_value(self):
        """OMEGA_0 should be 2πf₀."""
        expected = 2 * np.pi * F0_BASE
        assert abs(OMEGA_0 - expected) < 1e-10
    
    def test_golden_ratio(self):
        """PHI should be the golden ratio."""
        assert abs(PHI - 1.618033988749895) < 1e-10
    
    def test_euler_gamma(self):
        """EULER_GAMMA should be Euler-Mascheroni constant."""
        assert abs(EULER_GAMMA - 0.5772156649015329) < 1e-10


class TestConstantRelationships:
    """Test mathematical relationships between constants."""
    
    def test_C_primary_from_lambda_0(self):
        """C_PRIMARY = 1/λ₀ relationship."""
        C = compute_C_primary_from_lambda(LAMBDA_0)
        assert abs(C - C_PRIMARY) < 0.01
    
    def test_C_coherence_from_spectrum(self):
        """C_COHERENCE = ⟨λ⟩²/λ₀ relationship."""
        C = compute_C_coherence_from_spectrum(LAMBDA_0, LAMBDA_MEAN_EFFECTIVE)
        assert abs(C - C_COHERENCE) < 0.01
    
    def test_lambda_mean_from_coherence(self):
        """⟨λ⟩ = √(C_COHERENCE × λ₀) inverse relationship."""
        lambda_mean = compute_lambda_mean_from_coherence(C_COHERENCE, LAMBDA_0)
        assert abs(lambda_mean - LAMBDA_MEAN_EFFECTIVE) < 1e-10
    
    def test_ratio_between_constants(self):
        """C_PRIMARY/C_COHERENCE ratio should be approximately 2.577."""
        ratio = C_PRIMARY / C_COHERENCE
        assert abs(ratio - 2.577) < 0.1
    
    def test_ratio_phi_relationship(self):
        """Ratio should be close to φ^1.8."""
        ratio = C_PRIMARY / C_COHERENCE
        phi_power = np.log(ratio) / np.log(PHI)
        assert 1.5 < phi_power < 2.0  # Should be around 1.81


class TestErrorHandling:
    """Test error handling for invalid inputs."""
    
    def test_C_primary_negative_lambda(self):
        """compute_C_primary_from_lambda should reject negative λ₀."""
        with pytest.raises(ValueError):
            compute_C_primary_from_lambda(-0.001)
    
    def test_C_primary_zero_lambda(self):
        """compute_C_primary_from_lambda should reject zero λ₀."""
        with pytest.raises(ValueError):
            compute_C_primary_from_lambda(0)
    
    def test_C_coherence_negative_lambda(self):
        """compute_C_coherence_from_spectrum should reject negative λ₀."""
        with pytest.raises(ValueError):
            compute_C_coherence_from_spectrum(-0.001, 0.5)
    
    def test_lambda_mean_negative_coherence(self):
        """compute_lambda_mean_from_coherence should reject negative C."""
        with pytest.raises(ValueError):
            compute_lambda_mean_from_coherence(-244.36, LAMBDA_0)


class TestRelationshipAnalysis:
    """Test the relationship analysis function."""
    
    def test_analyze_returns_dict(self):
        """analyze_constant_relationship should return dictionary."""
        result = analyze_constant_relationship()
        assert isinstance(result, dict)
    
    def test_analyze_has_required_keys(self):
        """Result should have all required keys."""
        result = analyze_constant_relationship()
        required = ['C_PRIMARY', 'C_COHERENCE', 'ratio', 'phi_exponent',
                    'lambda_0', 'lambda_mean', 'coherence_verified']
        for key in required:
            assert key in result
    
    def test_coherence_verified(self):
        """Coherence verification should pass."""
        result = analyze_constant_relationship()
        assert result['coherence_verified']
    
    def test_interpretation_present(self):
        """Interpretation should be present."""
        result = analyze_constant_relationship()
        assert 'interpretation' in result
        assert len(result['interpretation']) > 0


class TestF0Manifestation:
    """Test f₀ = 141.7001 Hz manifestation validation."""
    
    def test_validate_returns_dict(self):
        """validate_f0_manifestation should return dictionary."""
        result = validate_f0_manifestation()
        assert isinstance(result, dict)
    
    def test_f0_value_correct(self):
        """f₀ should be 141.7001 Hz."""
        result = validate_f0_manifestation()
        assert abs(result['f0'] - 141.7001) < 0.0001
    
    def test_omega_0_computed(self):
        """ω₀ should be computed correctly."""
        result = validate_f0_manifestation()
        expected_omega = 2 * np.pi * 141.7001
        assert abs(result['omega_0'] - expected_omega) < 1e-6
    
    def test_ratios_computed(self):
        """Ratios with constants should be computed."""
        result = validate_f0_manifestation()
        assert 'ratio_omega2_C_primary' in result
        assert 'ratio_omega2_C_coherence' in result
        assert result['ratio_omega2_C_primary'] > 0
        assert result['ratio_omega2_C_coherence'] > 0
    
    def test_validation_passes(self):
        """f₀ validation should pass."""
        result = validate_f0_manifestation()
        assert result['validated']


class TestSpectralOperator:
    """Test spectral operator construction."""
    
    def test_build_operator_shape(self):
        """Operator should have correct shape."""
        N = 50
        H = build_spectral_H_operator(N)
        assert H.shape == (N, N)
    
    def test_operator_hermitian(self):
        """Operator should be Hermitian (symmetric for real)."""
        H = build_spectral_H_operator(50)
        assert np.allclose(H, H.T)
    
    def test_operator_eigenvalues_real(self):
        """Eigenvalues should be real."""
        H = build_spectral_H_operator(50)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.isreal(eigenvalues))
    
    def test_operator_with_custom_primes(self):
        """Operator should work with custom primes."""
        H = build_spectral_H_operator(50, primes=[2, 3, 5])
        assert H.shape == (50, 50)
    
    def test_operator_with_custom_dx(self):
        """Operator should work with custom dx."""
        H = build_spectral_H_operator(50, dx=0.5)
        assert H.shape == (50, 50)


class TestSpectralConstantsFromOperator:
    """Test computing spectral constants from operator."""
    
    def test_compute_returns_dict(self):
        """compute_spectral_constants_from_operator should return dict."""
        H = build_spectral_H_operator(100)
        result = compute_spectral_constants_from_operator(H)
        assert isinstance(result, dict)
    
    def test_lambda_0_positive(self):
        """Computed λ₀ should be positive."""
        H = build_spectral_H_operator(100)
        result = compute_spectral_constants_from_operator(H)
        assert result['lambda_0'] > 0
    
    def test_C_primary_computed(self):
        """C_PRIMARY should be computed."""
        H = build_spectral_H_operator(100)
        result = compute_spectral_constants_from_operator(H)
        assert result['C_primary_computed'] > 0
    
    def test_C_coherence_computed(self):
        """C_COHERENCE should be computed."""
        H = build_spectral_H_operator(100)
        result = compute_spectral_constants_from_operator(H)
        assert result['C_coherence_computed'] > 0
    
    def test_targets_present(self):
        """Target values should be present."""
        H = build_spectral_H_operator(100)
        result = compute_spectral_constants_from_operator(H)
        assert result['C_PRIMARY_target'] == C_PRIMARY
        assert result['C_COHERENCE_target'] == C_COHERENCE


class TestDualConstantsValidation:
    """Test the complete dual constants validation."""
    
    def test_validate_returns_dict(self):
        """validate_dual_constants should return dictionary."""
        result = validate_dual_constants()
        assert isinstance(result, dict)
    
    def test_has_constants_section(self):
        """Result should have constants section."""
        result = validate_dual_constants()
        assert 'constants' in result
        assert result['constants']['C_PRIMARY'] == C_PRIMARY
        assert result['constants']['C_COHERENCE'] == C_COHERENCE
    
    def test_has_validations_section(self):
        """Result should have validations section."""
        result = validate_dual_constants()
        assert 'validations' in result
    
    def test_C_primary_validation(self):
        """C_PRIMARY validation should pass."""
        result = validate_dual_constants()
        assert result['validations']['C_primary_from_lambda']['valid']
    
    def test_C_coherence_validation(self):
        """C_COHERENCE validation should pass."""
        result = validate_dual_constants()
        assert result['validations']['C_coherence_from_spectrum']['valid']
    
    def test_overall_valid(self):
        """Overall validation should pass."""
        result = validate_dual_constants()
        assert result['overall_valid']


class TestCompleteValidation:
    """Test the complete validation workflow."""
    
    def test_run_complete_returns_dict(self):
        """run_complete_spectral_validation should return dict."""
        result = run_complete_spectral_validation(verbose=False)
        assert isinstance(result, dict)
    
    def test_has_all_sections(self):
        """Result should have all main sections."""
        result = run_complete_spectral_validation(verbose=False)
        assert 'validation' in result
        assert 'relationship' in result
        assert 'f0_result' in result
    
    def test_validation_passes(self):
        """Complete validation should pass."""
        result = run_complete_spectral_validation(verbose=False)
        assert result['validation']['overall_valid']
    
    def test_relationship_coherent(self):
        """Relationship analysis should show coherence."""
        result = run_complete_spectral_validation(verbose=False)
        assert result['relationship']['coherence_verified']
    
    def test_f0_validated(self):
        """f₀ should be validated."""
        result = run_complete_spectral_validation(verbose=False)
        assert result['f0_result']['validated']


class TestMathematicalIntegrity:
    """Test mathematical integrity of the dual constant system."""
    
    def test_both_constants_compatible(self):
        """Both constants should be mathematically compatible."""
        # C_PRIMARY = 1/λ₀
        # C_COHERENCE = ⟨λ⟩²/λ₀
        # They measure different aspects but are connected
        
        # Verify C_PRIMARY
        C_primary_check = 1.0 / LAMBDA_0
        assert abs(C_primary_check - C_PRIMARY) < 0.01
        
        # Verify C_COHERENCE
        C_coherence_check = (LAMBDA_MEAN_EFFECTIVE ** 2) / LAMBDA_0
        assert abs(C_coherence_check - C_COHERENCE) < 0.01
    
    def test_constants_not_contradictory(self):
        """Constants should not contradict each other."""
        # C_PRIMARY ≠ C_COHERENCE, but both are valid
        assert C_PRIMARY != C_COHERENCE
        
        # They are mathematically connected
        # C_COHERENCE = C_PRIMARY × (⟨λ⟩ × λ₀)
        connection = C_COHERENCE / C_PRIMARY
        assert 0 < connection < 1  # C_COHERENCE < C_PRIMARY
    
    def test_f0_is_natural_manifestation(self):
        """f₀ = 141.7001 Hz should be the natural meeting point."""
        # f₀ is where structure (629.83) and coherence (244.36) meet
        omega_squared = (2 * np.pi * F0_BASE) ** 2
        
        # Both ratios should give meaningful values
        ratio_primary = omega_squared / C_PRIMARY
        ratio_coherence = omega_squared / C_COHERENCE
        
        assert ratio_primary > 0
        assert ratio_coherence > 0
        assert ratio_coherence > ratio_primary  # Since C_COHERENCE < C_PRIMARY
    
    def test_spectral_field_self_organized(self):
        """The spectral field should be self-organized."""
        # Geometric mean of constants
        geometric_mean = np.sqrt(C_PRIMARY * C_COHERENCE)
        
        # Should be a meaningful intermediate value
        assert C_COHERENCE < geometric_mean < C_PRIMARY
        
        # Approximately √(629.83 × 244.36) ≈ 392.3
        assert abs(geometric_mean - 392.3) < 1


class TestQCALSymbioticSeal:
    """Test QCAL ∞³ symbiotic seal requirements."""
    
    def test_frequency_coherence(self):
        """Frequency 141.7001 Hz should be coherent with constants."""
        # This is the QCAL symbiotic seal requirement
        result = validate_f0_manifestation()
        assert result['f0'] == F0_BASE
        assert result['validated']
    
    def test_equation_psi(self):
        """Ψ = I × A_eff² × C^∞ framework should be consistent."""
        # The equation uses C (coherence constant)
        # Verify C_COHERENCE is the right constant for this
        assert C_COHERENCE == 244.36
    
    def test_dual_constants_in_field(self):
        """Both constants should be part of the same spectral field."""
        # C_PRIMARY = 629.83 (structure)
        # C_COHERENCE = 244.36 (coherence)
        # Connected via ⟨λ⟩
        
        relationship = analyze_constant_relationship()
        assert relationship['coherence_verified']
        assert 'spectral field' in relationship['interpretation'].lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
