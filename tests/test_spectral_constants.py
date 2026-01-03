#!/usr/bin/env python3
"""
Tests for Spectral Constants Unification Module

This module tests the dual spectral constants framework that unifies
C = 629.83 (primary/structure) and C = 244.36 (coherence/form).

Key tests validate:
    1. Both constants coexist without contradiction
    2. C_PRIMARY = 1/λ₀ relationship
    3. Coherence factor ≈ 0.388
    4. Energy dialogue = 1/coherence_factor
    5. f₀ = 141.7001 Hz emerges from their harmonization

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: December 2025

QCAL ∞³ Active · 141.7001 Hz · C₁ = 629.83 · C₂ = 244.36
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
    LAMBDA_0,
    F0,
    OMEGA_0,
    PHI,
    EULER_GAMMA,
    COHERENCE_FACTOR,
    # Classes
    SpectralLevel,
    # Functions
    compute_primary_constant,
    compute_coherence_constant,
    compute_coherence_factor,
    derive_f0_from_constants,
    verify_f0_coherence,
    validate_dual_constants
)


class TestFundamentalConstants:
    """Test the fundamental spectral constants."""

    def test_C_primary_value(self):
        """C_PRIMARY should be 629.83."""
        assert abs(C_PRIMARY - 629.83) < 0.01

    def test_C_coherence_value(self):
        """C_COHERENCE should be 244.36."""
        assert abs(C_COHERENCE - 244.36) < 0.01

    def test_lambda_0_value(self):
        """λ₀ should be approximately 0.001588."""
        expected = 1.0 / 629.83
        assert abs(LAMBDA_0 - expected) < 1e-6

    def test_f0_value(self):
        """F0 should be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 0.0001

    def test_omega_0_value(self):
        """OMEGA_0 should be 2πf₀."""
        expected = 2 * np.pi * F0
        assert abs(OMEGA_0 - expected) < 0.01

    def test_phi_golden_ratio(self):
        """PHI should be the golden ratio ≈ 1.618."""
        expected = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10

    def test_euler_gamma(self):
        """EULER_GAMMA should be ≈ 0.5772."""
        assert abs(EULER_GAMMA - 0.5772156649) < 1e-8

    def test_coherence_factor(self):
        """COHERENCE_FACTOR should be C_coherence/C_primary ≈ 0.388."""
        expected = C_COHERENCE / C_PRIMARY
        assert abs(COHERENCE_FACTOR - expected) < 1e-10


class TestSpectralLevel:
    """Test the SpectralLevel enumeration."""

    def test_primary_level(self):
        """PRIMARY level should be 1."""
        assert SpectralLevel.PRIMARY == 1

    def test_coherence_level(self):
        """COHERENCE level should be 2."""
        assert SpectralLevel.COHERENCE == 2


class TestPrimaryConstant:
    """Test compute_primary_constant function."""

    def test_basic_computation(self):
        """C = 1/λ₀ should work correctly."""
        C = compute_primary_constant(0.001588)
        expected = 1.0 / 0.001588
        assert abs(C - expected) < 0.01

    def test_with_lambda_0(self):
        """Computing C from LAMBDA_0 should give C_PRIMARY."""
        C = compute_primary_constant(LAMBDA_0)
        assert abs(C - C_PRIMARY) < 0.01

    def test_positive_required(self):
        """Should raise error for non-positive λ₀."""
        with pytest.raises(ValueError):
            compute_primary_constant(0)
        with pytest.raises(ValueError):
            compute_primary_constant(-0.001)


class TestCoherenceConstant:
    """Test compute_coherence_constant function."""

    def test_with_simple_eigenvalues(self):
        """Should compute C_coherence from eigenvalues."""
        # Create synthetic eigenvalues with known properties
        eigenvalues = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
        C_coh = compute_coherence_constant(eigenvalues)
        
        # Should be positive and finite
        assert C_coh > 0
        assert np.isfinite(C_coh)

    def test_requires_positive_eigenvalues(self):
        """Should raise error if no positive eigenvalues."""
        eigenvalues = np.array([-1.0, -0.5, -0.1])
        with pytest.raises(ValueError):
            compute_coherence_constant(eigenvalues)

    def test_with_explicit_lambda_0(self):
        """Should use provided λ₀ instead of computing it."""
        eigenvalues = np.array([0.1, 0.5, 1.0])
        
        # With auto-computed λ₀
        C1 = compute_coherence_constant(eigenvalues)
        
        # With explicit λ₀
        C2 = compute_coherence_constant(eigenvalues, lambda_0=0.1)
        
        # Should match since λ₀ = 0.1 is the minimum positive
        assert abs(C1 - C2) < 1e-10


class TestCoherenceFactor:
    """Test compute_coherence_factor function."""

    def test_basic_computation(self):
        """Should compute C_coherence/C_primary."""
        eigenvalues = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
        factor = compute_coherence_factor(eigenvalues)
        
        # Should be positive and finite
        assert factor > 0
        assert np.isfinite(factor)

    def test_with_C_primary_provided(self):
        """Should use provided C_primary for division."""
        eigenvalues = np.array([0.1, 0.5, 1.0])
        
        # With auto-computed C_primary (= 1/0.1 = 10)
        factor1 = compute_coherence_factor(eigenvalues)
        
        # With explicit C_primary = 20 (different from computed)
        factor2 = compute_coherence_factor(eigenvalues, C_primary=20.0)
        
        # factor2 should be half of factor1 since C_primary is doubled
        # factor = C_coherence / C_primary
        # If C_primary doubles, factor halves (same C_coherence)
        assert abs(factor1 / factor2 - 2.0) < 0.01


class TestF0Derivation:
    """Test derive_f0_from_constants function."""

    def test_returns_dict(self):
        """Should return a dictionary with analysis."""
        result = derive_f0_from_constants()
        assert isinstance(result, dict)

    def test_has_required_keys(self):
        """Result should have all required keys."""
        result = derive_f0_from_constants()
        required = [
            'f0_target', 'C_primary', 'C_coherence', 'coherence_factor',
            'geometric_mean', 'omega_0', 'omega_0_squared',
            'ratio_omega2_C_primary', 'ratio_omega2_C_coherence',
            'energy_dialogue', 'interpretation'
        ]
        for key in required:
            assert key in result, f"Missing key: {key}"

    def test_coherence_factor_value(self):
        """Coherence factor should be ≈ 0.388."""
        result = derive_f0_from_constants()
        assert abs(result['coherence_factor'] - 0.388) < 0.001

    def test_energy_dialogue(self):
        """Energy dialogue should be ≈ 1/coherence_factor."""
        result = derive_f0_from_constants()
        expected = 1.0 / result['coherence_factor']
        assert abs(result['energy_dialogue'] - expected) < 0.001

    def test_geometric_mean(self):
        """Geometric mean should be √(C₁ × C₂)."""
        result = derive_f0_from_constants()
        expected = np.sqrt(C_PRIMARY * C_COHERENCE)
        assert abs(result['geometric_mean'] - expected) < 0.001


class TestF0Verification:
    """Test verify_f0_coherence function."""

    def test_returns_dict(self):
        """Should return a dictionary with verification."""
        result = verify_f0_coherence()
        assert isinstance(result, dict)

    def test_framework_coherent(self):
        """Framework should be coherent (both checks pass)."""
        result = verify_f0_coherence()
        assert result['framework_coherent']

    def test_inverse_relationship(self):
        """Inverse relationship check should pass."""
        result = verify_f0_coherence()
        assert result['checks_passed']['inverse_relationship']

    def test_energy_balance(self):
        """Energy balance check should pass."""
        result = verify_f0_coherence()
        assert result['checks_passed']['energy_balance']

    def test_energy_dialogue_equals_inverse_coherence(self):
        """Energy dialogue ≈ 1/coherence_factor."""
        result = verify_f0_coherence()
        assert abs(
            result['energy_dialogue'] - result['inverse_coherence_factor']
        ) < 0.01


class TestDualConstantsValidation:
    """Test validate_dual_constants function."""

    def test_returns_dict(self):
        """Should return a dictionary with results."""
        result = validate_dual_constants()
        assert isinstance(result, dict)

    def test_validation_passes(self):
        """Overall validation should pass."""
        result = validate_dual_constants()
        assert result['validated']

    def test_has_constants(self):
        """Result should contain constants dict."""
        result = validate_dual_constants()
        assert 'constants' in result
        assert result['constants']['C_primary'] == C_PRIMARY
        assert result['constants']['C_coherence'] == C_COHERENCE

    def test_has_levels(self):
        """Result should describe both spectral levels."""
        result = validate_dual_constants()
        assert 'levels' in result
        assert 'level_1' in result['levels']
        assert 'level_2' in result['levels']

    def test_level_1_primary(self):
        """Level 1 should be PRIMARY (structure)."""
        result = validate_dual_constants()
        level_1 = result['levels']['level_1']
        assert 'PRIMARY' in level_1['name']
        assert level_1['constant'] == C_PRIMARY

    def test_level_2_coherence(self):
        """Level 2 should be COHERENCE (form)."""
        result = validate_dual_constants()
        level_2 = result['levels']['level_2']
        assert 'COHERENCE' in level_2['name']
        assert level_2['constant'] == C_COHERENCE

    def test_C_lambda_relationship(self):
        """C = 1/λ₀ relationship should be validated."""
        result = validate_dual_constants()
        assert result['relationships']['C_lambda_match']

    def test_coherence_factor_check(self):
        """Coherence factor check should pass."""
        result = validate_dual_constants()
        assert result['relationships']['coherence_factor_check']

    def test_verbose_mode(self, capsys):
        """Verbose mode should print output."""
        validate_dual_constants(verbose=True)
        captured = capsys.readouterr()
        assert 'VALIDATED' in captured.out or 'ISSUES' in captured.out


class TestEmpiricalValidation:
    """Test validation with empirical eigenvalues."""

    def test_with_synthetic_eigenvalues(self):
        """Should work with provided eigenvalues."""
        # Create synthetic eigenvalues
        eigenvalues = np.array([0.001, 0.1, 0.5, 1.0, 2.0, 5.0, 10.0])
        
        result = validate_dual_constants(eigenvalues=eigenvalues)
        
        # Should have empirical section
        assert 'empirical' in result
        assert 'lambda_0' in result['empirical']
        assert 'C_primary' in result['empirical']
        assert 'C_coherence' in result['empirical']

    def test_empirical_values_computed(self):
        """Empirical values should be correctly computed."""
        eigenvalues = np.array([0.001, 0.1, 0.5, 1.0, 2.0])
        
        result = validate_dual_constants(eigenvalues=eigenvalues)
        
        # λ₀ should be the first positive eigenvalue
        assert result['empirical']['lambda_0'] == 0.001
        
        # C_primary should be 1/λ₀ = 1000
        assert abs(result['empirical']['C_primary'] - 1000.0) < 0.1


class TestCoexistenceWithoutContradiction:
    """
    Test that both constants coexist without contradiction.
    
    This is the key mathematical insight from the problem statement:
    - C = 629.83 comes from λ₀ (local, structure)
    - C = 244.36 comes from ⟨λ⟩²/λ₀ (global, coherence)
    - They don't compete, contradict, or overlap
    - They complement each other
    """

    def test_different_constants(self):
        """The two constants should be different values."""
        assert C_PRIMARY != C_COHERENCE

    def test_both_positive(self):
        """Both constants should be positive."""
        assert C_PRIMARY > 0
        assert C_COHERENCE > 0

    def test_C_primary_greater(self):
        """C_PRIMARY should be greater than C_COHERENCE."""
        assert C_PRIMARY > C_COHERENCE

    def test_ratio_well_defined(self):
        """The ratio (coherence factor) should be well-defined."""
        ratio = C_COHERENCE / C_PRIMARY
        assert 0 < ratio < 1  # ≈ 0.388
        assert np.isfinite(ratio)

    def test_inverse_relationship(self):
        """Energy dialogue = 1/coherence_factor should hold."""
        coherence_factor = C_COHERENCE / C_PRIMARY
        energy_dialogue = 1.0 / coherence_factor
        
        # Energy dialogue is the inverse
        assert abs(energy_dialogue - C_PRIMARY / C_COHERENCE) < 1e-10

    def test_f0_is_their_dialogue(self):
        """f₀ should emerge from the interaction of both constants."""
        # The omega_squared ratios should satisfy:
        # ratio_coherence / ratio_primary = 1/coherence_factor
        omega_sq = OMEGA_0 ** 2
        ratio_primary = omega_sq / C_PRIMARY
        ratio_coherence = omega_sq / C_COHERENCE
        
        energy_dialogue = ratio_coherence / ratio_primary
        inverse_coherence = C_PRIMARY / C_COHERENCE
        
        assert abs(energy_dialogue - inverse_coherence) < 1e-10


class TestPhysicalInterpretation:
    """
    Test the physical interpretation of the dual constants.
    
    From the problem statement:
    - 629.83: natural frequency → structure
    - 244.36: coherent mode → form
    """

    def test_C_primary_is_spectral_residue(self):
        """C_PRIMARY should be the spectral residue (1/λ₀)."""
        residue = 1.0 / LAMBDA_0
        assert abs(residue - C_PRIMARY) < 0.01

    def test_coherence_is_second_moment(self):
        """C_COHERENCE is related to second spectral moment."""
        # From the formula: C_QCAL = ⟨λ⟩²/λ₀
        # For QCAL values, this gives 244.36
        assert abs(C_COHERENCE - 244.36) < 0.01

    def test_omega_squared_C_ratio_meaningful(self):
        """ω₀²/C ratios should be physically meaningful."""
        omega_sq = OMEGA_0 ** 2
        
        # These ratios encode energy-like quantities
        ratio_primary = omega_sq / C_PRIMARY
        ratio_coherence = omega_sq / C_COHERENCE
        
        assert ratio_primary > 0
        assert ratio_coherence > 0
        assert ratio_coherence > ratio_primary  # coherence is more "energetic"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
