#!/usr/bin/env python3
"""
Tests for P17 Balance Optimality

Tests the spectral map of primes to frequencies and verifies that:
1. p = 17 does NOT minimize equilibrium(p) = exp(π√p/2) / p^(3/2)
2. p = 17 IS the unique prime producing f₀ = 141.7001 Hz
3. The theoretical correction is properly implemented

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.p17_balance_optimality import (
    # Constants
    C_LIGHT,
    L_PLANCK,
    SCALE_FACTOR,
    F0_TARGET,
    # Functions
    equilibrium,
    frequency_from_prime,
    find_equilibrium_minimum,
    find_resonance_prime,
    compute_spectral_map,
    verify_p17_resonance,
    p17_yields_resonance,
    run_complete_verification,
    # Classes
    SpectralMapResult,
    P17ResonanceVerification,
)


class TestPhysicalConstants:
    """Test the physical constants used in calculations."""

    def test_speed_of_light(self):
        """Speed of light should be ~3e8 m/s."""
        assert abs(C_LIGHT - 299792458.0) < 1

    def test_planck_length(self):
        """Planck length should be ~1.6e-35 m."""
        assert 1e-36 < L_PLANCK < 1e-34

    def test_scale_factor_order(self):
        """Scale factor should be ~1.9e41."""
        assert 1e40 < SCALE_FACTOR < 1e42

    def test_target_frequency(self):
        """Target frequency should be 141.7001 Hz."""
        assert abs(F0_TARGET - 141.7001) < 1e-4


class TestEquilibriumFunction:
    """Test the equilibrium function."""

    def test_equilibrium_positive(self):
        """Equilibrium should be positive for all primes."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        for p in primes:
            assert equilibrium(p) > 0

    def test_equilibrium_formula(self):
        """Verify equilibrium formula: exp(π√p/2) / p^(3/2)."""
        p = 17
        expected = np.exp(np.pi * np.sqrt(p) / 2) / (p ** 1.5)
        assert abs(equilibrium(p) - expected) / expected < 1e-6

    def test_equilibrium_not_minimized_at_17(self):
        """The equilibrium is NOT minimized at p = 17."""
        eq_3 = equilibrium(3)
        eq_17 = equilibrium(17)
        # p = 3 has lower equilibrium than p = 17
        assert eq_3 < eq_17

    def test_equilibrium_minimum_not_at_17(self):
        """Verify that the minimum is NOT at p = 17."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        min_p = min(primes, key=equilibrium)
        # The minimum is at p = 3, not at p = 17
        assert min_p != 17


class TestFindEquilibriumMinimum:
    """Test finding the equilibrium minimum."""

    def test_minimum_is_at_p3(self):
        """The equilibrium minimum among first primes is at p = 3."""
        min_p, min_val = find_equilibrium_minimum()
        assert min_p == 3

    def test_minimum_value_reasonable(self):
        """The minimum value should be around 2.9."""
        min_p, min_val = find_equilibrium_minimum()
        assert 2.5 < min_val < 3.5


class TestFrequencyFromPrime:
    """Test the frequency calculation from primes."""

    def test_frequency_positive(self):
        """Frequency should be positive for all primes."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        for p in primes:
            assert frequency_from_prime(p) > 0

    def test_p17_produces_f0(self):
        """p = 17 should produce f₀ ≈ 141.7001 Hz."""
        f17 = frequency_from_prime(17)
        assert abs(f17 - F0_TARGET) < 0.01

    def test_p11_produces_lower_frequency(self):
        """p = 11 should produce ~76.7 Hz."""
        f11 = frequency_from_prime(11)
        assert 70 < f11 < 85

    def test_p29_produces_higher_frequency(self):
        """p = 29 should produce ~461.8 Hz."""
        f29 = frequency_from_prime(29)
        assert 450 < f29 < 480


class TestFindResonancePrime:
    """Test finding the resonance prime."""

    def test_resonance_prime_is_17(self):
        """The prime producing f₀ ≈ 141.7001 Hz is p = 17."""
        p, f = find_resonance_prime()
        assert p == 17

    def test_resonance_frequency_correct(self):
        """The resonance frequency should be close to target."""
        p, f = find_resonance_prime()
        assert abs(f - F0_TARGET) < 0.01


class TestSpectralMap:
    """Test the spectral map computation."""

    def test_spectral_map_returns_list(self):
        """compute_spectral_map should return a list."""
        results = compute_spectral_map()
        assert isinstance(results, list)
        assert len(results) > 0

    def test_spectral_map_entries_are_results(self):
        """Each entry should be a SpectralMapResult."""
        results = compute_spectral_map()
        for r in results:
            assert isinstance(r, SpectralMapResult)

    def test_spectral_map_p17_is_resonance(self):
        """p = 17 should be marked as resonance."""
        results = compute_spectral_map()
        p17_result = next(r for r in results if r.prime == 17)
        assert p17_result.is_resonance == True

    def test_spectral_map_other_primes_not_resonance(self):
        """Other primes should NOT be marked as resonance."""
        results = compute_spectral_map()
        for r in results:
            if r.prime != 17:
                assert r.is_resonance == False

    def test_spectral_map_p17_has_noetic_note(self):
        """p = 17 should have 'noetic point' note."""
        results = compute_spectral_map()
        p17_result = next(r for r in results if r.prime == 17)
        assert "noetic" in p17_result.notes.lower()


class TestVerifyP17Resonance:
    """Test the p17 resonance verification."""

    def test_verification_returns_result(self):
        """verify_p17_resonance should return P17ResonanceVerification."""
        result = verify_p17_resonance()
        assert isinstance(result, P17ResonanceVerification)

    def test_verification_is_verified(self):
        """The resonance should be verified."""
        result = verify_p17_resonance()
        assert result.is_verified == True

    def test_verification_shows_minimum_not_at_17(self):
        """Verification should show that minimum is NOT at p = 17."""
        result = verify_p17_resonance()
        assert result.equilibrium_minimum_prime != 17

    def test_verification_relative_error_small(self):
        """Relative error should be very small (< 0.1%)."""
        result = verify_p17_resonance()
        assert result.relative_error < 0.001

    def test_verification_has_interpretation(self):
        """Verification should include interpretation."""
        result = verify_p17_resonance()
        assert len(result.interpretation) > 0
        assert "resonance" in result.interpretation.lower()


class TestP17YieldsResonance:
    """Test the main theorem function."""

    def test_theorem_holds(self):
        """p17_yields_resonance theorem should return True."""
        assert p17_yields_resonance() == True


class TestTheoreticalCorrection:
    """Test that the theoretical correction is properly implemented."""

    def test_equilibrium_minimum_documented(self):
        """The code should document that minimum is NOT at p = 17."""
        result = verify_p17_resonance()
        assert "minimum" in result.interpretation.lower()
        assert str(result.equilibrium_minimum_prime) in result.interpretation

    def test_resonance_vs_optimization(self):
        """The distinction between resonance and optimization should be clear."""
        result = verify_p17_resonance()
        assert "resonance" in result.interpretation.lower() or \
               "RESONANCE" in result.interpretation

    def test_minimum_is_not_17(self):
        """Explicitly verify that the equilibrium minimum is not at p = 17."""
        min_p, _ = find_equilibrium_minimum()
        # The minimum is at p = 3 for the canonical equilibrium function
        assert min_p == 3
        assert min_p != 17


class TestRunCompleteVerification:
    """Test the complete verification run."""

    def test_run_complete_verification(self):
        """run_complete_verification should complete without error."""
        result = run_complete_verification(verbose=False)
        assert isinstance(result, P17ResonanceVerification)

    def test_run_complete_verification_verified(self):
        """Complete verification should show theorem verified."""
        result = run_complete_verification(verbose=False)
        assert result.is_verified == True


class TestSpectralMapValues:
    """Test specific spectral map values from the problem statement."""

    def test_p11_frequency(self):
        """p = 11 → 76.7 Hz."""
        f = frequency_from_prime(11)
        assert abs(f - 76.7) < 1.0

    def test_p17_frequency(self):
        """p = 17 → 141.7 Hz."""
        f = frequency_from_prime(17)
        assert abs(f - 141.7) < 0.1

    def test_p29_frequency(self):
        """p = 29 → 461.8 Hz."""
        f = frequency_from_prime(29)
        assert abs(f - 461.8) < 1.0


class TestResonanceInterpretation:
    """Test the interpretation aspects."""

    def test_p17_is_resonance_point(self):
        """p = 17 should be identified as a resonance point."""
        result = verify_p17_resonance()
        assert "resonance" in result.interpretation.lower()

    def test_p17_is_not_optimization_point(self):
        """p = 17 should NOT be identified as an optimization point."""
        result = verify_p17_resonance()
        # The interpretation should clarify it's NOT an optimization
        assert "not" in result.interpretation.lower() or \
               "NOT" in result.interpretation


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
