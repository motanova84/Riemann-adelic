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
Tests for the P17 Adelic-Fractal Equilibrium Module.

Tests verify that p = 17 is the optimal prime for adelic-fractal equilibrium
and validate the mathematical properties of the balance and equilibrium functions.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import pytest
import sys
import os

try:
    import mpmath as mp
except ImportError:
    pytest.skip("mpmath is required for these tests", allow_module_level=True)

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from utils.p17_balance_optimality import (
    balance,
    equilibrium,
    adelic_factor,
    fractal_suppression,
    verify_p17_optimality,
    connection_68_81,
    get_qcal_parameters,
    get_physical_primes,
    get_primes_to_check,
    find_optimal_prime,
    compute_R_psi,
    generate_equilibrium_data,
    is_prime,
    F0_UNIVERSAL,
    COHERENCE_C,
    OPTIMAL_PRIME,
    REFERENCE_EQUILIBRIUM,
)


class TestIsPrime:
    """Tests for the is_prime function."""
    
    def test_prime_numbers(self):
        """Test that known primes return True."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
        for p in primes:
            assert is_prime(p) is True, f"{p} should be prime"
    
    def test_composite_numbers(self):
        """Test that composite numbers return False."""
        composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20]
        for n in composites:
            assert is_prime(n) is False, f"{n} should not be prime"
    
    def test_edge_cases(self):
        """Test edge cases."""
        assert is_prime(0) is False
        assert is_prime(1) is False
        assert is_prime(2) is True
        assert is_prime(-5) is False


class TestBalanceFunction:
    """Tests for the balance function."""
    
    def test_balance_positive(self):
        """Test that balance is positive for all primes."""
        primes = get_primes_to_check()[:10]
        for p in primes:
            b = balance(p)
            assert float(b) > 0, f"balance({p}) should be positive"
    
    def test_balance_formula(self):
        """Test that balance = exp(π√p/2) / p^(3/2)."""
        mp.mp.dps = 80
        for p in [11, 13, 17, 19, 23]:
            expected = mp.exp(mp.pi * mp.sqrt(p) / 2) / mp.power(p, mp.mpf('1.5'))
            actual = balance(p, precision=80)
            assert abs(float(actual - expected)) < 1e-70
    
    def test_balance_at_17(self):
        """Test balance value at p=17."""
        b17 = balance(17, precision=80)
        # balance(17) ≈ 9.27
        assert 9.0 < float(b17) < 10.0
    
    def test_balance_increases_for_large_primes(self):
        """Test that balance increases for sufficiently large primes."""
        # Balance should generally increase for primes > ~3
        b17 = balance(17)
        b29 = balance(29)
        b47 = balance(47)
        assert float(b29) > float(b17)
        assert float(b47) > float(b29)


class TestAdelicAndFractalFactors:
    """Tests for adelic and fractal factors."""
    
    def test_adelic_factor_positive(self):
        """Test that adelic factor is positive."""
        for p in [2, 3, 5, 7, 11, 17]:
            a = adelic_factor(p)
            assert float(a) > 0
    
    def test_adelic_factor_increases(self):
        """Test that adelic factor increases with p."""
        a11 = adelic_factor(11)
        a17 = adelic_factor(17)
        a29 = adelic_factor(29)
        assert float(a17) > float(a11)
        assert float(a29) > float(a17)
    
    def test_fractal_suppression_positive(self):
        """Test that fractal suppression is positive."""
        for p in [2, 3, 5, 7, 11, 17]:
            f = fractal_suppression(p)
            assert float(f) > 0
    
    def test_fractal_suppression_decreases(self):
        """Test that fractal suppression decreases with p."""
        f11 = fractal_suppression(11)
        f17 = fractal_suppression(17)
        f29 = fractal_suppression(29)
        assert float(f11) > float(f17)
        assert float(f17) > float(f29)
    
    def test_balance_equals_product(self):
        """Test that balance = adelic_factor × fractal_suppression."""
        for p in [11, 17, 23]:
            a = adelic_factor(p, precision=80)
            f = fractal_suppression(p, precision=80)
            b = balance(p, precision=80)
            product = a * f
            assert abs(float(b - product)) < 1e-70


class TestEquilibriumFunction:
    """Tests for the equilibrium function."""
    
    def test_equilibrium_minimum_at_17(self):
        """Test that equilibrium has minimum at p=17."""
        primes = get_physical_primes()
        eq_values = {p: float(equilibrium(p)) for p in primes}
        min_prime = min(eq_values, key=eq_values.get)
        assert min_prime == 17, f"Minimum should be at p=17, got p={min_prime}"
    
    def test_equilibrium_at_17(self):
        """Test equilibrium value at p=17."""
        eq17 = equilibrium(17)
        # equilibrium(17) = 76.143 (by construction)
        assert abs(float(eq17) - 76.143) < 0.001
    
    def test_equilibrium_local_minimum(self):
        """Test that p=17 is a local minimum."""
        eq13 = equilibrium(13)
        eq17 = equilibrium(17)
        eq19 = equilibrium(19)
        assert float(eq17) < float(eq13), "eq(17) < eq(13)"
        assert float(eq17) < float(eq19), "eq(17) < eq(19)"
    
    def test_equilibrium_v_shape(self):
        """Test V-shape: decreasing before 17, increasing after."""
        eq11 = equilibrium(11)
        eq13 = equilibrium(13)
        eq17 = equilibrium(17)
        eq19 = equilibrium(19)
        eq23 = equilibrium(23)
        
        # Decreasing towards 17
        assert float(eq11) > float(eq13) > float(eq17)
        # Increasing away from 17
        assert float(eq17) < float(eq19) < float(eq23)


class TestP17Optimality:
    """Tests for p=17 optimality verification."""
    
    def test_verification_passes(self):
        """Test that verification passes."""
        result = verify_p17_optimality(precision=80)
        assert result['verification_passed'] is True
    
    def test_17_is_optimal(self):
        """Test that p=17 is identified as optimal."""
        result = verify_p17_optimality(precision=80)
        assert result['is_17_optimal'] is True
        assert result['optimal_prime'] == 17
    
    def test_local_minimum_check(self):
        """Test local minimum detection."""
        result = verify_p17_optimality(precision=80)
        assert result['local_minimum'] is True
    
    def test_global_minimum_check(self):
        """Test global minimum detection within physical primes."""
        result = verify_p17_optimality(precision=80)
        assert result['global_minimum'] is True


class TestConnection6881:
    """Tests for the 68/81 connection."""
    
    def test_decimal_value(self):
        """Test 68/81 decimal value."""
        conn = connection_68_81()
        assert conn['decimal_68_81'].startswith('0.839506172')
    
    def test_period_length(self):
        """Test period length is 9."""
        conn = connection_68_81()
        assert conn['period_length'] == 9
    
    def test_period_digits(self):
        """Test period digits are 839506172."""
        conn = connection_68_81()
        assert conn['period_digits'] == '839506172'
    
    def test_17_divides_68(self):
        """Test that 17 divides 68."""
        conn = connection_68_81()
        assert conn['is_17_divisor_of_68'] is True
        assert 68 % 17 == 0
        assert 68 // 17 == 4


class TestQCALParameters:
    """Tests for QCAL parameters."""
    
    def test_f0_universal(self):
        """Test universal frequency."""
        params = get_qcal_parameters()
        assert params['f0_universal_hz'] == F0_UNIVERSAL
        assert abs(params['f0_universal_hz'] - 141.7001) < 0.0001
    
    def test_coherence_c(self):
        """Test coherence constant."""
        params = get_qcal_parameters()
        assert params['coherence_C'] == COHERENCE_C
        assert abs(params['coherence_C'] - 244.36) < 0.01
    
    def test_optimal_prime(self):
        """Test optimal prime is 17."""
        params = get_qcal_parameters()
        assert params['optimal_prime_p0'] == 17
    
    def test_balance_at_p0(self):
        """Test balance at optimal prime."""
        params = get_qcal_parameters()
        assert params['balance_p0'] > 0
        # balance(17) ≈ 9.27
        assert 9.0 < params['balance_p0'] < 10.0


class TestFindOptimalPrime:
    """Tests for find_optimal_prime function."""
    
    def test_finds_17(self):
        """Test that optimal prime is 17."""
        optimal, min_val, all_vals = find_optimal_prime()
        assert optimal == 17
    
    def test_minimum_value(self):
        """Test minimum value is at p=17."""
        optimal, min_val, all_vals = find_optimal_prime()
        assert float(min_val) == float(all_vals[17])
    
    def test_custom_primes(self):
        """Test with custom prime list."""
        custom_primes = [11, 13, 17, 19, 23]
        optimal, min_val, all_vals = find_optimal_prime(primes=custom_primes)
        assert optimal == 17
        assert len(all_vals) == 5


class TestDataGeneration:
    """Tests for data generation functions."""
    
    def test_generate_equilibrium_data(self):
        """Test equilibrium data generation."""
        data = generate_equilibrium_data()
        assert len(data) > 0
        assert all('prime' in d for d in data)
        assert all('equilibrium' in d for d in data)
        assert all('balance' in d for d in data)
    
    def test_data_minimum_at_17(self):
        """Test that data shows minimum at p=17."""
        data = generate_equilibrium_data()
        min_entry = min(data, key=lambda d: d['equilibrium'])
        assert min_entry['prime'] == 17
        assert min_entry['is_minimum'] is True
    
    def test_reference_values_included(self):
        """Test that reference values are included."""
        data = generate_equilibrium_data()
        for entry in data:
            if entry['prime'] in REFERENCE_EQUILIBRIUM:
                assert entry['reference'] is not None


class TestComputeRPsi:
    """Tests for R_Ψ computation."""
    
    def test_r_psi_positive(self):
        """Test R_Ψ is positive."""
        for p in [11, 13, 17, 19, 23]:
            r_psi = compute_R_psi(p)
            assert float(r_psi) > 0
    
    def test_r_psi_equals_balance(self):
        """Test R_Ψ equals balance function."""
        for p in [11, 17, 29]:
            r_psi = compute_R_psi(p, precision=80)
            b = balance(p, precision=80)
            assert abs(float(r_psi - b)) < 1e-70


class TestPrimeUtilities:
    """Tests for prime utility functions."""
    
    def test_primes_to_check(self):
        """Test get_primes_to_check returns primes."""
        primes = get_primes_to_check()
        assert 2 in primes
        assert 17 in primes
        assert 101 in primes
        assert 4 not in primes  # Not prime
    
    def test_physical_primes(self):
        """Test get_physical_primes returns expected primes."""
        primes = get_physical_primes()
        assert 11 in primes
        assert 17 in primes
        assert 47 in primes
        assert 2 not in primes  # Too small
        assert 53 not in primes  # Too large


class TestConstants:
    """Tests for module constants."""
    
    def test_f0_universal_value(self):
        """Test F0_UNIVERSAL constant."""
        assert F0_UNIVERSAL == 141.7001
    
    def test_coherence_c_value(self):
        """Test COHERENCE_C constant."""
        assert COHERENCE_C == 244.36
    
    def test_optimal_prime_value(self):
        """Test OPTIMAL_PRIME constant."""
        assert OPTIMAL_PRIME == 17
    
    def test_reference_equilibrium(self):
        """Test REFERENCE_EQUILIBRIUM dictionary."""
        assert REFERENCE_EQUILIBRIUM[17] == 76.143
        assert len(REFERENCE_EQUILIBRIUM) == 6
