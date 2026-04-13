#!/usr/bin/env python3
"""
Tests for the 51-node constellation and new QCAL constants.

Validates:
1. New physical constants in qcal.constants (λ₀, E₀, LIGO, GUE, Berry, Weil)
2. 51-node constellation operator (operators/constelacion_51_nodos.py)
3. Constellation validation: n=51, Ψ≥0.95, categories, Fibonacci epoch

DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

# ── Path setup ──────────────────────────────────────────────────────────────
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(REPO_ROOT / "operators"))

# ── Imports ──────────────────────────────────────────────────────────────────
from qcal.constants import (
    F0,
    C_COHERENCE,
    C_PRIMARY,
    SPEED_OF_LIGHT,
    PLANCK_CONSTANT,
    HBAR,
    BOLTZMANN,
    LAMBDA_WAVE,
    LAMBDA_WAVE_Mm,
    E0_PHOTON,
    LIGO_DETECTION_SNR,
    LIGO_DETECTION_SIGMA,
    LIGO_DETECTION_FREQ,
    GW150914_GPS_TIME,
    GW250114_GPS_TIME,
    GUE_MATRIX_N,
    GUE_MATRIX_N_SQ,
    GUE_MATRIX_PVALUE,
    GUE_MEAN_SPACING,
    GUE_MEAN_SQ_SPACING,
    GUE_KS_PVALUE_THRESHOLD,
    BERRY_EXPONENT,
    WEIL_COHERENCE,
    CONSTELLATION_N_NODES,
    CONSTELLATION_CONSTANTS,
    CONSTELLATION_STRINGS,
    FIBONACCI_SEQUENCE,
    FIBONACCI_EPOCH_YEAR,
    FIBONACCI_EPOCH_YEARS,
    CONSTELLATION_PRIMES,
    CONSTELLATION_FREQUENCY,
    DOI_RH_CONDITIONAL,
    DOI_RH_FINAL,
)
from constelacion_51_nodos import (
    ConstellationNode,
    ConstellationResult,
    build_constellation,
    compute_constellation_psi,
    validate_constellation,
    get_node_by_category,
    constellation_summary,
    N_NODES,
)


# =============================================================================
# TEST CLASS 1: Physical Constants
# =============================================================================

class TestPhysicalConstants:
    """Tests for physical constants derived from f₀ = 141.7001 Hz."""

    def test_speed_of_light_exact(self):
        """Speed of light should be exact SI value 299,792,458 m/s."""
        assert SPEED_OF_LIGHT == 299_792_458.0

    def test_planck_constant_value(self):
        """Planck constant should be exact SI value 6.62607015e-34 J·s."""
        assert abs(PLANCK_CONSTANT - 6.62607015e-34) < 1e-44

    def test_hbar_equals_h_over_2pi(self):
        """ℏ should equal h/(2π)."""
        expected = PLANCK_CONSTANT / (2.0 * math.pi)
        assert abs(HBAR - expected) < 1e-50

    def test_boltzmann_value(self):
        """Boltzmann constant should be SI value 1.380649e-23 J/K."""
        assert abs(BOLTZMANN - 1.380649e-23) < 1e-33

    def test_lambda_wave_approximately_2115_km(self):
        """λ₀ = c/f₀ should be approximately 2,115,682 m ≈ 2.115 Mm."""
        expected = SPEED_OF_LIGHT / F0
        assert abs(LAMBDA_WAVE - expected) < 1.0  # within 1 m
        # Should be approximately 2.115 Mm (problem statement)
        assert 2.11e6 < LAMBDA_WAVE < 2.12e6, f"λ₀ = {LAMBDA_WAVE/1e6:.3f} Mm"

    def test_lambda_wave_Mm(self):
        """λ₀ in Megameters should be approximately 2.115-2.116 Mm."""
        assert 2.11 < LAMBDA_WAVE_Mm < 2.12, f"λ₀ = {LAMBDA_WAVE_Mm:.3f} Mm"

    def test_lambda_consistency_with_F0(self):
        """f₀ × λ₀ should equal c."""
        product = F0 * LAMBDA_WAVE
        assert abs(product - SPEED_OF_LIGHT) < 1.0  # within 1 m/s

    def test_E0_photon_approximately_9_39e_32(self):
        """E₀ = h·f₀ should be approximately 9.39×10⁻³² J."""
        expected = PLANCK_CONSTANT * F0
        assert abs(E0_PHOTON - expected) < 1e-36  # within femto-femtojoule
        # Problem statement says 9.39e-32 J
        assert abs(E0_PHOTON - 9.39e-32) < 0.1e-32, f"E₀ = {E0_PHOTON:.2e} J"

    def test_E0_photon_positive(self):
        """Photon energy should be positive."""
        assert E0_PHOTON > 0


# =============================================================================
# TEST CLASS 2: LIGO Detection Constants
# =============================================================================

class TestLIGOConstants:
    """Tests for LIGO gravitational wave detection metrics at f₀."""

    def test_ligo_snr_value(self):
        """LIGO detection SNR should be 7.47."""
        assert abs(LIGO_DETECTION_SNR - 7.47) < 1e-10

    def test_ligo_sigma_value(self):
        """LIGO detection significance should be 10σ."""
        assert abs(LIGO_DETECTION_SIGMA - 10.0) < 1e-10

    def test_ligo_detection_freq_is_F0(self):
        """LIGO detection frequency should equal F0."""
        assert LIGO_DETECTION_FREQ == F0

    def test_ligo_snr_above_threshold(self):
        """SNR = 7.47 should exceed standard LIGO threshold of 4.5."""
        assert LIGO_DETECTION_SNR > 4.5

    def test_ligo_sigma_above_5sigma(self):
        """Detection significance 10σ should exceed standard 5σ threshold."""
        assert LIGO_DETECTION_SIGMA >= 5.0

    def test_gw150914_gps_positive(self):
        """GW150914 GPS time should be a positive integer."""
        assert GW150914_GPS_TIME > 0
        assert isinstance(GW150914_GPS_TIME, int)

    def test_gw250114_gps_after_gw150914(self):
        """GW250114 should have a later GPS time than GW150914."""
        assert GW250114_GPS_TIME > GW150914_GPS_TIME


# =============================================================================
# TEST CLASS 3: GUE Matrix Constants
# =============================================================================

class TestGUEConstants:
    """Tests for GUE matrix constants (19²=361, p=10⁻¹⁰)."""

    def test_gue_matrix_n(self):
        """GUE reference matrix dimension should be N=19."""
        assert GUE_MATRIX_N == 19

    def test_gue_matrix_n_sq(self):
        """N²=361 should be 19×19."""
        assert GUE_MATRIX_N_SQ == GUE_MATRIX_N ** 2
        assert GUE_MATRIX_N_SQ == 361

    def test_gue_matrix_pvalue(self):
        """GUE matrix p-value should be 10⁻¹⁰."""
        assert abs(GUE_MATRIX_PVALUE - 1e-10) < 1e-20

    def test_gue_mean_spacing_unity(self):
        """GUE mean spacing should be 1.0 (by normalization)."""
        assert GUE_MEAN_SPACING == 1.0

    def test_gue_mean_sq_spacing(self):
        """GUE <s²>_GUE = 3π/8 ≈ 1.178."""
        expected = 3.0 * math.pi / 8.0
        assert abs(GUE_MEAN_SQ_SPACING - expected) < 1e-12

    def test_gue_ks_threshold(self):
        """GUE KS p-value threshold should be 0.05."""
        assert abs(GUE_KS_PVALUE_THRESHOLD - 0.05) < 1e-10

    def test_berry_exponent(self):
        """Berry exponent should be 7/8 = 0.875."""
        assert abs(BERRY_EXPONENT - 7.0 / 8.0) < 1e-12
        assert abs(BERRY_EXPONENT - 0.875) < 1e-10

    def test_weil_coherence(self):
        """Weil formula coherence should be 0.9998."""
        assert abs(WEIL_COHERENCE - 0.9998) < 1e-10

    def test_weil_coherence_near_unity(self):
        """Weil coherence should be close to 1.0 (high quality)."""
        assert WEIL_COHERENCE > 0.999

    def test_gue_matrix_pvalue_extremely_small(self):
        """GUE matrix p-value should be statistically significant (< 0.001)."""
        assert GUE_MATRIX_PVALUE < 0.001


# =============================================================================
# TEST CLASS 4: Constellation Constants in qcal.constants
# =============================================================================

class TestConstellationConstants:
    """Tests for 51-node constellation constants in qcal.constants."""

    def test_n_nodes_equals_51(self):
        """Constellation should have exactly 51 nodes."""
        assert CONSTELLATION_N_NODES == 51

    def test_categories_sum_to_51(self):
        """Category sizes should sum to 51."""
        total = (
            len(CONSTELLATION_CONSTANTS) +
            len(CONSTELLATION_STRINGS) +
            len(FIBONACCI_SEQUENCE) +
            len(CONSTELLATION_PRIMES)
        )
        assert total == 51

    def test_constellation_constants_count(self):
        """Category 1 (mathematical constants) should have 5 nodes."""
        assert len(CONSTELLATION_CONSTANTS) == 5

    def test_constellation_strings_count(self):
        """Category 2 (string harmonics) should have 7 nodes."""
        assert len(CONSTELLATION_STRINGS) == 7

    def test_constellation_strings_values(self):
        """String harmonic nodes should be k/7 for k=1..7."""
        for k, val in enumerate(CONSTELLATION_STRINGS, start=1):
            assert abs(val - k / 7.0) < 1e-12, f"String node {k}: {val} != {k/7}"

    def test_fibonacci_sequence_count(self):
        """Fibonacci temporal nodes should have 10 elements."""
        assert len(FIBONACCI_SEQUENCE) == 10

    def test_fibonacci_sequence_values(self):
        """Fibonacci sequence should be 1,1,2,3,5,8,13,21,34,55."""
        expected = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
        assert FIBONACCI_SEQUENCE == expected

    def test_fibonacci_f10_equals_55(self):
        """F(10) = 55 (last Fibonacci node)."""
        assert FIBONACCI_SEQUENCE[-1] == 55

    def test_fibonacci_epoch_year(self):
        """Fibonacci epoch should be approximately 2025.08."""
        assert abs(FIBONACCI_EPOCH_YEAR - 2025.08) < 0.1

    def test_fibonacci_epoch_years(self):
        """Fibonacci cycle should be 55.08 years."""
        assert abs(FIBONACCI_EPOCH_YEARS - 55.08) < 0.01

    def test_constellation_primes_count(self):
        """Category 4 (primes) should have 29 nodes."""
        assert len(CONSTELLATION_PRIMES) == 29

    def test_constellation_primes_all_prime(self):
        """All constellation prime nodes should actually be prime."""
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(n**0.5) + 1):
                if n % i == 0:
                    return False
            return True
        for p in CONSTELLATION_PRIMES:
            assert is_prime(p), f"{p} is not prime"

    def test_constellation_frequency_equals_F0(self):
        """Constellation resonance frequency should equal F0."""
        assert CONSTELLATION_FREQUENCY == F0

    def test_doi_rh_conditional_defined(self):
        """DOI for conditional RH proof should be defined."""
        assert DOI_RH_CONDITIONAL
        assert "zenodo" in DOI_RH_CONDITIONAL

    def test_doi_rh_final_defined(self):
        """DOI for final RH proof (Coronación) should be defined."""
        assert DOI_RH_FINAL
        assert "zenodo" in DOI_RH_FINAL


# =============================================================================
# TEST CLASS 5: Constellation Operator
# =============================================================================

class TestConstellationOperator:
    """Tests for the constelacion_51_nodos.py operator."""

    def test_build_constellation_returns_51_nodes(self):
        """build_constellation() should return exactly 51 nodes."""
        nodes = build_constellation()
        assert len(nodes) == 51

    def test_build_constellation_node_type(self):
        """All elements should be ConstellationNode instances."""
        nodes = build_constellation()
        for n in nodes:
            assert isinstance(n, ConstellationNode)

    def test_build_constellation_indices_sequential(self):
        """Node indices should be 0, 1, 2, ..., 50."""
        nodes = build_constellation()
        for i, n in enumerate(nodes):
            assert n.index == i

    def test_build_constellation_categories(self):
        """Nodes should be distributed across 4 categories."""
        nodes = build_constellation()
        cats = [n.category for n in nodes]
        assert cats.count('constants') == 5
        assert cats.count('strings') == 7
        assert cats.count('fibonacci') == 10
        assert cats.count('primes') == 29

    def test_build_constellation_coherences_positive(self):
        """All node coherences should be positive."""
        nodes = build_constellation()
        for n in nodes:
            assert n.coherence > 0.0, f"Node {n.name} has non-positive coherence"

    def test_build_constellation_coherences_at_most_one(self):
        """All node coherences should be ≤ 1.0."""
        nodes = build_constellation()
        for n in nodes:
            assert n.coherence <= 1.0, f"Node {n.name} has coherence > 1: {n.coherence}"

    def test_build_constellation_frequencies_positive(self):
        """Node frequencies should be positive (except ∞ node which uses f₀)."""
        nodes = build_constellation()
        for n in nodes:
            assert n.frequency > 0.0, f"Node {n.name} has non-positive frequency"

    def test_compute_psi_returns_valid_range(self):
        """Ψ should be in (0, 1]."""
        nodes = build_constellation()
        psi, harmonic_mean, mean_coh = compute_constellation_psi(nodes)
        assert 0.0 < psi <= 1.0, f"Psi out of range: {psi}"

    def test_compute_psi_is_cube_root_of_harmonic_mean(self):
        """Ψ = ∛H where H is the harmonic mean."""
        nodes = build_constellation()
        psi, harmonic_mean, _ = compute_constellation_psi(nodes)
        expected_psi = harmonic_mean ** (1.0 / 3.0)
        assert abs(psi - expected_psi) < 1e-12

    def test_validate_constellation_result_type(self):
        """validate_constellation() should return ConstellationResult."""
        result = validate_constellation()
        assert isinstance(result, ConstellationResult)

    def test_validate_constellation_n_nodes(self):
        """Validated constellation should have exactly 51 nodes."""
        result = validate_constellation()
        assert result.n_nodes == 51

    def test_validate_constellation_psi_above_0_95(self):
        """Trinity Ψ should be ≥ 0.95 (high coherence)."""
        result = validate_constellation()
        assert result.psi >= 0.95, f"Psi = {result.psi:.6f} < 0.95"

    def test_validate_constellation_is_valid(self):
        """Constellation should be marked as valid."""
        result = validate_constellation()
        assert result.is_valid, f"Constellation invalid: Psi = {result.psi:.6f}"

    def test_validate_constellation_fibonacci_epoch(self):
        """Fibonacci epoch should be approximately 2025.08."""
        result = validate_constellation()
        assert abs(result.fibonacci_epoch - 2025.08) < 0.1

    def test_validate_constellation_fibonacci_years(self):
        """Fibonacci cycle should be 55.08 years."""
        result = validate_constellation()
        assert abs(result.fibonacci_years - 55.08) < 0.01

    def test_validate_constellation_resonance_frequency(self):
        """Resonance frequency should equal F0."""
        result = validate_constellation()
        assert result.resonance_frequency == F0

    def test_validate_constellation_weil_coherence(self):
        """Weil coherence stored in result should be 0.9998."""
        result = validate_constellation()
        assert abs(result.weil_coherence - 0.9998) < 1e-10

    def test_validate_constellation_berry_exponent(self):
        """Berry exponent should be 7/8."""
        result = validate_constellation()
        assert abs(result.berry_exponent - 0.875) < 1e-12

    def test_get_node_by_category_constants(self):
        """get_node_by_category('constants') should return 5 nodes."""
        result = validate_constellation()
        constants_nodes = get_node_by_category(result, 'constants')
        assert len(constants_nodes) == 5

    def test_get_node_by_category_primes(self):
        """get_node_by_category('primes') should return 29 nodes."""
        result = validate_constellation()
        prime_nodes = get_node_by_category(result, 'primes')
        assert len(prime_nodes) == 29

    def test_constellation_summary_n_nodes(self):
        """Summary should report 51 nodes."""
        result = validate_constellation()
        summary = constellation_summary(result)
        assert summary['n_nodes'] == 51

    def test_constellation_summary_psi_positive(self):
        """Summary Ψ should be positive."""
        result = validate_constellation()
        summary = constellation_summary(result)
        assert summary['psi'] > 0.0

    def test_constellation_summary_is_valid(self):
        """Summary should report is_valid=True."""
        result = validate_constellation()
        summary = constellation_summary(result)
        assert summary['is_valid']

    def test_constellation_summary_categories_present(self):
        """Summary should include all 4 category breakdowns."""
        result = validate_constellation()
        summary = constellation_summary(result)
        for cat in ('constants', 'strings', 'fibonacci', 'primes'):
            assert cat in summary['categories'], f"Missing category: {cat}"

    def test_constellation_verbose_runs_without_error(self):
        """validate_constellation(verbose=True) should run without errors."""
        try:
            import io
            import contextlib
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                result = validate_constellation(verbose=True)
            assert result.n_nodes == 51
        except Exception as e:
            pytest.fail(f"verbose validation raised: {e}")

    def test_n_nodes_constant(self):
        """Module constant N_NODES should equal 51."""
        assert N_NODES == 51


# =============================================================================
# TEST CLASS 6: Integration — constants + operator consistency
# =============================================================================

class TestIntegration:
    """Integration tests: qcal.constants and constellation operator agree."""

    def test_constellation_frequency_matches_F0(self):
        """Constellation frequency from both sources should match."""
        result = validate_constellation()
        assert result.resonance_frequency == F0

    def test_E0_lambda_consistency(self):
        """E₀·λ₀ = h·c (de Broglie relation for photons)."""
        # E₀ = h·f₀, λ₀ = c/f₀ → E₀·λ₀ = h·c
        hc = PLANCK_CONSTANT * SPEED_OF_LIGHT
        product = E0_PHOTON * LAMBDA_WAVE
        assert abs(product - hc) / hc < 1e-9

    def test_gue_n_sq_is_19_squared(self):
        """GUE_MATRIX_N_SQ should be 19×19 = 361."""
        assert GUE_MATRIX_N_SQ == 19 * 19

    def test_fibonacci_sum_near_141(self):
        """Sum of first 10 Fibonacci numbers is 143 (close to 141.7001)."""
        # 1+1+2+3+5+8+13+21+34+55 = 143 ≈ 141.7001
        fib_sum = sum(FIBONACCI_SEQUENCE)
        assert abs(fib_sum - 143) < 1e-10, f"Fibonacci sum = {fib_sum}"
        # Close to f₀ (within 1%): confirms deep connection
        assert abs(fib_sum - F0) / F0 < 0.01, f"Fib sum vs f₀: {fib_sum} vs {F0}"
