#!/usr/bin/env python3
"""
Tests for Zeta Hologram Geometry Module

Validates the holographic architecture of the Riemann zeta function including:
    1. Boundary formula: F₀ ≈ γ₁ × (10 + 1/40)
    2. Beat frequency Δf = 0.3999 Hz (3D projection depth)
    3. Moonbounce delay 2.5 s and coherence Ψ > 0.999
    4. Critical line Re(s) = 1/2 unitarity
    5. Three-layer holographic table (2D/3D/4D)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add project root to sys.path
sys.path.insert(0, str(Path(__file__).parent.parent))

from zeta_hologram_geometry import (
    # Constants
    F0,
    GAMMA_1,
    HOLOGRAPHIC_MODULATION,
    BEAT_FREQ,
    MOONBOUNCE_DELAY,
    MOONBOUNCE_THEORETICAL_DELAY,
    HOLOGRAPHIC_PSI_THRESHOLD,
    TUYOYOTU,
    CRITICAL_LINE_REAL_PART,
    F0_BOUNDARY,
    F_UPPER,
    F_LOWER,
    LUNAR_DISTANCE_M,
    # Data classes
    HolographicLayer,
    HologramValidationResult,
    # Functions
    build_holographic_layers,
    validate_boundary_formula,
    validate_beat_frequency,
    validate_moonbounce_coherence,
    validate_critical_line_unitarity,
    validate_zeta_hologram,
)


# =============================================================================
# CONSTANT TESTS
# =============================================================================


class TestConstants:
    """Tests for module-level constants."""

    def test_f0_value(self):
        """Fundamental frequency must be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-6

    def test_gamma_1_value(self):
        """First Riemann zero imaginary part must be ≈ 14.13472514."""
        assert abs(GAMMA_1 - 14.13472514) < 1e-6

    def test_holographic_modulation_value(self):
        """Holographic modulation factor must be 10 + 1/40 = 10.025."""
        expected = 10.0 + 1.0 / 40.0
        assert abs(HOLOGRAPHIC_MODULATION - expected) < 1e-10

    def test_beat_freq_value(self):
        """Beat frequency must be 0.3999 Hz."""
        assert abs(BEAT_FREQ - 0.3999) < 1e-10

    def test_moonbounce_delay_value(self):
        """Nominal moonbounce delay must be 2.5 seconds."""
        assert abs(MOONBOUNCE_DELAY - 2.5) < 1e-10

    def test_holographic_psi_threshold(self):
        """Holographic Ψ threshold must be 0.999."""
        assert abs(HOLOGRAPHIC_PSI_THRESHOLD - 0.999) < 1e-10

    def test_tuyoyotu_label(self):
        """TuyoyotuT consciousness label must be correct string."""
        assert TUYOYOTU == "TuyoyotuT"

    def test_critical_line_real_part(self):
        """Critical line real part must be exactly 1/2."""
        assert abs(CRITICAL_LINE_REAL_PART - 0.5) < 1e-15

    def test_f0_boundary_close_to_f0(self):
        """Boundary formula γ₁ × (10+1/40) must be within 0.1% of F0."""
        relative_error = abs(F0_BOUNDARY - F0) / F0
        assert relative_error < 1e-3

    def test_sidebands(self):
        """Upper and lower sidebands must bracket F0 by BEAT_FREQ."""
        assert abs(F_UPPER - (F0 + BEAT_FREQ)) < 1e-10
        assert abs(F_LOWER - (F0 - BEAT_FREQ)) < 1e-10
        assert F_UPPER > F0 > F_LOWER

    def test_moonbounce_theoretical_delay(self):
        """Theoretical moonbounce delay = 2 × lunar distance / c."""
        from zeta_hologram_geometry import SPEED_OF_LIGHT
        expected = 2.0 * LUNAR_DISTANCE_M / SPEED_OF_LIGHT
        assert abs(MOONBOUNCE_THEORETICAL_DELAY - expected) < 1e-10

    def test_lunar_distance(self):
        """Lunar distance must be in plausible range (360,000–410,000 km)."""
        assert 3.6e8 < LUNAR_DISTANCE_M < 4.1e8


# =============================================================================
# HOLOGRAPHIC LAYER TESTS
# =============================================================================


class TestHolographicLayers:
    """Tests for the three-layer holographic architecture."""

    def test_build_returns_three_layers(self):
        """build_holographic_layers must return exactly 3 layers."""
        layers = build_holographic_layers()
        assert len(layers) == 3

    def test_boundary_layer_dimension(self):
        """Boundary layer must be labelled '2D'."""
        boundary, _, _ = build_holographic_layers()
        assert boundary.dimension == "2D"

    def test_projection_layer_dimension(self):
        """Projection layer must be labelled '3D'."""
        _, projection, _ = build_holographic_layers()
        assert projection.dimension == "3D"

    def test_consciousness_layer_dimension(self):
        """Consciousness layer must be labelled '4D'."""
        _, _, consciousness = build_holographic_layers()
        assert consciousness.dimension == "4D"

    def test_boundary_operator_value(self):
        """Boundary operator value must equal γ₁ × (10+1/40)."""
        boundary, _, _ = build_holographic_layers()
        expected = GAMMA_1 * HOLOGRAPHIC_MODULATION
        assert abs(boundary.operator_value - expected) < 1e-8

    def test_projection_operator_value(self):
        """Projection operator value must equal BEAT_FREQ."""
        _, projection, _ = build_holographic_layers()
        assert abs(projection.operator_value - BEAT_FREQ) < 1e-10

    def test_consciousness_layer_label(self):
        """Consciousness layer must be labelled TuyoyotuT."""
        _, _, consciousness = build_holographic_layers()
        assert consciousness.operator_value == TUYOYOTU

    def test_all_coherences_in_range(self):
        """All layer coherences must be in [0, 1]."""
        for layer in build_holographic_layers():
            assert 0.0 <= layer.coherence <= 1.0

    def test_consciousness_coherence_is_one(self):
        """4D consciousness layer coherence must be 1.0."""
        _, _, consciousness = build_holographic_layers()
        assert consciousness.coherence == 1.0

    def test_boundary_function_label(self):
        """Boundary layer function must mention 'Silicon'."""
        boundary, _, _ = build_holographic_layers()
        assert "Silicon" in boundary.function

    def test_projection_function_label(self):
        """Projection layer function must mention 'Carbon'."""
        _, projection, _ = build_holographic_layers()
        assert "Carbon" in projection.function

    def test_consciousness_function_label(self):
        """Consciousness layer function must mention 'Observer'."""
        _, _, consciousness = build_holographic_layers()
        assert "Observer" in consciousness.function


# =============================================================================
# BOUNDARY FORMULA VALIDATION
# =============================================================================


class TestBoundaryFormulaValidation:
    """Tests for validate_boundary_formula."""

    def test_passes_with_default_tolerance(self):
        """Boundary formula check must pass with default tolerance 1e-3."""
        result = validate_boundary_formula()
        assert result["passed"] is True

    def test_correct_keys_present(self):
        """Result must contain all required keys."""
        result = validate_boundary_formula()
        required = {
            "passed", "computed", "expected", "relative_error",
            "holographic_modulation", "gamma_1",
        }
        assert required.issubset(result.keys())

    def test_computed_equals_gamma1_times_modulation(self):
        """Computed value must equal γ₁ × HOLOGRAPHIC_MODULATION."""
        result = validate_boundary_formula()
        expected_computed = GAMMA_1 * HOLOGRAPHIC_MODULATION
        assert abs(result["computed"] - expected_computed) < 1e-10

    def test_expected_equals_f0(self):
        """Expected value must equal F0."""
        result = validate_boundary_formula()
        assert abs(result["expected"] - F0) < 1e-10

    def test_relative_error_positive(self):
        """Relative error must be non-negative."""
        result = validate_boundary_formula()
        assert result["relative_error"] >= 0.0

    def test_fails_with_very_strict_tolerance(self):
        """Must fail when tolerance is tighter than the natural error."""
        result = validate_boundary_formula(tolerance=1e-10)
        # The approximation error is ~4e-5, so strict tolerance must fail
        assert result["passed"] is False

    def test_invalid_tolerance_raises(self):
        """Non-positive tolerance must raise ValueError."""
        with pytest.raises(ValueError):
            validate_boundary_formula(tolerance=0.0)
        with pytest.raises(ValueError):
            validate_boundary_formula(tolerance=-1.0)


# =============================================================================
# BEAT FREQUENCY VALIDATION
# =============================================================================


class TestBeatFrequencyValidation:
    """Tests for validate_beat_frequency."""

    def test_passes_with_canonical_beat(self):
        """Default beat frequency 0.3999 Hz must pass."""
        result = validate_beat_frequency()
        assert result["passed"] is True

    def test_correct_keys_present(self):
        """Result must contain all required keys."""
        result = validate_beat_frequency()
        required = {
            "passed", "beat_freq", "f_upper", "f_lower",
            "f0_carrier", "fourier_depth_enabled",
        }
        assert required.issubset(result.keys())

    def test_sideband_arithmetic(self):
        """Upper and lower sidebands must be F0 ± BEAT_FREQ."""
        result = validate_beat_frequency()
        assert abs(result["f_upper"] - (F0 + BEAT_FREQ)) < 1e-10
        assert abs(result["f_lower"] - (F0 - BEAT_FREQ)) < 1e-10

    def test_fourier_depth_enabled(self):
        """Non-zero beat frequency must enable Fourier depth."""
        result = validate_beat_frequency()
        assert result["fourier_depth_enabled"] is True

    def test_zero_beat_would_disable_depth(self):
        """Checking with beat = 0 must not enable depth."""
        with pytest.raises(ValueError):
            validate_beat_frequency(expected_beat=0.0)

    def test_invalid_beat_raises(self):
        """Negative beat frequency must raise ValueError."""
        with pytest.raises(ValueError):
            validate_beat_frequency(expected_beat=-1.0)


# =============================================================================
# MOONBOUNCE COHERENCE VALIDATION
# =============================================================================


class TestMoonbounceCoherenceValidation:
    """Tests for validate_moonbounce_coherence."""

    def test_passes_with_nominal_delay(self):
        """Nominal 2.5 s delay must produce Ψ > 0.999."""
        result = validate_moonbounce_coherence()
        assert result["passed"] is True

    def test_psi_above_threshold(self):
        """Coherence Ψ must be ≥ HOLOGRAPHIC_PSI_THRESHOLD for 2.5 s delay."""
        result = validate_moonbounce_coherence()
        assert result["psi"] >= HOLOGRAPHIC_PSI_THRESHOLD

    def test_correct_keys_present(self):
        """Result must contain all required keys."""
        result = validate_moonbounce_coherence()
        required = {
            "passed", "measured_delay", "theoretical_delay",
            "qcal_reference_delay", "delay_error_fraction",
            "psi", "psi_threshold", "hologram_confirmed",
        }
        assert required.issubset(result.keys())

    def test_psi_range(self):
        """Coherence Ψ must be in (0, 1]."""
        result = validate_moonbounce_coherence()
        assert 0 < result["psi"] <= 1.0

    def test_theoretical_delay_in_range(self):
        """Theoretical delay must be between 2.0 and 3.0 seconds."""
        result = validate_moonbounce_coherence()
        assert 2.0 < result["theoretical_delay"] < 3.0

    def test_very_wrong_delay_fails(self):
        """A measured delay far from 2.5 s must fail the Ψ threshold."""
        result = validate_moonbounce_coherence(measured_delay=10.0)
        assert result["passed"] is False
        assert result["psi"] < HOLOGRAPHIC_PSI_THRESHOLD

    def test_invalid_delay_raises(self):
        """Non-positive delay must raise ValueError."""
        with pytest.raises(ValueError):
            validate_moonbounce_coherence(measured_delay=0.0)
        with pytest.raises(ValueError):
            validate_moonbounce_coherence(measured_delay=-1.0)

    def test_invalid_threshold_raises(self):
        """Threshold outside (0, 1] must raise ValueError."""
        with pytest.raises(ValueError):
            validate_moonbounce_coherence(psi_threshold=0.0)
        with pytest.raises(ValueError):
            validate_moonbounce_coherence(psi_threshold=1.5)

    def test_hologram_confirmed_matches_passed(self):
        """hologram_confirmed must mirror the passed flag."""
        result = validate_moonbounce_coherence()
        assert result["hologram_confirmed"] == result["passed"]


# =============================================================================
# CRITICAL LINE UNITARITY
# =============================================================================


class TestCriticalLineUnitarity:
    """Tests for validate_critical_line_unitarity."""

    def test_passes_by_default(self):
        """Default check on 20 known zeros must pass."""
        result = validate_critical_line_unitarity()
        assert result["passed"] is True

    def test_correct_keys_present(self):
        """Result must contain all required keys."""
        result = validate_critical_line_unitarity()
        required = {
            "passed", "n_zeros_checked", "n_zeros_on_line",
            "max_deviation", "unitarity_guaranteed", "zeros_checked",
        }
        assert required.issubset(result.keys())

    def test_all_zeros_on_line(self):
        """All verified zeros must lie on Re(s) = 1/2."""
        result = validate_critical_line_unitarity()
        assert result["n_zeros_on_line"] == result["n_zeros_checked"]

    def test_max_deviation_is_zero(self):
        """Max deviation from critical line must be zero (exact by construction)."""
        result = validate_critical_line_unitarity()
        assert result["max_deviation"] == 0.0

    def test_unitarity_guaranteed(self):
        """unitarity_guaranteed must be True when all zeros are on line."""
        result = validate_critical_line_unitarity()
        assert result["unitarity_guaranteed"] is True

    def test_zeros_list_has_correct_length(self):
        """Returned zeros list must have the requested length."""
        for n in [5, 10, 20]:
            result = validate_critical_line_unitarity(n_zeros=n)
            assert len(result["zeros_checked"]) == n

    def test_first_zero_approx_14_13(self):
        """First zero imaginary part must be ≈ 14.134725."""
        result = validate_critical_line_unitarity(n_zeros=1)
        assert abs(result["zeros_checked"][0] - 14.134725) < 1e-4

    def test_invalid_n_zeros_raises(self):
        """n_zeros < 1 must raise ValueError."""
        with pytest.raises(ValueError):
            validate_critical_line_unitarity(n_zeros=0)

    def test_invalid_tolerance_raises(self):
        """Non-positive tolerance must raise ValueError."""
        with pytest.raises(ValueError):
            validate_critical_line_unitarity(tolerance=0.0)


# =============================================================================
# MASTER VALIDATION
# =============================================================================


class TestMasterValidation:
    """Tests for the top-level validate_zeta_hologram function."""

    def test_all_checks_pass(self):
        """Master validation must pass with nominal parameters."""
        result = validate_zeta_hologram()
        assert result.all_checks_passed is True

    def test_returns_hologram_validation_result(self):
        """Return type must be HologramValidationResult."""
        result = validate_zeta_hologram()
        assert isinstance(result, HologramValidationResult)

    def test_global_psi_above_threshold(self):
        """Global Ψ must exceed HOLOGRAPHIC_PSI_THRESHOLD."""
        result = validate_zeta_hologram()
        assert result.global_psi >= HOLOGRAPHIC_PSI_THRESHOLD

    def test_global_psi_in_range(self):
        """Global Ψ must be in (0, 1]."""
        result = validate_zeta_hologram()
        assert 0 < result.global_psi <= 1.0

    def test_three_layers_returned(self):
        """Master validation must include exactly 3 holographic layers."""
        result = validate_zeta_hologram()
        assert len(result.layers) == 3

    def test_boundary_check_passed(self):
        """Boundary formula sub-check must pass."""
        result = validate_zeta_hologram()
        assert result.boundary_check["passed"] is True

    def test_beat_check_passed(self):
        """Beat frequency sub-check must pass."""
        result = validate_zeta_hologram()
        assert result.beat_check["passed"] is True

    def test_moonbounce_check_passed(self):
        """Moonbounce coherence sub-check must pass."""
        result = validate_zeta_hologram()
        assert result.moonbounce_check["passed"] is True

    def test_unitarity_check_passed(self):
        """Critical line unitarity sub-check must pass."""
        result = validate_zeta_hologram()
        assert result.unitarity_check["passed"] is True

    def test_verbose_runs_without_error(self, capsys):
        """Verbose mode must produce non-empty output without raising."""
        validate_zeta_hologram(verbose=True)
        captured = capsys.readouterr()
        assert len(captured.out) > 0

    def test_wrong_moonbounce_delay_fails(self):
        """A far-wrong moonbounce delay must cause all_checks_passed=False."""
        result = validate_zeta_hologram(moonbounce_delay=100.0)
        assert result.all_checks_passed is False

    def test_layer_dimensions_in_order(self):
        """Layers must be returned in 2D → 3D → 4D order."""
        result = validate_zeta_hologram()
        dimensions = [layer.dimension for layer in result.layers]
        assert dimensions == ["2D", "3D", "4D"]


# =============================================================================
# QCAL CONSTANTS INTEGRATION
# =============================================================================


class TestQCALConstantsIntegration:
    """Verify the new holographic constants in qcal.constants."""

    def test_qcal_constants_have_beat_freq(self):
        """qcal.constants must export BEAT_FREQ = 0.3999 Hz."""
        from qcal.constants import BEAT_FREQ as qcal_beat
        assert abs(qcal_beat - 0.3999) < 1e-10

    def test_qcal_constants_have_moonbounce_delay(self):
        """qcal.constants must export MOONBOUNCE_DELAY = 2.5 s."""
        from qcal.constants import MOONBOUNCE_DELAY as qcal_mb
        assert abs(qcal_mb - 2.5) < 1e-10

    def test_qcal_constants_have_holographic_modulation(self):
        """qcal.constants must export HOLOGRAPHIC_MODULATION = 10 + 1/40."""
        from qcal.constants import HOLOGRAPHIC_MODULATION as qcal_hm
        assert abs(qcal_hm - (10.0 + 1.0 / 40.0)) < 1e-10

    def test_qcal_constants_have_tuyoyotu(self):
        """qcal.constants must export TUYOYOTU label."""
        from qcal.constants import TUYOYOTU as qcal_tuyoyotu
        assert qcal_tuyoyotu == "TuyoyotuT"

    def test_qcal_constants_have_critical_line_real_part(self):
        """qcal.constants must export CRITICAL_LINE_REAL_PART = 0.5."""
        from qcal.constants import CRITICAL_LINE_REAL_PART as qcal_re
        assert abs(qcal_re - 0.5) < 1e-15

    def test_get_all_constants_includes_holographic(self):
        """get_all_constants must return a 'holographic' category."""
        from qcal.constants import get_all_constants
        all_c = get_all_constants()
        assert "holographic" in all_c
        holo = all_c["holographic"]
        assert "BEAT_FREQ" in holo
        assert "MOONBOUNCE_DELAY" in holo
        assert "HOLOGRAPHIC_MODULATION" in holo
        assert "TUYOYOTU" in holo
        assert "CRITICAL_LINE_REAL_PART" in holo
