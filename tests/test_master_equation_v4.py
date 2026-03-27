#!/usr/bin/env python3
"""
Tests for Universal Master Equation v4.0

Validates the derivation of the QCAL substrate frequency from first principles:

    f₀ = (c / (2π √(λ_p · L_Λ))) · (α · Φ / (D · N₇)) · Γ_eff

Tests cover:
- Physical constants used in the derivation
- Formula output falls in the expected range (~141 700 Hz)
- Γ_eff (1.4% effective mass correction) interpretation
- IRS-Luna experiment design parameters
- Full derivation report

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from utils.master_equation_v4 import (
    compute_master_equation,
    irs_luna_parameters,
    run_master_equation_derivation,
    MasterEquationResult,
    SPEED_OF_LIGHT,
    PROTON_COMPTON_WAVELENGTH,
    FINE_STRUCTURE_CONSTANT,
    COSMOLOGICAL_CONSTANT,
    L_LAMBDA,
    TOPO_PHI_RING,
    TOPO_N7,
    TOPO_D,
    GAMMA_EFF,
    GAMMA_EFF_DEVIATION,
    XI_COOPERATIVITY,
    BIREFRINGENCE_IRS_LUNA,
)


# ---------------------------------------------------------------------------
# Physical constants
# ---------------------------------------------------------------------------

class TestPhysicalConstants:
    """Verify the physical constants used in the Master Equation v4.0."""

    def test_speed_of_light(self):
        assert SPEED_OF_LIGHT == 299_792_458.0

    def test_proton_compton_wavelength_order(self):
        """λ_p should be ~2.10×10⁻¹⁶ m."""
        assert 2.0e-16 < PROTON_COMPTON_WAVELENGTH < 2.2e-16

    def test_fine_structure_constant(self):
        """α ≈ 1/137.036."""
        assert abs(FINE_STRUCTURE_CONSTANT - 1.0 / 137.036) < 1e-6

    def test_cosmological_constant_order(self):
        """Λ should be ~10⁻⁵² m⁻²."""
        assert 1e-53 < COSMOLOGICAL_CONSTANT < 1e-51

    def test_l_lambda_order(self):
        """L_Λ = Λ^(-1/4) should be ~9.76×10¹² m."""
        assert 9.0e12 < L_LAMBDA < 1.1e13

    def test_l_lambda_relation_to_cosmological_constant(self):
        """L_Λ should satisfy L_Λ⁴ = 1/Λ."""
        assert abs(L_LAMBDA ** 4 * COSMOLOGICAL_CONSTANT - 1.0) < 1e-6

    def test_topo_phi_ring(self):
        """Φ = π/8."""
        assert abs(TOPO_PHI_RING - np.pi / 8.0) < 1e-12

    def test_topo_n7(self):
        assert TOPO_N7 == 7

    def test_topo_d(self):
        assert TOPO_D == 3

    def test_gamma_eff_value(self):
        """Γ_eff = 0.986 (1.4% correction)."""
        assert abs(GAMMA_EFF - 0.986) < 1e-9

    def test_gamma_eff_deviation(self):
        """Deviation = 1 - Γ_eff = 0.014."""
        assert abs(GAMMA_EFF_DEVIATION - 0.014) < 1e-9

    def test_xi_cooperativity(self):
        assert abs(XI_COOPERATIVITY - 0.053) < 1e-9

    def test_birefringence_order(self):
        """Birefringence signal should be 10⁻¹⁹ rad."""
        assert abs(BIREFRINGENCE_IRS_LUNA - 1.0e-19) < 1e-30


# ---------------------------------------------------------------------------
# Core formula computation
# ---------------------------------------------------------------------------

class TestMasterEquationComputation:
    """Test the master equation computation."""

    def test_returns_result_type(self):
        result = compute_master_equation()
        assert isinstance(result, MasterEquationResult)

    def test_f0_substrate_in_expected_range(self):
        """f₀ substrate should be approximately 141 700 Hz (±5%)."""
        result = compute_master_equation()
        assert 1.34e5 < result.f0_substrate < 1.49e5

    def test_f0_close_to_target(self):
        """f₀ should be within 5% of 141 700.1 Hz."""
        result = compute_master_equation()
        rel_error = abs(result.f0_substrate - 141_700.1) / 141_700.1
        assert rel_error < 0.05

    def test_prefactor_positive(self):
        result = compute_master_equation()
        assert result.prefactor > 0

    def test_coupling_positive(self):
        result = compute_master_equation()
        assert result.coupling > 0

    def test_f0_ideal_greater_than_f0_substrate(self):
        """Ideal f₀ (Γ_eff=1) must exceed the corrected f₀ (Γ_eff<1)."""
        result = compute_master_equation()
        assert result.f0_ideal > result.f0_substrate

    def test_gamma_eff_correction_size(self):
        """The 1.4% correction should reduce f₀ by approximately 1.4%."""
        result = compute_master_equation()
        ratio = result.f0_substrate / result.f0_ideal
        assert abs(ratio - GAMMA_EFF) < 1e-9

    def test_validation_passes(self):
        result = compute_master_equation()
        assert result.is_validated

    def test_validation_details_keys(self):
        result = compute_master_equation()
        for key in ("f0_expected_hz", "f0_computed_hz", "relative_error",
                    "passed", "gamma_eff_applied", "dark_matter_signature_pct"):
            assert key in result.validation_details

    def test_dark_matter_signature_percentage(self):
        """Dark matter signature should report 1.4%."""
        result = compute_master_equation()
        assert abs(result.validation_details["dark_matter_signature_pct"] - 1.4) < 1e-6

    def test_invalid_lambda_p_raises(self):
        with pytest.raises(ValueError):
            compute_master_equation(lambda_p=0)

    def test_invalid_l_lambda_raises(self):
        with pytest.raises(ValueError):
            compute_master_equation(l_lambda=-1.0)

    def test_invalid_d_raises(self):
        with pytest.raises(ValueError):
            compute_master_equation(d=0)


# ---------------------------------------------------------------------------
# Γ_eff physical interpretation
# ---------------------------------------------------------------------------

class TestGammaEffInterpretation:
    """Test the physical interpretation of Γ_eff."""

    def test_unit_gamma_gives_higher_frequency(self):
        """With Γ_eff = 1 the 'static crystal' frequency is higher."""
        result_crystal = compute_master_equation(gamma_eff=1.0)
        result_fluid = compute_master_equation(gamma_eff=GAMMA_EFF)
        assert result_crystal.f0_substrate > result_fluid.f0_substrate

    def test_gamma_eff_deviation_is_lyman_alpha_signature(self):
        """The 1.4% deviation encodes the Lyman-α / dark-matter signal."""
        result = compute_master_equation()
        assert abs(result.gamma_eff_deviation - 0.014) < 1e-9

    def test_frequency_scales_linearly_with_gamma_eff(self):
        """f₀ should scale linearly with Γ_eff."""
        r1 = compute_master_equation(gamma_eff=0.9)
        r2 = compute_master_equation(gamma_eff=1.8)
        # Ratio of frequencies should equal ratio of Γ_eff values
        assert abs(r2.f0_substrate / r1.f0_substrate - 1.8 / 0.9) < 1e-9


# ---------------------------------------------------------------------------
# IRS-Luna experiment parameters
# ---------------------------------------------------------------------------

class TestIRSLunaParameters:
    """Test the IRS-Luna experiment parameter derivation."""

    def test_returns_dict(self):
        params = irs_luna_parameters()
        assert isinstance(params, dict)

    def test_tuning_hz_positive(self):
        params = irs_luna_parameters()
        assert params["tuning_hz"] > 0

    def test_xi_cooperativity_value(self):
        params = irs_luna_parameters()
        assert abs(params["xi_cooperativity"] - 0.053) < 1e-9

    def test_birefringence_order(self):
        params = irs_luna_parameters()
        assert abs(params["birefringence_rad"] - 1.0e-19) < 1e-30

    def test_expected_flux_modulation(self):
        """Expected ±1.4% modulation confirms the condensate."""
        params = irs_luna_parameters()
        assert abs(params["expected_flux_modulation_pct"] - 1.4) < 1e-6

    def test_confirmation_criterion_present(self):
        params = irs_luna_parameters()
        assert "confirmation_criterion" in params
        assert "1.4%" in params["confirmation_criterion"]

    def test_accepts_precomputed_result(self):
        result = compute_master_equation()
        params = irs_luna_parameters(result)
        assert params["tuning_hz"] == result.f0_substrate


# ---------------------------------------------------------------------------
# Full derivation report
# ---------------------------------------------------------------------------

class TestFullDerivation:
    """Test the complete derivation and report function."""

    def test_run_derivation_returns_dict(self):
        report = run_master_equation_derivation(verbose=False)
        assert isinstance(report, dict)

    def test_report_keys(self):
        report = run_master_equation_derivation(verbose=False)
        assert "master_equation" in report
        assert "irs_luna" in report

    def test_master_equation_is_validated(self):
        report = run_master_equation_derivation(verbose=False)
        assert report["master_equation"].is_validated

    def test_irs_luna_tuning_matches_f0(self):
        report = run_master_equation_derivation(verbose=False)
        me = report["master_equation"]
        irs = report["irs_luna"]
        assert me.f0_substrate == irs["tuning_hz"]


# ---------------------------------------------------------------------------
# Integration: constants module cross-check
# ---------------------------------------------------------------------------

class TestConstantsIntegration:
    """Verify integration with qcal.constants."""

    def test_f0_substrate_from_constants_matches_formula(self):
        """F0_SUBSTRATE in qcal.constants should match formula evaluation."""
        try:
            from qcal.constants import F0_SUBSTRATE
        except ImportError:
            pytest.skip("qcal.constants not available")

        result = compute_master_equation()
        assert abs(F0_SUBSTRATE - result.f0_substrate) < 1.0  # within 1 Hz


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
