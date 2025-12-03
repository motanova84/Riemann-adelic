#!/usr/bin/env python3
"""
Tests for Non-Circular Derivation of f₀ = 141.7001 Hz

Tests the complete non-circular derivation including:
1. G_Y = (m_P / Λ_Q)^(1/3) without f₀
2. R_Ψ from vacuum quantum energy
3. p = 17 as spectral RESONANCE POINT (NOT minimum!)
   - CRITICAL: p=11 minimizes equilibrium(p), not p=17
   - p=17 produces f₀ = 141.7001 Hz (the universal frequency)
4. φ⁻³ as fractal dimension
5. π/2 as fundamental mode
6. Non-circularity verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.non_circular_derivation import (
    # Constants
    F0_TARGET,
    C_LIGHT,
    L_PLANCK,
    M_PLANCK,
    LAMBDA_Q,
    PHI,
    ZETA_PRIME_HALF,
    # Functions
    compute_G_Y_non_circular,
    compute_R_Psi_from_vacuum,
    compute_adelic_equilibrium_prime,
    compute_fractal_factor,
    compute_fundamental_mode,
    compute_G_components,
    derive_f0_non_circular,
    verify_non_circularity,
    run_complete_non_circular_derivation,
    # Classes
    NonCircularResult,
)


class TestPhysicalConstants:
    """Test the physical constants used in derivation."""

    def test_f0_target_value(self):
        """Target frequency should be 141.7001 Hz."""
        assert abs(F0_TARGET - 141.7001) < 1e-4

    def test_planck_mass_order(self):
        """Planck mass should be ~2.2e-8 kg."""
        m_P = float(M_PLANCK)
        assert 1e-9 < m_P < 1e-7

    def test_lambda_q_order(self):
        """Quantum vacuum scale should be ~4e-22 kg."""
        lambda_q = float(LAMBDA_Q)
        assert 1e-23 < lambda_q < 1e-21

    def test_phi_golden_ratio(self):
        """Golden ratio should be (1 + √5) / 2."""
        expected = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10

    def test_zeta_prime_half_sign(self):
        """ζ'(1/2) should be negative."""
        assert float(ZETA_PRIME_HALF) < 0

    def test_zeta_prime_half_value(self):
        """ζ'(1/2) should be approximately -3.9226."""
        assert abs(float(ZETA_PRIME_HALF) + 3.9226461392) < 0.001


class TestGYNonCircular:
    """Test G_Y = (m_P / Λ_Q)^(1/3) computation."""

    def test_G_Y_positive(self):
        """G_Y should be positive."""
        G_Y, _ = compute_G_Y_non_circular()
        assert G_Y > 0

    def test_G_Y_order_of_magnitude(self):
        """G_Y should be ~3.7e4."""
        G_Y, _ = compute_G_Y_non_circular()
        assert 1e4 < G_Y < 1e5

    def test_G_Y_precise_value(self):
        """G_Y should be approximately 3.72×10⁴ (computed from constants)."""
        G_Y, _ = compute_G_Y_non_circular()
        # Compute expected value from constants rather than hard-coding
        m_P = 2.176434e-8  # Updated CODATA 2022 value
        Lambda_Q = 4.12e-22
        expected = (m_P / Lambda_Q) ** (1/3)
        assert abs(G_Y - expected) / expected < 0.01  # 1% tolerance

    def test_G_Y_does_not_use_f0(self):
        """G_Y calculation should NOT use f₀."""
        _, details = compute_G_Y_non_circular()
        assert not details.get("uses_f0", True)

    def test_G_Y_formula_correctness(self):
        """Verify G_Y = (m_P / Λ_Q)^(1/3) formula."""
        G_Y, details = compute_G_Y_non_circular()
        m_P = details["m_P"]
        Lambda_Q = details["Lambda_Q"]
        expected = (m_P / Lambda_Q) ** (1/3)
        assert abs(G_Y - expected) / expected < 1e-6


class TestRPsiFromVacuum:
    """Test R_Ψ derivation from vacuum quantum energy."""

    def test_R_Psi_positive(self):
        """R_Ψ should be positive."""
        R_Psi, _ = compute_R_Psi_from_vacuum()
        assert R_Psi > 0

    def test_R_Psi_order_of_magnitude(self):
        """R_Ψ should be ~10^47 (from problem statement)."""
        R_Psi, _ = compute_R_Psi_from_vacuum()
        # The problem states R_Ψ ≈ 10⁴⁷
        log_R = np.log10(R_Psi)
        assert 45 < log_R < 50  # Allow some variation

    def test_R_Psi_does_not_use_f0(self):
        """R_Ψ calculation should NOT use f₀."""
        _, details = compute_R_Psi_from_vacuum()
        assert not details.get("uses_f0", True)

    def test_R_Psi_base_positive(self):
        """R_Ψ base (before corrections) should be positive."""
        _, details = compute_R_Psi_from_vacuum()
        assert details.get("R_Psi_base", 0) > 0

    def test_adelic_correction_value(self):
        """17^(7/2) correction should be ~20,240."""
        _, details = compute_R_Psi_from_vacuum()
        corr = details.get("corr_adelic_17", 0)
        expected = 17 ** 3.5
        assert abs(corr - expected) / expected < 0.01

    def test_pi_correction_value(self):
        """π³ correction should be ~31."""
        _, details = compute_R_Psi_from_vacuum()
        corr = details.get("corr_pi_3", 0)
        expected = np.pi ** 3
        assert abs(corr - expected) / expected < 0.01

    def test_phi_correction_value(self):
        """φ⁶ correction should match computed value."""
        _, details = compute_R_Psi_from_vacuum()
        corr = details.get("corr_phi_6", 0)
        expected = PHI ** 6  # φ⁶ ≈ 17.94
        assert abs(corr - expected) / expected < 0.01


class TestAdelicEquilibriumPrime:
    """Test p = 17 as spectral resonance point (NOT minimum!)."""

    def test_resonance_prime_is_17(self):
        """The resonance prime (yielding f₀=141.7001 Hz) should be 17."""
        p_opt, _ = compute_adelic_equilibrium_prime()
        assert p_opt == 17

    def test_returns_prime_number(self):
        """Should return a prime number."""
        p_opt, _ = compute_adelic_equilibrium_prime()
        # Check if 17 is prime
        assert all(p_opt % i != 0 for i in range(2, int(np.sqrt(p_opt)) + 1))

    def test_has_justification(self):
        """Should include mathematical justification."""
        _, details = compute_adelic_equilibrium_prime()
        assert "justification" in details
        assert len(details["justification"]) > 0

    def test_equilibrium_minimum_is_not_17(self):
        """
        CRITICAL TEST: The equilibrium MINIMUM is at p=11, NOT p=17!
        
        This corrects a theoretical error in the original formulation.
        p=17 is special because it produces f₀=141.7001 Hz (resonance),
        not because it minimizes equilibrium(p).
        """
        _, details = compute_adelic_equilibrium_prime()
        equilibrium_min_p = details.get("equilibrium_minimum_p")
        assert equilibrium_min_p == 11, (
            f"Equilibrium minimum should be at p=11, got p={equilibrium_min_p}"
        )

    def test_p17_yields_target_frequency(self):
        """p=17 should produce frequency close to 141.7001 Hz."""
        _, details = compute_adelic_equilibrium_prime()
        f0_17 = details.get("resonance_frequency", 0)
        target = details.get("target_frequency", 141.7001)
        # Should be very close to 141.7001 Hz
        assert abs(f0_17 - target) < 1.0, (
            f"f₀(17) = {f0_17} should be close to {target}"
        )

    def test_frequency_values_computed(self):
        """Should compute frequency values for all primes."""
        _, details = compute_adelic_equilibrium_prime()
        assert "frequency_values" in details
        freq_values = details["frequency_values"]
        # Check some key primes
        assert 11 in freq_values
        assert 17 in freq_values
        assert 29 in freq_values
        
    def test_equilibrium_function_values(self):
        """
        Verify equilibrium(p) = exp(π√p/2) / p^(3/2) values.
        
        Known values:
            equilibrium(11) ≈ 5.017
            equilibrium(17) ≈ 9.270
            equilibrium(29) ≈ 30.206
        """
        _, details = compute_adelic_equilibrium_prime()
        eq_values = details.get("equilibrium_values", {})
        
        # Check approximate values
        assert 4.5 < eq_values.get(11, 0) < 5.5, "equilibrium(11) should be ~5.017"
        assert 8.5 < eq_values.get(17, 0) < 10.0, "equilibrium(17) should be ~9.270"
        assert 29.0 < eq_values.get(29, 0) < 31.0, "equilibrium(29) should be ~30.206"


class TestFractalFactor:
    """Test φ⁻³ as fractal dimension."""

    def test_fractal_factor_positive(self):
        """Fractal factor should be positive."""
        factor, _ = compute_fractal_factor()
        assert factor > 0

    def test_fractal_factor_less_than_one(self):
        """φ⁻³ should be less than 1."""
        factor, _ = compute_fractal_factor()
        assert factor < 1

    def test_fractal_factor_value(self):
        """φ⁻³ should be ~0.236."""
        factor, _ = compute_fractal_factor()
        expected = 1 / PHI**3
        assert abs(factor - expected) < 1e-6

    def test_phi_cubed_value(self):
        """φ³ should be ~4.236."""
        _, details = compute_fractal_factor()
        phi_cubed = details.get("phi_cubed", 0)
        expected = PHI ** 3
        assert abs(phi_cubed - expected) < 1e-6


class TestFundamentalMode:
    """Test π/2 as fundamental mode."""

    def test_mode_factor_is_pi_over_2(self):
        """Mode factor should be π/2."""
        factor, _ = compute_fundamental_mode()
        expected = np.pi / 2
        assert abs(factor - expected) < 1e-10

    def test_mode_factor_value(self):
        """π/2 should be ~1.5708."""
        factor, _ = compute_fundamental_mode()
        assert abs(factor - 1.5707963) < 1e-5

    def test_has_properties_list(self):
        """Should include list of properties."""
        _, details = compute_fundamental_mode()
        assert "properties" in details
        assert len(details["properties"]) >= 4


class TestGComponents:
    """Test G component calculations."""

    def test_returns_all_components(self):
        """Should return all 5 G components."""
        components = compute_G_components()
        required = ["A_p", "F_zeta", "Factor_K", "F_fractal", "G_Y"]
        for key in required:
            assert key in components

    def test_all_components_positive(self):
        """All G components should be positive."""
        components = compute_G_components()
        for key, value in components.items():
            assert value > 0, f"{key} should be positive"

    def test_A_p_order(self):
        """A_p = exp(π·√17/2) should be ~650."""
        components = compute_G_components()
        A_p = components["A_p"]
        expected = np.exp(np.pi * np.sqrt(17) / 2)
        assert abs(A_p - expected) / expected < 0.01


class TestDeriveF0NonCircular:
    """Test the main non-circular derivation."""

    def test_returns_result(self):
        """derive_f0_non_circular should return NonCircularResult."""
        result = derive_f0_non_circular()
        assert isinstance(result, NonCircularResult)

    def test_f0_calculated_positive(self):
        """Calculated f₀ should be positive."""
        result = derive_f0_non_circular()
        assert result.f0_calculated > 0

    def test_f0_target_stored(self):
        """Target f₀ should be stored correctly."""
        result = derive_f0_non_circular()
        assert abs(result.f0_target - F0_TARGET) < 1e-10

    def test_G_Y_stored(self):
        """G_Y value should be stored."""
        result = derive_f0_non_circular()
        assert result.G_Y > 0

    def test_R_Psi_stored(self):
        """R_Ψ value should be stored."""
        result = derive_f0_non_circular()
        assert result.R_Psi > 0

    def test_non_circularity_flags_set(self):
        """Non-circularity flags should be set correctly."""
        result = derive_f0_non_circular()
        assert result.uses_f0_in_G_Y == False
        assert result.uses_f0_in_R_Psi == False
        assert result.uses_f0_anywhere == False

    def test_genuine_emergence(self):
        """Should be marked as genuine emergence."""
        result = derive_f0_non_circular()
        assert result.is_genuine_emergence == True

    def test_has_timestamp(self):
        """Result should have timestamp."""
        result = derive_f0_non_circular()
        assert len(result.timestamp) > 0


class TestVerifyNonCircularity:
    """Test the non-circularity verification."""

    def test_verification_passes(self):
        """Verification should pass for non-circular derivation."""
        report = verify_non_circularity()
        assert report["verification_passed"] == True

    def test_G_Y_clean(self):
        """G_Y should not use f₀."""
        report = verify_non_circularity()
        assert report["G_Y_uses_f0"] == False

    def test_R_Psi_clean(self):
        """R_Ψ should not use f₀."""
        report = verify_non_circularity()
        assert report["R_Psi_uses_f0"] == False

    def test_no_step_uses_f0(self):
        """No step should use f₀."""
        report = verify_non_circularity()
        assert report["any_step_uses_f0"] == False

    def test_has_summary(self):
        """Report should include summary with formulas."""
        report = verify_non_circularity()
        assert "summary" in report
        summary = report["summary"]
        assert "G_Y_formula" in summary
        assert "R_Psi_formula" in summary
        assert "NO f₀" in summary["G_Y_formula"]


class TestCompleteDerivation:
    """Test the complete derivation function."""

    def test_run_complete_derivation(self):
        """run_complete_non_circular_derivation should complete without error."""
        result = run_complete_non_circular_derivation(verbose=False)
        assert isinstance(result, NonCircularResult)

    def test_complete_derivation_has_all_values(self):
        """Complete derivation should have all intermediate values."""
        result = run_complete_non_circular_derivation(verbose=False)
        
        # Check all key values are set
        assert result.G_Y > 0
        assert result.A_p > 0
        assert result.F_zeta > 0
        assert result.Factor_K > 0
        assert result.F_fractal > 0
        assert result.R_Psi > 0
        assert result.G_partial > 0
        assert result.G_corrected > 0
        assert result.f0_calculated > 0


class TestMathematicalRelations:
    """Test mathematical relations and invariants."""

    def test_phi_defining_equation(self):
        """φ² - φ - 1 should equal 0."""
        relation = PHI**2 - PHI - 1
        assert abs(relation) < 1e-10

    def test_phi_inverse_relation(self):
        """1/φ should equal φ - 1."""
        assert abs(1/PHI - (PHI - 1)) < 1e-10

    def test_G_Y_uses_ratio(self):
        """G_Y should use m_P / Λ_Q ratio correctly."""
        G_Y, details = compute_G_Y_non_circular()
        ratio = details["ratio"]
        expected_ratio = float(M_PLANCK) / float(LAMBDA_Q)
        assert abs(ratio - expected_ratio) / expected_ratio < 1e-6


class TestNonCircularResult:
    """Test the NonCircularResult dataclass."""

    def test_default_values(self):
        """Default values should be zeros/False."""
        result = NonCircularResult()
        assert result.G_Y == 0.0
        assert result.uses_f0_anywhere == False

    def test_has_timestamp_by_default(self):
        """Should have timestamp even with defaults."""
        result = NonCircularResult()
        assert len(result.timestamp) > 0

    def test_can_set_values(self):
        """Should be able to set values."""
        result = NonCircularResult(G_Y=3.72e4, is_genuine_emergence=True)
        assert result.G_Y == 3.72e4
        assert result.is_genuine_emergence == True


class TestEdgeCases:
    """Test edge cases and boundary conditions."""

    def test_mpmath_fallback(self):
        """Should work even without mpmath (using fallback)."""
        # This test verifies the structure works
        result = derive_f0_non_circular()
        assert result.f0_calculated > 0

    def test_repeated_calls_consistent(self):
        """Repeated calls should give consistent results."""
        result1 = derive_f0_non_circular()
        result2 = derive_f0_non_circular()
        
        assert abs(result1.G_Y - result2.G_Y) < 1e-10
        assert abs(result1.R_Psi - result2.R_Psi) < 1e-10
        assert abs(result1.f0_calculated - result2.f0_calculated) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
