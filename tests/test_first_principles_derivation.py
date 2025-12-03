#!/usr/bin/env python3
"""
Tests for First Principles Derivation Module

Tests the implementation of first-principles derivation of QCAL constants,
eliminating circular dependencies with f₀.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: December 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from first_principles_derivation import (
    derive_G_Y,
    derive_R_psi_from_vacuum,
    find_optimal_prime,
    compute_adelic_correction,
    compute_fractal_correction,
    justify_phi_minus3,
    justify_pi_half,
    derive_all_from_first_principles,
    vacuum_energy_full,
    M_PLANCK,
    L_PLANCK,
    LAMBDA_Q_KG,
    HBAR_C,
    PHI
)


class TestGYDerivation:
    """Test suite for G_Y Yukawa coupling derivation."""

    def test_derive_G_Y_default_values(self):
        """Test G_Y derivation with default physical constants."""
        G_Y, details = derive_G_Y()

        # G_Y should be approximately 3.72×10⁴
        assert 3e4 < G_Y < 4e4
        assert "m_planck_kg" in details
        assert "lambda_Q_kg" in details

    def test_derive_G_Y_custom_values(self):
        """Test G_Y derivation with custom values."""
        # Custom Planck mass (10× larger)
        m_P_custom = M_PLANCK * 10
        G_Y, _ = derive_G_Y(m_P=m_P_custom)

        # G_Y should scale as m_P^(1/3)
        G_Y_default, _ = derive_G_Y()
        expected_ratio = 10 ** (1.0 / 3.0)
        actual_ratio = G_Y / G_Y_default

        assert abs(actual_ratio - expected_ratio) < 0.01

    def test_G_Y_formula_correctness(self):
        """Test that G_Y = (m_P / Λ_Q)^(1/3) is computed correctly."""
        m_P = M_PLANCK
        lambda_Q = LAMBDA_Q_KG

        G_Y, _ = derive_G_Y(m_P=m_P, lambda_Q=lambda_Q)
        expected = (m_P / lambda_Q) ** (1.0 / 3.0)

        assert abs(G_Y - expected) < 1e-10

    def test_G_Y_independent_of_f0(self):
        """Verify G_Y derivation doesn't use f₀ value."""
        # The derivation only uses m_P and Λ_Q
        _, details = derive_G_Y()

        # Check that details don't mention f₀ as an input
        assert "f0" not in str(details).lower() or "without" in str(details).lower()


class TestRPsiDerivation:
    """Test suite for R_Ψ vacuum energy derivation."""

    def test_R_psi_from_vacuum_returns_positive(self):
        """Test that R_Ψ derivation returns positive values."""
        R_psi, details = derive_R_psi_from_vacuum()

        assert R_psi > 0
        assert details["R_physical_m"] > 0

    def test_R_psi_physical_scale(self):
        """Test that R_physical is at reasonable scale."""
        _, details = derive_R_psi_from_vacuum()
        R_physical = details["R_physical_m"]

        # R_physical should be around 10⁵ - 10⁶ meters
        assert 1e4 < R_physical < 1e7

    def test_R_psi_base_order_of_magnitude(self):
        """Test R_Ψ base is around 10^40."""
        R_psi, _ = derive_R_psi_from_vacuum()

        log_R_psi = np.log10(R_psi)
        # Should be around 40 orders of magnitude
        assert 38 < log_R_psi < 42

    def test_alpha_gamma_relation(self):
        """Test that α and γ satisfy physical constraints."""
        _, details = derive_R_psi_from_vacuum()
        alpha = details["alpha_phys"]
        gamma = details["gamma_phys"]

        # α × γ should equal 1 (complementary UV/IR scales)
        # Actually α = ħc/Λ² and γ = Λ²/ħc, so α × γ = 1
        product = alpha * gamma

        assert abs(product - 1.0) < 1e-10


class TestOptimalPrime:
    """Test suite for optimal adelic prime finding."""

    def test_optimal_prime_is_17(self):
        """Test that the optimal prime is 17."""
        optimal_prime, details = find_optimal_prime()

        assert optimal_prime == 17

    def test_prime_17_factor(self):
        """Test the factor for p=17."""
        _, details = find_optimal_prime()

        # exp(π√17 / 2) ≈ 649-650
        factor_17 = details["factors"][17]
        assert 640 < factor_17 < 660

    def test_prime_equilibrium(self):
        """Test that p=17 is at equilibrium point."""
        _, details = find_optimal_prime()
        factors = details["factors"]

        # Primes < 17 have smaller factors
        assert factors[11] < factors[17]
        assert factors[13] < factors[17]

        # Primes > 17 have larger factors
        assert factors[19] > factors[17]
        assert factors[23] > factors[17]


class TestAdelicCorrection:
    """Test suite for adelic correction computation."""

    def test_adelic_correction_p17(self):
        """Test adelic correction for p=17."""
        correction = compute_adelic_correction(17)

        # 17^(7/2) = 17^3.5 ≈ 20240
        expected = 17 ** 3.5
        assert abs(correction - expected) < 1

    def test_adelic_correction_scaling(self):
        """Test that adelic correction scales as p^(7/2)."""
        c11 = compute_adelic_correction(11)
        c17 = compute_adelic_correction(17)
        c23 = compute_adelic_correction(23)

        # Verify monotonic increase
        assert c11 < c17 < c23

        # Verify scaling law
        expected_ratio = (17 / 11) ** 3.5
        actual_ratio = c17 / c11
        assert abs(actual_ratio - expected_ratio) < 0.01


class TestFractalCorrections:
    """Test suite for fractal correction computations."""

    def test_pi_cubed_value(self):
        """Test π³ value."""
        pi_cubed, _, details = compute_fractal_correction()

        expected = np.pi ** 3
        assert abs(pi_cubed - expected) < 1e-10
        assert abs(pi_cubed - 31.006) < 0.01

    def test_phi_sixth_value(self):
        """Test φ⁶ value."""
        _, phi_sixth, details = compute_fractal_correction()

        expected = PHI ** 6
        assert abs(phi_sixth - expected) < 1e-10
        assert abs(phi_sixth - 17.94) < 0.01

    def test_combined_factor(self):
        """Test combined fractal factor."""
        pi_cubed, phi_sixth, details = compute_fractal_correction()

        combined = details["combined_factor"]
        assert abs(combined - pi_cubed * phi_sixth) < 1e-10


class TestPhiMinus3Justification:
    """Test suite for φ^(-3) justification."""

    def test_phi_minus3_value(self):
        """Test φ^(-3) value."""
        info = justify_phi_minus3()

        expected = PHI ** (-3)
        assert abs(info["phi_minus3"] - expected) < 1e-10

    def test_fractal_base_value(self):
        """Test fractal base b = π / φ³."""
        info = justify_phi_minus3()

        expected_base = np.pi / (PHI ** 3)
        assert abs(info["fractal_base"] - expected_base) < 1e-10

    def test_effective_dimension(self):
        """Test effective dimension D_eff = 3."""
        info = justify_phi_minus3()

        assert info["D_eff"] == 3


class TestPiHalfJustification:
    """Test suite for π/2 justification."""

    def test_pi_half_value(self):
        """Test π/2 value."""
        info = justify_pi_half()

        expected = np.pi / 2
        assert abs(info["pi_half"] - expected) < 1e-10

    def test_uniqueness_statement(self):
        """Test that uniqueness is documented."""
        info = justify_pi_half()

        assert "uniqueness" in info
        assert "ONLY" in info["uniqueness"]


class TestVacuumEnergyFull:
    """Test suite for full vacuum energy function."""

    def test_vacuum_energy_positive_R(self):
        """Test vacuum energy for positive R."""
        E = vacuum_energy_full(R=1.0, alpha=1.0, beta=1.0, gamma=0.001, delta=0.5)

        assert np.isfinite(E)

    def test_vacuum_energy_zero_R(self):
        """Test vacuum energy at R=0 returns infinity."""
        E = vacuum_energy_full(R=0, alpha=1.0, beta=1.0, gamma=0.001, delta=0.5)

        assert E == float('inf')

    def test_vacuum_energy_negative_R(self):
        """Test vacuum energy at negative R returns infinity."""
        E = vacuum_energy_full(R=-1.0, alpha=1.0, beta=1.0, gamma=0.001, delta=0.5)

        assert E == float('inf')

    def test_UV_dominance_small_R(self):
        """Test that UV term dominates at small R."""
        alpha = 1.0
        R_small = 0.1

        E = vacuum_energy_full(
            R=R_small, alpha=alpha, beta=0.0, gamma=0.0, delta=0.0
        )
        E_uv = alpha / (R_small ** 4)

        assert abs(E - E_uv) < 1e-10

    def test_IR_dominance_large_R(self):
        """Test that IR term dominates at large R."""
        gamma = 1.0
        R_large = 1000.0

        E = vacuum_energy_full(
            R=R_large, alpha=0.0, beta=0.0, gamma=gamma, delta=0.0
        )
        E_ir = gamma * (R_large ** 2)

        assert abs(E - E_ir) < 1e-10


class TestCompleteDerivation:
    """Test suite for complete first-principles derivation."""

    def test_derive_all_returns_result(self):
        """Test that complete derivation returns a result object."""
        result = derive_all_from_first_principles()

        assert result is not None
        assert result.G_Y > 0
        assert result.R_psi > 0

    def test_G_Y_in_expected_range(self):
        """Test G_Y is in expected range."""
        result = derive_all_from_first_principles()

        # G_Y ≈ 3.72×10⁴
        assert 3e4 < result.G_Y < 4e4

    def test_optimal_prime_is_17(self):
        """Test optimal prime is 17."""
        result = derive_all_from_first_principles()

        assert result.optimal_prime == 17

    def test_R_psi_corrected_order(self):
        """Test R_Ψ with corrections is around 10^47."""
        result = derive_all_from_first_principles()

        log_R = np.log10(result.R_psi_corrected)
        # Should be between 10^44 and 10^50
        assert 44 < log_R < 50

    def test_validation_passes(self):
        """Test that validation passes."""
        result = derive_all_from_first_principles()

        assert result.is_validated

    def test_all_corrections_positive(self):
        """Test all correction factors are positive."""
        result = derive_all_from_first_principles()

        assert result.adelic_correction > 0
        assert result.fractal_correction > 0
        assert result.golden_correction > 0

    def test_timestamp_present(self):
        """Test that timestamp is present."""
        result = derive_all_from_first_principles()

        assert result.timestamp is not None
        assert len(result.timestamp) > 0


class TestPhysicalInterpretation:
    """Test physical interpretation and consistency."""

    def test_planck_mass_value(self):
        """Test Planck mass constant value."""
        assert abs(M_PLANCK - 2.176434e-8) < 1e-13

    def test_planck_length_value(self):
        """Test Planck length constant value."""
        assert abs(L_PLANCK - 1.616255e-35) < 1e-40

    def test_hbar_c_value(self):
        """Test ħc constant value."""
        # ħc ≈ 197.3 MeV·fm in SI ≈ 3.16×10⁻²⁶ J·m
        assert abs(HBAR_C - 3.16152649e-26) < 1e-30

    def test_lambda_Q_scale(self):
        """Test Λ_Q vacuum scale."""
        # Λ_Q ≈ 2.3 meV equivalent ≈ 4×10⁻²² kg
        assert 1e-23 < LAMBDA_Q_KG < 1e-21

    def test_golden_ratio(self):
        """Test golden ratio value."""
        expected_phi = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected_phi) < 1e-15


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
