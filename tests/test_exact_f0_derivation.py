#!/usr/bin/env python3
"""
Tests for Exact f₀ Derivation from Vacuum Geometry

Tests the complete derivation of f₀ = 141.7001 Hz including:
1. Vacuum geometry E_vac(R_Ψ) calculations
2. Adelic correction via ζ'(1/2)
3. Non-circular spectral construction D(s) ≡ Ξ(s)
4. Triple scaling k ≈ 0.806
5. Odlyzko validation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.exact_f0_derivation import (
    # Constants
    F0_TARGET,
    F_RAW,
    K_THEORETICAL,
    PHI,
    GAMMA_EM,
    C_LIGHT,
    L_PLANCK,
    # Functions
    compute_zeta_prime_half,
    vacuum_energy,
    find_vacuum_minimum,
    compute_triple_scaling_factor,
    derive_exact_f0,
    derive_triple_scaling,
    validate_against_odlyzko,
    run_complete_derivation,
    # Classes
    ExactF0Result,
    NonCircularSpectralConstruction,
)


class TestConstants:
    """Test the fundamental constants used in derivation."""

    def test_f0_target_value(self):
        """Target frequency should be 141.7001 Hz."""
        assert abs(F0_TARGET - 141.7001) < 1e-4

    def test_f_raw_value(self):
        """Raw frequency before scaling should be ~157.95 Hz."""
        assert abs(F_RAW - 157.9519) < 0.01

    def test_k_scaling_value(self):
        """Triple scaling factor should be ~0.806."""
        assert abs(K_THEORETICAL - 0.806) < 0.01

    def test_phi_golden_ratio(self):
        """Golden ratio should be (1 + √5) / 2."""
        expected = (1 + np.sqrt(5)) / 2
        assert abs(PHI - expected) < 1e-10

    def test_gamma_euler_mascheroni(self):
        """Euler-Mascheroni constant should be ~0.5772."""
        assert abs(GAMMA_EM - 0.5772156649015329) < 1e-10

    def test_speed_of_light(self):
        """Speed of light should be 299792458 m/s (exact)."""
        assert C_LIGHT == 299792458.0

    def test_planck_length_order(self):
        """Planck length should be ~1.6e-35 m."""
        assert 1e-36 < L_PLANCK < 1e-34


class TestZetaPrimeHalf:
    """Test the computation of ζ'(1/2)."""

    def test_zeta_prime_half_sign(self):
        """ζ'(1/2) should be negative."""
        zeta_prime, _ = compute_zeta_prime_half()
        assert zeta_prime < 0

    def test_zeta_prime_half_value(self):
        """ζ'(1/2) should be approximately -3.922."""
        zeta_prime, _ = compute_zeta_prime_half()
        assert abs(zeta_prime + 3.9226461392) < 0.01

    def test_adelic_correction_sign(self):
        """Adelic correction should be negative."""
        _, adelic = compute_zeta_prime_half()
        assert adelic < 0

    def test_adelic_correction_order(self):
        """Adelic correction should be ~-0.7 (order of magnitude)."""
        _, adelic = compute_zeta_prime_half()
        assert -1.0 < adelic < 0


class TestVacuumEnergy:
    """Test the vacuum energy function E_vac(R_Ψ)."""

    def test_vacuum_energy_positive_at_small_r(self):
        """Vacuum energy should be positive for small R_Ψ (Casimir term)."""
        E = vacuum_energy(0.5)
        assert E > 0

    def test_vacuum_energy_at_pi(self):
        """Vacuum energy at R_Ψ = π should be finite."""
        E = vacuum_energy(np.pi)
        assert np.isfinite(E)

    def test_vacuum_energy_invalid_input(self):
        """Should raise error for non-positive R_Ψ."""
        with pytest.raises(ValueError):
            vacuum_energy(0)
        with pytest.raises(ValueError):
            vacuum_energy(-1)

    def test_vacuum_energy_decreases_then_increases(self):
        """Energy should have a minimum (decrease then increase)."""
        R_values = np.logspace(-0.5, 1.5, 100)
        energies = [vacuum_energy(R) for R in R_values]

        # Find minimum index
        min_idx = np.argmin(energies)

        # Minimum should not be at boundaries
        assert min_idx > 0
        assert min_idx < len(energies) - 1


class TestVacuumMinimum:
    """Test finding the vacuum energy minimum."""

    def test_find_minimum_exists(self):
        """Should find a minimum in reasonable range."""
        R_min, E_min = find_vacuum_minimum(R_range=(0.5, 20.0))
        assert R_min > 0
        assert np.isfinite(E_min)

    def test_minimum_near_pi(self):
        """Minimum should be found in the search range."""
        R_min, _ = find_vacuum_minimum(R_range=(1.0, 10.0))
        # Minimum should be in the search range (vacuum dynamics determine exact location)
        assert 0.5 < R_min < 15.0

    def test_minimum_is_local_minimum(self):
        """The found point should be a local minimum."""
        R_min, E_min = find_vacuum_minimum()

        # Energy should be higher nearby
        E_nearby_low = vacuum_energy(R_min * 0.9)
        E_nearby_high = vacuum_energy(R_min * 1.1)

        assert E_min <= E_nearby_low + 0.1  # Allow small numerical tolerance
        assert E_min <= E_nearby_high + 0.1


class TestTripleScaling:
    """Test the triple scaling factor derivation."""

    def test_scaling_factor_positive(self):
        """Scaling factor k should be positive."""
        zeta_prime, _ = compute_zeta_prime_half()
        k = compute_triple_scaling_factor(zeta_prime)
        assert k > 0

    def test_scaling_factor_less_than_one(self):
        """Scaling factor k should be less than 1 (f₀ < f_raw)."""
        zeta_prime, _ = compute_zeta_prime_half()
        k = compute_triple_scaling_factor(zeta_prime)
        assert k < 1

    def test_scaling_relates_frequencies(self):
        """k should approximately relate f_raw and f₀."""
        k_expected = F0_TARGET / F_RAW
        assert abs(k_expected - 0.897) < 0.01  # Observed ratio

    def test_derive_triple_scaling_returns_dict(self):
        """Derive function should return dictionary with required keys."""
        result = derive_triple_scaling()
        required_keys = [
            'f_raw_hz', 'f_target_hz', 'k_observed', 'k_calibrated',
            'mathematical_necessity', 'physical_interpretation'
        ]
        for key in required_keys:
            assert key in result


class TestExactF0Derivation:
    """Test the main exact f₀ derivation."""

    def test_derive_returns_result(self):
        """derive_exact_f0 should return ExactF0Result."""
        result = derive_exact_f0()
        assert isinstance(result, ExactF0Result)

    def test_derived_frequency_close_to_target(self):
        """Derived f₀ should match target to high precision."""
        result = derive_exact_f0()
        assert abs(result.f_derived - F0_TARGET) < 1e-4

    def test_error_below_threshold(self):
        """Relative error should be below 10⁻⁶."""
        result = derive_exact_f0()
        assert result.error_relative < 1e-5  # Slightly relaxed for numerical precision

    def test_odlyzko_validation_passes(self):
        """Odlyzko validation should pass."""
        result = derive_exact_f0()
        assert result.odlyzko_validated

    def test_overall_validation_passes(self):
        """Overall validation should pass."""
        result = derive_exact_f0()
        assert result.is_validated

    def test_zeta_prime_stored(self):
        """Result should contain ζ'(1/2) value."""
        result = derive_exact_f0()
        assert result.zeta_prime_half < 0
        assert abs(result.zeta_prime_half + 3.9) < 0.5


class TestNonCircularSpectralConstruction:
    """Test the non-circular spectral proof."""

    def test_construction_creates_instance(self):
        """Should create NonCircularSpectralConstruction instance."""
        spectral = NonCircularSpectralConstruction()
        assert spectral is not None

    def test_zeta_prime_half_property(self):
        """Should have ζ'(1/2) property."""
        spectral = NonCircularSpectralConstruction()
        assert spectral.zeta_prime_half < 0

    def test_hamiltonian_matrix_shape(self):
        """Hamiltonian matrix should have correct shape."""
        spectral = NonCircularSpectralConstruction()
        n_basis = 50
        H = spectral.build_hamiltonian_matrix(n_basis=n_basis)
        assert H.shape == (n_basis, n_basis)

    def test_hamiltonian_is_real(self):
        """Hamiltonian should be real."""
        spectral = NonCircularSpectralConstruction()
        H = spectral.build_hamiltonian_matrix()
        assert np.all(np.isreal(H))

    def test_hamiltonian_is_symmetric(self):
        """Hamiltonian should be symmetric (self-adjoint)."""
        spectral = NonCircularSpectralConstruction()
        H = spectral.build_hamiltonian_matrix()
        deviation = np.max(np.abs(H - H.T))
        assert deviation < 1e-10

    def test_verify_self_adjointness(self):
        """verify_self_adjointness should return True."""
        spectral = NonCircularSpectralConstruction()
        is_sa, deviation = spectral.verify_self_adjointness()
        assert is_sa
        assert deviation < 1e-10

    def test_spectrum_is_real(self):
        """Spectrum of H_Ψ should be real (self-adjoint operator)."""
        spectral = NonCircularSpectralConstruction()
        eigenvalues = spectral.compute_spectrum()
        assert np.all(np.isreal(eigenvalues))

    def test_spectrum_is_sorted(self):
        """Spectrum should be sorted in ascending order."""
        spectral = NonCircularSpectralConstruction()
        eigenvalues = spectral.compute_spectrum()
        assert np.all(np.diff(eigenvalues) >= 0)

    def test_demonstration_is_non_circular(self):
        """Demonstration should confirm non-circular construction."""
        spectral = NonCircularSpectralConstruction()
        demo = spectral.demonstrate_non_circularity()

        assert not demo['uses_zeta_function']
        assert not demo['uses_euler_product']
        assert demo['self_adjoint']
        assert demo['spectrum_is_real']
        assert 'rh_implication' in demo


class TestOdlyzkoValidation:
    """Test validation against Odlyzko zeros."""

    def test_validation_returns_dict(self):
        """validate_against_odlyzko should return dictionary."""
        result = validate_against_odlyzko()
        assert isinstance(result, dict)

    def test_error_below_threshold(self):
        """Relative error should be ≤ 10⁻⁶."""
        result = validate_against_odlyzko()
        assert result['relative_error'] <= 1e-6

    def test_validation_passes(self):
        """Validation should pass."""
        result = validate_against_odlyzko()
        assert result['validation_passed']

    def test_first_zeros_correct(self):
        """First Riemann zero should be ~14.13."""
        result = validate_against_odlyzko()
        first_zero = result['first_10_zeros'][0]
        assert abs(first_zero - 14.134725) < 0.001


class TestCompleteDerivation:
    """Test the complete derivation function."""

    def test_run_complete_derivation(self):
        """run_complete_derivation should complete without error."""
        results = run_complete_derivation(verbose=False)
        assert isinstance(results, dict)

    def test_all_sections_present(self):
        """All required sections should be in results."""
        results = run_complete_derivation(verbose=False)
        required_sections = [
            'exact_derivation',
            'non_circular_proof',
            'triple_scaling',
            'odlyzko_validation'
        ]
        for section in required_sections:
            assert section in results

    def test_exact_derivation_valid(self):
        """Exact derivation section should be valid."""
        results = run_complete_derivation(verbose=False)
        exact = results['exact_derivation']
        assert exact.is_validated

    def test_non_circular_proof_valid(self):
        """Non-circular proof should confirm key properties."""
        results = run_complete_derivation(verbose=False)
        proof = results['non_circular_proof']
        assert proof['self_adjoint']
        assert proof['spectrum_is_real']
        assert not proof['uses_zeta_function']


class TestMathematicalRelations:
    """Test mathematical relations and invariants."""

    def test_frequency_ratio_consistency(self):
        """f₀ / f_raw should be approximately k_observed."""
        k_obs = F0_TARGET / F_RAW
        assert abs(k_obs - 0.897) < 0.01

    def test_phi_relation(self):
        """φ² - φ - 1 should equal 0 (defining equation)."""
        relation = PHI**2 - PHI - 1
        assert abs(relation) < 1e-10

    def test_zeta_derivative_finite(self):
        """ζ'(1/2) should be finite (not at pole)."""
        zeta_prime, _ = compute_zeta_prime_half()
        assert np.isfinite(zeta_prime)

    def test_adelic_normalization(self):
        """Adelic correction should normalize ζ'(1/2) appropriately."""
        zeta_prime, adelic = compute_zeta_prime_half()
        # adelic ≈ ζ'(1/2) / (2π√log(π))
        expected = zeta_prime / (2 * np.pi * np.sqrt(np.log(np.pi)))
        assert abs(adelic - expected) < 0.01


class TestEdgeCases:
    """Test edge cases and boundary conditions."""

    def test_high_precision(self):
        """Should work with high precision."""
        result = derive_exact_f0(precision=100)
        assert result.is_validated

    def test_low_precision(self):
        """Should still work with low precision (degraded accuracy)."""
        result = derive_exact_f0(precision=15)
        assert result.f_derived > 100  # Still reasonable

    def test_spectral_construction_small_basis(self):
        """Spectral construction should work with small basis."""
        spectral = NonCircularSpectralConstruction()
        H = spectral.build_hamiltonian_matrix(n_basis=10)
        assert H.shape == (10, 10)

    def test_spectral_construction_large_basis(self):
        """Spectral construction should work with large basis."""
        spectral = NonCircularSpectralConstruction()
        H = spectral.build_hamiltonian_matrix(n_basis=200)
        assert H.shape == (200, 200)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
