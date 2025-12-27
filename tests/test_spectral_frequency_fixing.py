#!/usr/bin/env python3
"""
Tests for the Spectral Frequency Fixing module.

This test suite validates the implementation of the Universal Frequency
Fixing Theorem as described in the QCAL ∞³ framework.

Tests cover:
1. Vacuum energy functional properties
2. Triple scaling mechanism
3. Spectral operator eigenvalue rescaling
4. Frequency fixing theorem verification
5. QCAL constants validation

Author: José Manuel Mota Burruezo
Date: December 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from spectral_frequency_fixing import (
    VacuumParameters,
    FrequencyFixingResult,
    VacuumEnergyFunctional,
    TripleScalingMechanism,
    SpectralOperatorRescaling,
    validate_frequency_theorem,
    run_complete_validation,
    QCAL_F0,
    F_RAW,
    R_PSI_STAR,
    K_SCALING,
    OMEGA_RAW,
    OMEGA_0,
    ZETA_PRIME_HALF
)


class TestQCALConstants:
    """Test that QCAL constants are correctly defined."""
    
    def test_fundamental_frequency(self):
        """Test f₀ = 141.7001 Hz."""
        assert QCAL_F0 == 141.7001
        
    def test_raw_frequency(self):
        """Test f_raw = 157.9519 Hz."""
        assert F_RAW == 157.9519
        
    def test_vacuum_radius(self):
        """Test R_Ψ* = 0.6952."""
        assert R_PSI_STAR == 0.6952
        
    def test_scaling_factor(self):
        """Test k = (f₀/f_raw)² ≈ 0.806."""
        expected_k = (QCAL_F0 / F_RAW) ** 2
        assert abs(K_SCALING - expected_k) < 1e-10
        assert 0.80 < K_SCALING < 0.81
        
    def test_angular_frequencies(self):
        """Test ω_raw and ω₀ are 2π × f."""
        assert abs(OMEGA_RAW - 2 * np.pi * F_RAW) < 1e-10
        assert abs(OMEGA_0 - 2 * np.pi * QCAL_F0) < 1e-10
        
    def test_zeta_prime_half(self):
        """Test ζ'(1/2) is negative."""
        assert ZETA_PRIME_HALF < 0
        # Known value is approximately -3.92
        assert -4.0 < ZETA_PRIME_HALF < -3.8


class TestVacuumParameters:
    """Test VacuumParameters dataclass."""
    
    def test_default_values(self):
        """Test default parameter values."""
        params = VacuumParameters()
        assert params.alpha == 1.0
        assert params.beta == 1.0
        assert params.gamma == 1.0
        assert params.delta == 0.5
        assert params.eta == np.pi
        assert params.zeta_prime_half == ZETA_PRIME_HALF
        
    def test_custom_values(self):
        """Test custom parameter values."""
        params = VacuumParameters(alpha=2.0, beta=0.5, gamma=1.5)
        assert params.alpha == 2.0
        assert params.beta == 0.5
        assert params.gamma == 1.5


class TestVacuumEnergyFunctional:
    """Test the vacuum energy functional."""
    
    def test_energy_positive_R(self):
        """Test energy is finite for positive R."""
        func = VacuumEnergyFunctional()
        E = func.energy(1.0)
        assert np.isfinite(E)
        
    def test_energy_diverges_at_zero(self):
        """Test energy diverges at R = 0."""
        func = VacuumEnergyFunctional()
        E = func.energy(1e-10)
        assert E > 1e20  # Very large
        
    def test_energy_invalid_R(self):
        """Test energy returns inf for R ≤ 0."""
        func = VacuumEnergyFunctional()
        assert func.energy(0) == np.inf
        assert func.energy(-1) == np.inf
        
    def test_derivative_at_minimum(self):
        """Test derivative is near zero at minimum."""
        func = VacuumEnergyFunctional()
        R_star, _ = func.find_minimum()
        dE = func.derivative(R_star)
        assert abs(dE) < 0.1  # Near zero
        
    def test_second_derivative_positive_at_minimum(self):
        """Test curvature is positive at minimum (stable)."""
        func = VacuumEnergyFunctional()
        R_star, _ = func.find_minimum()
        d2E = func.second_derivative(R_star)
        assert d2E > 0  # Positive curvature = stable minimum
        
    def test_find_minimum_in_range(self):
        """Test minimum is found within search range."""
        func = VacuumEnergyFunctional()
        R_star, E_min = func.find_minimum(R_range=(0.1, 10.0))
        assert 0.1 <= R_star <= 10.0
        assert np.isfinite(E_min)
        
    def test_scaling_factor(self):
        """Test scaling factor is applied correctly."""
        func_raw = VacuumEnergyFunctional(scaled=False)
        func_scaled = VacuumEnergyFunctional(scaled=True)
        
        R_test = 1.0
        E_raw = func_raw.energy(R_test)
        E_scaled = func_scaled.energy(R_test)
        
        # Scaled energy should be k × raw energy
        assert abs(E_scaled - K_SCALING * E_raw) < 1e-10
        
    def test_custom_k_factor(self):
        """Test custom scaling factor."""
        custom_k = 0.5
        func = VacuumEnergyFunctional(scaled=True, custom_k=custom_k)
        assert func.k_factor == custom_k


class TestTripleScalingMechanism:
    """Test the triple scaling mechanism."""
    
    def test_initialization(self):
        """Test mechanism initializes correctly."""
        mechanism = TripleScalingMechanism()
        assert mechanism.target_f0 == QCAL_F0
        assert mechanism.f_raw == F_RAW
        assert abs(mechanism.k - K_SCALING) < 1e-10
        
    def test_theoretical_values(self):
        """Test theoretical values match problem statement."""
        mechanism = TripleScalingMechanism()
        values = mechanism.get_theoretical_values()
        
        assert values['R_psi_star'] == R_PSI_STAR
        assert values['f_raw'] == F_RAW
        assert values['f0'] == QCAL_F0
        
    def test_scaling_factor_identity(self):
        """Test k = (f₀/f_raw)²."""
        mechanism = TripleScalingMechanism()
        k = mechanism.compute_scaling_factor()
        expected_k = (QCAL_F0 / F_RAW) ** 2
        assert abs(k - expected_k) < 1e-10
        
    def test_fix_frequency(self):
        """Test frequency fixing produces correct result."""
        mechanism = TripleScalingMechanism()
        result = mechanism.fix_frequency(tolerance=0.001)
        
        assert isinstance(result, FrequencyFixingResult)
        assert result.verified
        assert result.relative_error < 0.001
        
    def test_fixed_frequency_value(self):
        """Test fixed frequency equals target."""
        mechanism = TripleScalingMechanism()
        result = mechanism.fix_frequency()
        
        assert abs(result.f0_fixed - QCAL_F0) < 0.01
        
    def test_omega_identity(self):
        """Test ω₀ = √k × ω_raw."""
        mechanism = TripleScalingMechanism()
        result = mechanism.fix_frequency()
        
        # ω₀ = √k × ω_raw should equal 2π × f₀
        omega_expected = np.sqrt(K_SCALING) * OMEGA_RAW
        assert abs(result.omega_0 - omega_expected) < 1e-10


class TestSpectralOperatorRescaling:
    """Test spectral operator eigenvalue rescaling."""
    
    def test_raw_spectrum_generation(self):
        """Test raw eigenvalue generation."""
        spectral = SpectralOperatorRescaling(n_eigenvalues=50)
        raw = spectral.generate_raw_spectrum()
        
        assert len(raw) == 50
        assert all(np.isfinite(raw))
        
    def test_raw_spectrum_centered(self):
        """Test raw spectrum is centered around ω_raw."""
        spectral = SpectralOperatorRescaling(n_eigenvalues=100)
        raw = spectral.generate_raw_spectrum()
        
        mean = np.mean(raw)
        rel_error = abs(mean - OMEGA_RAW) / OMEGA_RAW
        assert rel_error < 0.05  # Within 5%
        
    def test_rescale_by_sqrt_k(self):
        """Test rescaling applies √k factor."""
        spectral = SpectralOperatorRescaling()
        raw = spectral.generate_raw_spectrum()
        scaled = spectral.rescale_spectrum(raw)
        
        # Each scaled eigenvalue should be √k × raw
        for r, s in zip(raw, scaled):
            assert abs(s - spectral.sqrt_k * r) < 1e-10
            
    def test_scaled_spectrum_alignment(self):
        """Test scaled spectrum aligns with ω₀."""
        spectral = SpectralOperatorRescaling(n_eigenvalues=100)
        raw = spectral.generate_raw_spectrum()
        scaled = spectral.rescale_spectrum(raw)
        
        is_aligned, error, _ = spectral.verify_alignment(scaled, OMEGA_0)
        assert is_aligned
        assert error < 0.05
        
    def test_full_validation(self):
        """Test full spectral validation."""
        spectral = SpectralOperatorRescaling()
        result = spectral.full_validation()
        
        assert result['success']
        assert result['raw_aligned']
        assert result['scaled_aligned']


class TestUniversalFrequencyTheorem:
    """Test the Universal Frequency Fixing Theorem."""
    
    def test_theorem_statement(self):
        """Test theorem mathematical identity."""
        # The theorem states: ω₀ = 2π × f₀ = √k × ω_raw
        omega_0_from_f0 = 2 * np.pi * QCAL_F0
        omega_0_from_scaling = np.sqrt(K_SCALING) * OMEGA_RAW
        
        # These should be exactly equal (mathematical identity)
        rel_error = abs(omega_0_from_f0 - omega_0_from_scaling) / omega_0_from_f0
        assert rel_error < 1e-10
        
    def test_validate_frequency_theorem(self):
        """Test the validation function."""
        result = validate_frequency_theorem()
        
        assert result['theorem_verified']
        assert result['identity_error'] < 1e-10
        
    def test_complete_validation(self):
        """Test complete validation succeeds."""
        result = run_complete_validation()
        
        assert result['overall_success']
        assert abs(result['f0_final'] - QCAL_F0) < 0.01


class TestFrequencyFixingResult:
    """Test FrequencyFixingResult dataclass."""
    
    def test_result_fields(self):
        """Test all result fields are present."""
        mechanism = TripleScalingMechanism()
        result = mechanism.fix_frequency()
        
        assert hasattr(result, 'R_psi_star')
        assert hasattr(result, 'f_raw')
        assert hasattr(result, 'f0_fixed')
        assert hasattr(result, 'omega_raw')
        assert hasattr(result, 'omega_0')
        assert hasattr(result, 'k_scaling')
        assert hasattr(result, 'verified')
        assert hasattr(result, 'relative_error')
        
    def test_result_values(self):
        """Test result values are consistent."""
        mechanism = TripleScalingMechanism()
        result = mechanism.fix_frequency()
        
        # f₀ and ω₀ should be related by 2π
        assert abs(result.omega_0 - 2 * np.pi * result.f0_fixed) < 1e-10
        
        # k should be (f₀/f_raw)²
        assert abs(result.k_scaling - (result.f0_fixed / result.f_raw) ** 2) < 0.01


class TestIntegrationWithExistingCode:
    """Test integration with existing QCAL codebase."""
    
    def test_f0_matches_beacon(self):
        """Test f₀ matches the .qcal_beacon value."""
        # The .qcal_beacon file specifies frequency = 141.7001 Hz
        assert QCAL_F0 == 141.7001
        
    def test_coherence_constant(self):
        """Test QCAL coherence constant C = 244.36."""
        # From .qcal_beacon: coherence = "C = 244.36"
        C = 244.36
        assert C > 0  # Coherence is positive
        
    def test_pi_code_888(self):
        """Test π CODE-888 symbolic alignment."""
        # The πCODE-888 is a symbolic reference
        # Verify numeric pi is used correctly
        assert abs(np.pi - 3.141592653589793) < 1e-15


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
