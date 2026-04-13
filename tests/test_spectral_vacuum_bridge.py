#!/usr/bin/env python3
"""
Tests for Spectral-Vacuum Bridge Module

Tests the unification of the spectral operator H_Ψ with vacuum energy E_vac,
validating the mathematical-physical bridge that connects the Riemann Hypothesis
to quantum vacuum energy.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from spectral_vacuum_bridge import (
    SpectralVacuumBridge,
    SpectralVacuumResult,
    PhysicalConstants,
    derive_f0_mathematical,
    validate_physical_consistency,
)


class TestPhysicalConstants:
    """Test suite for PhysicalConstants class."""
    
    def test_default_constants(self):
        """Test default physical constants values."""
        constants = PhysicalConstants()
        
        assert constants.c == 299792458.0
        assert constants.l_planck == pytest.approx(1.616255e-35, rel=1e-4)
        assert constants.alpha == pytest.approx(7.2973525693e-3, rel=1e-8)
    
    def test_from_scipy(self):
        """Test loading constants from scipy."""
        constants = PhysicalConstants.from_scipy()
        
        # Speed of light should be exact
        assert constants.c == 299792458.0
        
        # Planck length should be in correct order of magnitude
        assert 1e-36 < constants.l_planck < 1e-34
    
    def test_vacuum_energy_density_order(self):
        """Test vacuum energy density is in correct cosmological range."""
        constants = PhysicalConstants()
        
        # Dark energy density is ~5-6 × 10^-27 kg/m³
        assert 1e-28 < constants.rho_vac < 1e-26


class TestSpectralVacuumBridge:
    """Test suite for SpectralVacuumBridge class."""
    
    def test_initialization(self):
        """Test bridge initialization."""
        bridge = SpectralVacuumBridge(precision=30)
        
        assert bridge.precision == 30
        assert bridge.phi > 0
        assert bridge.zeta_prime_half < 0
        assert bridge.f0_target == 141.7001
    
    def test_golden_ratio_accuracy(self):
        """Test golden ratio φ is computed accurately."""
        bridge = SpectralVacuumBridge()
        
        # φ = (1 + √5) / 2 ≈ 1.6180339887...
        assert bridge.phi == pytest.approx(1.6180339887, rel=1e-8)
        
        # φ satisfies φ² = φ + 1
        assert bridge.phi ** 2 == pytest.approx(bridge.phi + 1, rel=1e-8)
    
    def test_zeta_prime_half_accuracy(self):
        """Test ζ'(1/2) is computed accurately."""
        bridge = SpectralVacuumBridge()
        
        # ζ'(1/2) ≈ -3.9226461392
        assert bridge.zeta_prime_half == pytest.approx(-3.9226461392, rel=1e-4)
    
    def test_derive_f0_from_zeta_phi(self):
        """Test fundamental frequency derivation from ζ'(1/2) and φ."""
        bridge = SpectralVacuumBridge()
        
        f0_derived, raw_product, normalization = bridge.derive_f0_from_zeta_phi()
        
        # f₀ should be positive
        assert f0_derived > 0
        
        # f₀ should be close to target
        assert f0_derived == pytest.approx(141.7001, rel=1e-6)
        
        # Raw product |ζ'(1/2)| × φ³ ≈ 16.6
        expected_raw = abs(bridge.zeta_prime_half) * (bridge.phi ** 3)
        assert raw_product == pytest.approx(expected_raw, rel=1e-6)
    
    def test_derive_f0_from_vacuum_minimum(self):
        """Test frequency derivation from vacuum energy minimum."""
        bridge = SpectralVacuumBridge()
        
        f0_derived, R_psi = bridge.derive_f0_from_vacuum_minimum()
        
        # f₀ should be positive
        assert f0_derived > 0
        
        # R_Ψ should be near π
        assert R_psi == pytest.approx(np.pi, rel=0.5)
    
    def test_hamiltonian_ground_state(self):
        """Test Hamiltonian ground state computation."""
        bridge = SpectralVacuumBridge()
        
        lambda_0, spectrum = bridge.compute_hamiltonian_ground_state()
        
        # Ground state eigenvalue should be positive
        assert lambda_0 > 0
        
        # Ground state is the minimum eigenvalue (should be ≥ 0.25)
        assert lambda_0 >= 0.25 - 1e-6  # Allow small numerical error
    
    def test_frequency_hamiltonian_conversion(self):
        """Test frequency ↔ Hamiltonian eigenvalue conversion."""
        bridge = SpectralVacuumBridge()
        
        # Test round-trip conversion
        f_original = 10.0  # Hz
        eigenvalue = bridge.hamiltonian_from_frequency(f_original)
        f_recovered = bridge.frequency_from_hamiltonian(eigenvalue)
        
        assert f_recovered == pytest.approx(f_original, rel=1e-10)
    
    def test_hamiltonian_eigenvalue_formula(self):
        """Test λ = ω² + 1/4 formula."""
        bridge = SpectralVacuumBridge()
        
        frequency = 1.0  # Hz
        omega = 2 * np.pi * frequency
        expected_eigenvalue = omega ** 2 + 0.25
        
        computed_eigenvalue = bridge.hamiltonian_from_frequency(frequency)
        
        assert computed_eigenvalue == pytest.approx(expected_eigenvalue, rel=1e-10)
    
    def test_validate_codata_consistency(self):
        """Test CODATA consistency validation."""
        bridge = SpectralVacuumBridge()
        
        validations = bridge.validate_codata_consistency()
        
        # All validations should pass
        assert all(validations.values())
        
        # Check specific validations exist
        assert 'c_consistent' in validations
        assert 'l_planck_order' in validations
        assert 'zeta_prime_valid' in validations
        assert 'phi_valid' in validations
    
    def test_complete_unification(self):
        """Test complete spectral-vacuum unification."""
        bridge = SpectralVacuumBridge()
        
        result = bridge.compute_spectral_vacuum_unification()
        
        # Check result type
        assert isinstance(result, SpectralVacuumResult)
        
        # Check key fields
        assert result.zeta_prime_half < 0
        assert result.phi > 0
        assert result.f0_derived > 0
        assert result.R_psi_optimal > 0
        
        # Deviation should be small
        assert result.deviation_percent < 1.0


class TestSpectralVacuumResult:
    """Test suite for SpectralVacuumResult dataclass."""
    
    def test_default_values(self):
        """Test default values of result dataclass."""
        result = SpectralVacuumResult()
        
        assert result.f0_target == 141.7001
        assert result.is_validated == False
        assert result.timestamp is not None
    
    def test_validation_status(self):
        """Test validation status reflects correct values."""
        bridge = SpectralVacuumBridge()
        result = bridge.compute_spectral_vacuum_unification()
        
        # Should be validated when all checks pass
        assert result.is_validated == True


class TestHelperFunctions:
    """Test suite for module-level helper functions."""
    
    def test_derive_f0_mathematical(self):
        """Test mathematical derivation of f₀."""
        f0 = derive_f0_mathematical()
        
        assert f0 == pytest.approx(141.7001, rel=1e-4)
    
    def test_validate_physical_consistency(self):
        """Test physical consistency validation."""
        validation = validate_physical_consistency()
        
        assert 'spectral_result' in validation
        assert 'codata_validations' in validation
        assert 'f0_derived' in validation
        assert 'is_physically_consistent' in validation


class TestMathematicalPhysicsConnection:
    """Test the core mathematical-physics connection."""
    
    def test_zeta_phi_formula(self):
        """Test the formula f₀ ∝ |ζ'(1/2)| × φ³."""
        bridge = SpectralVacuumBridge()
        
        # The raw product should be approximately 16.6
        raw_product = abs(bridge.zeta_prime_half) * (bridge.phi ** 3)
        
        assert 15.0 < raw_product < 18.0
    
    def test_phi_cubed_value(self):
        """Test φ³ ≈ 4.236."""
        bridge = SpectralVacuumBridge()
        
        phi_cubed = bridge.phi ** 3
        
        assert phi_cubed == pytest.approx(4.2360679775, rel=1e-8)
    
    def test_vacuum_energy_resonant_scale(self):
        """Test vacuum energy minimum near resonant scale R_Ψ = π."""
        bridge = SpectralVacuumBridge()
        
        _, R_psi = bridge.derive_f0_from_vacuum_minimum()
        
        # R_Ψ should be near π (within 10%)
        assert abs(R_psi - np.pi) / np.pi < 0.1
    
    def test_eigenvalue_ground_state_bound(self):
        """Test ground state eigenvalue λ₀ ≥ 1/4."""
        bridge = SpectralVacuumBridge()
        
        lambda_0, _ = bridge.compute_hamiltonian_ground_state()
        
        # The ground state of H = -d²/dt² + 1/4 has λ ≥ 1/4
        assert lambda_0 >= 0.25 - 1e-6


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_precision_levels(self):
        """Test different precision levels give consistent results."""
        results = []
        for precision in [30, 50, 100]:
            bridge = SpectralVacuumBridge(precision=precision)
            result = bridge.compute_spectral_vacuum_unification()
            results.append(result.f0_derived)
        
        # All precision levels should give similar results
        for r in results[1:]:
            assert r == pytest.approx(results[0], rel=1e-4)
    
    def test_frequency_conversion_stability(self):
        """Test frequency conversion is stable for various values."""
        bridge = SpectralVacuumBridge()
        
        frequencies = [0.1, 1.0, 10.0, 100.0, 141.7001]
        
        for f in frequencies:
            eigenvalue = bridge.hamiltonian_from_frequency(f)
            f_recovered = bridge.frequency_from_hamiltonian(eigenvalue)
            
            assert f_recovered == pytest.approx(f, rel=1e-10)


class TestPhysicalInterpretation:
    """Test physical interpretation of results."""
    
    def test_negative_zeta_prime_implies_attraction(self):
        """Test ζ'(1/2) < 0 corresponds to attractive coupling."""
        bridge = SpectralVacuumBridge()
        
        # ζ'(1/2) is negative
        assert bridge.zeta_prime_half < 0
        
        # In the vacuum energy equation, this means
        # the β·ζ'(1/2)/R² term is negative (attractive)
    
    def test_f0_in_audible_range(self):
        """Test f₀ = 141.7001 Hz is in audible range."""
        bridge = SpectralVacuumBridge()
        result = bridge.compute_spectral_vacuum_unification()
        
        # Human audible range is roughly 20 Hz to 20,000 Hz
        assert 20 < result.f0_derived < 20000
    
    def test_f0_near_cosmic_microwave_background_peak(self):
        """
        Note: f₀ = 141.7001 Hz is not directly related to CMB,
        but this test documents that it's a physically meaningful frequency.
        """
        bridge = SpectralVacuumBridge()
        result = bridge.compute_spectral_vacuum_unification()
        
        # f₀ is a well-defined frequency in the audible range
        assert 140 < result.f0_derived < 143


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
