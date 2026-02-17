#!/usr/bin/env python3
"""
Tests for verify_psi_energy_equation.py

Tests the Planck relation E_Ψ = hf₀ calculations.

Author: José Manuel Mota Burruezo
Date: January 2026
"""

import pytest
import numpy as np
from verify_psi_energy_equation import PsiEnergyVerifier


class TestPsiEnergyVerifier:
    """Test suite for PsiEnergyVerifier class."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.verifier = PsiEnergyVerifier()
    
    def test_physical_constants(self):
        """Test that physical constants are correctly defined."""
        # Planck constant (exact value from 2019 SI redefinition)
        assert self.verifier.PLANCK_CONSTANT == 6.62607015e-34
        
        # Reduced Planck constant
        h = self.verifier.PLANCK_CONSTANT
        hbar = self.verifier.PLANCK_CONSTANT_REDUCED
        assert abs(hbar - h / (2 * np.pi)) < 1e-42
        
        # Electron volt (exact value from 2019 SI)
        assert self.verifier.ELECTRON_VOLT == 1.602176634e-19
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency is correctly set."""
        assert self.verifier.FUNDAMENTAL_FREQUENCY == 141.7001
    
    def test_planck_relation(self):
        """Test Planck relation E = hf for arbitrary frequency."""
        freq = 100.0  # Hz
        result = self.verifier.planck_relation(freq)
        
        # Check that energy is calculated correctly
        expected_E = self.verifier.PLANCK_CONSTANT * freq
        assert abs(result['E_joules'] - expected_E) < 1e-40
        
        # Check eV conversion
        expected_eV = expected_E / self.verifier.ELECTRON_VOLT
        assert abs(result['E_eV'] - expected_eV) < 1e-25
    
    def test_planck_relation_two_forms_agree(self):
        """Test that E = hf and E = ℏω give the same result."""
        freq = 141.7001
        result = self.verifier.planck_relation(freq)
        
        # Both forms should give the same energy
        diff = abs(result['E_joules'] - result['E_reduced_joules'])
        assert diff < 1e-40
    
    def test_verify_psi_energy_equation(self):
        """Test the main verification for f₀ = 141.7001 Hz."""
        result = self.verifier.verify_psi_energy_equation()
        
        # Check frequency
        assert result['frequency_hz'] == 141.7001
        
        # Check energy calculation
        expected_E = self.verifier.PLANCK_CONSTANT * 141.7001
        assert abs(result['E_joules'] - expected_E) < 1e-40
        
        # Check that result includes interpretation
        assert 'interpretation' in result
        assert isinstance(result['interpretation'], str)
    
    def test_frequency_to_wavelength(self):
        """Test frequency to wavelength conversion."""
        freq = 141.7001
        c = 299792458.0  # m/s
        
        wavelength = self.verifier.frequency_to_wavelength(freq, c)
        expected = c / freq
        
        assert abs(wavelength - expected) < 1e-6
    
    def test_frequency_to_period(self):
        """Test frequency to period conversion."""
        freq = 141.7001
        period = self.verifier.frequency_to_period(freq)
        expected = 1.0 / freq
        
        assert abs(period - expected) < 1e-10
    
    def test_energy_scale(self):
        """Test that energy scale is physically reasonable."""
        result = self.verifier.verify_psi_energy_equation()
        
        # Energy should be positive
        assert result['E_joules'] > 0
        assert result['E_eV'] > 0
        
        # Energy should be very small (ELF range)
        assert result['E_joules'] < 1e-30  # Less than 1e-30 J
        assert result['E_eV'] < 1e-10  # Less than 1e-10 eV
    
    def test_wavelength_scale(self):
        """Test that wavelength is in expected range."""
        freq = self.verifier.FUNDAMENTAL_FREQUENCY
        wavelength = self.verifier.frequency_to_wavelength(freq)
        
        # Should be on order of thousands of km
        assert wavelength > 1e6  # > 1000 km
        assert wavelength < 1e7  # < 10000 km
    
    def test_period_scale(self):
        """Test that period is in expected range."""
        freq = self.verifier.FUNDAMENTAL_FREQUENCY
        period = self.verifier.frequency_to_period(freq)
        
        # Should be on order of milliseconds
        assert period > 1e-3  # > 1 ms
        assert period < 1e-1  # < 100 ms
    
    def test_planck_relation_zero_frequency_raises(self):
        """Test that zero frequency is handled properly."""
        # Zero frequency should give zero energy (not error)
        result = self.verifier.planck_relation(0.0)
        assert result['E_joules'] == 0.0
    
    def test_planck_relation_negative_frequency(self):
        """Test behavior with negative frequency."""
        # Negative frequency should give negative energy
        # (though physically we'd use absolute value)
        result = self.verifier.planck_relation(-100.0)
        assert result['E_joules'] < 0


class TestPhysicalConsistency:
    """Test physical consistency of results."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.verifier = PsiEnergyVerifier()
    
    def test_energy_frequency_proportionality(self):
        """Test that energy is proportional to frequency."""
        freq1 = 100.0
        freq2 = 200.0
        
        E1 = self.verifier.planck_relation(freq1)['E_joules']
        E2 = self.verifier.planck_relation(freq2)['E_joules']
        
        # E2 should be twice E1
        assert abs(E2 / E1 - 2.0) < 1e-10
    
    def test_wavelength_frequency_inverse(self):
        """Test that wavelength is inversely proportional to frequency."""
        freq1 = 100.0
        freq2 = 200.0
        
        lambda1 = self.verifier.frequency_to_wavelength(freq1)
        lambda2 = self.verifier.frequency_to_wavelength(freq2)
        
        # lambda1 should be twice lambda2
        assert abs(lambda1 / lambda2 - 2.0) < 1e-10
    
    def test_fundamental_frequency_comparison(self):
        """Test fundamental frequency against known references."""
        f0 = self.verifier.FUNDAMENTAL_FREQUENCY
        
        # Should be in ELF range (3-30 Hz) or slightly above
        assert f0 > 30  # Above ELF
        assert f0 < 3000  # Below VLF
        
        # Specifically, it's around 142 Hz
        assert abs(f0 - 141.7) < 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
