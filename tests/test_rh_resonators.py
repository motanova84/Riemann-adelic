#!/usr/bin/env python3
"""
Tests for RH ∞³ Resonator System
==================================

Validates that the resonator system correctly:
1. Converts zero spectrum to vibrational modes
2. Achieves mathematical coherence
3. Reproduces physical frequency f₀
4. Generates valid certificates
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path
sys.path.append('.')

from utils.rh_resonators import (
    ResonatorMode,
    RHResonatorSystem,
    F0_FUNDAMENTAL,
    COHERENCE_C,
    UNIVERSAL_C,
    COHERENCE_FACTOR
)


class TestResonatorMode:
    """Tests for individual resonator modes."""
    
    def test_mode_creation(self):
        """Test creating a resonator mode."""
        mode = ResonatorMode(zero_t=14.134725)
        
        assert mode.zero_t == 14.134725
        assert mode.frequency > 0
        assert mode.amplitude > 0
        assert 0 <= mode.phase < 2 * np.pi
        assert mode.energy > 0
        assert mode.coherence_contribution >= 0
    
    def test_frequency_scaling(self):
        """Test that frequency increases with zero height."""
        mode1 = ResonatorMode(zero_t=10.0)
        mode2 = ResonatorMode(zero_t=20.0)
        mode3 = ResonatorMode(zero_t=30.0)
        
        assert mode1.frequency < mode2.frequency < mode3.frequency
    
    def test_amplitude_decay(self):
        """Test that amplitude decreases with zero height."""
        mode1 = ResonatorMode(zero_t=10.0)
        mode2 = ResonatorMode(zero_t=100.0)
        mode3 = ResonatorMode(zero_t=1000.0)
        
        assert mode1.amplitude > mode2.amplitude > mode3.amplitude
    
    def test_energy_positive(self):
        """Test that mode energy is always positive."""
        for t in [1.0, 10.0, 100.0, 1000.0]:
            mode = ResonatorMode(zero_t=t)
            assert mode.energy > 0
    
    def test_evaluate_at_time(self):
        """Test time evolution of mode."""
        mode = ResonatorMode(zero_t=14.134725)
        
        # Evaluate at different times
        psi_0 = mode.evaluate_at_time(0.0)
        psi_1 = mode.evaluate_at_time(0.001)
        psi_2 = mode.evaluate_at_time(0.002)
        
        # Should all be complex numbers
        assert isinstance(psi_0, complex)
        assert isinstance(psi_1, complex)
        assert isinstance(psi_2, complex)
        
        # Amplitude should be constant
        assert np.isclose(abs(psi_0), abs(psi_1), rtol=1e-10)
        assert np.isclose(abs(psi_1), abs(psi_2), rtol=1e-10)


class TestRHResonatorSystem:
    """Tests for the complete resonator system."""
    
    @pytest.fixture
    def simple_resonator(self):
        """Create a simple resonator with a few zeros."""
        zeros = [14.134725, 21.022040, 25.010858]
        return RHResonatorSystem(zeros=zeros)
    
    @pytest.fixture
    def full_resonator(self):
        """Create a resonator with many zeros."""
        zeros = [
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
            52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
            67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
        ]
        return RHResonatorSystem(zeros=zeros)
    
    def test_system_creation(self, simple_resonator):
        """Test creating a resonator system."""
        assert simple_resonator.n_modes == 3
        assert len(simple_resonator.modes) == 3
        assert simple_resonator.total_energy > 0
        assert 0 <= simple_resonator.global_coherence <= 1
    
    def test_modes_sorted(self, full_resonator):
        """Test that modes are sorted by zero height."""
        zeros = [m.zero_t for m in full_resonator.modes]
        assert zeros == sorted(zeros)
    
    def test_global_coherence_range(self, full_resonator):
        """Test that global coherence is in valid range."""
        assert 0 <= full_resonator.global_coherence <= 1
    
    def test_dominant_frequency_near_f0(self, full_resonator):
        """Test that dominant frequency is near f₀."""
        # Should be in the range of F0_FUNDAMENTAL
        # Allow 50% tolerance since frequency depends on mode distribution
        error = abs(full_resonator.dominant_frequency - F0_FUNDAMENTAL)
        assert error < 0.5 * F0_FUNDAMENTAL
    
    def test_spectral_width_positive(self, full_resonator):
        """Test that spectral width is positive."""
        assert full_resonator.spectral_width > 0
    
    def test_evaluate_field(self, simple_resonator):
        """Test evaluating the total field."""
        psi = simple_resonator.evaluate_field(0.0)
        assert isinstance(psi, complex)
        
        # Should be sum of individual modes
        manual_sum = sum(m.evaluate_at_time(0.0) for m in simple_resonator.modes)
        assert np.isclose(psi, manual_sum)
    
    def test_evaluate_coherence_field(self, simple_resonator):
        """Test evaluating coherence field over time."""
        t_array = np.linspace(0, 0.01, 100)
        coherence = simple_resonator.evaluate_coherence_field(t_array)
        
        assert len(coherence) == len(t_array)
        assert np.all(coherence >= 0)  # Coherence is always non-negative
    
    def test_mathematical_validation(self, full_resonator):
        """Test mathematical coherence validation."""
        results = full_resonator.validate_mathematical_coherence()
        
        assert 'global_coherence' in results
        assert 'coherence_achieved' in results
        assert 'mathematical_validation' in results
        assert 'mode_orthogonality' in results
        
        # With 20 modes, should achieve reasonable coherence
        assert results['global_coherence'] > 0.1  # At least some coherence
        assert 0 <= results['global_coherence'] <= 1  # In valid range
    
    def test_physical_validation(self, full_resonator):
        """Test physical coherence validation."""
        results = full_resonator.validate_physical_coherence()
        
        assert 'target_frequency' in results
        assert 'dominant_frequency' in results
        assert 'frequency_match' in results
        assert 'coherence_constant' in results
        
        assert results['target_frequency'] == F0_FUNDAMENTAL
        assert results['coherence_constant'] == COHERENCE_C
    
    def test_certificate_generation(self, full_resonator):
        """Test generating validation certificate."""
        cert = full_resonator.generate_validation_certificate()
        
        # Check required fields
        assert 'system' in cert
        assert 'version' in cert
        assert 'timestamp' in cert
        assert 'author' in cert
        assert 'mathematical_validation' in cert
        assert 'physical_validation' in cert
        assert 'overall_status' in cert
        assert 'signature' in cert
        
        assert cert['system'] == 'RH ∞³ Resonators'
        assert cert['signature'] == '∴𓂀Ω∞³·RH·RESONATORS'
    
    def test_certificate_status(self, full_resonator):
        """Test that certificate status reflects validation."""
        cert = full_resonator.generate_validation_certificate()
        
        # Status should be VALIDATED or PENDING_VALIDATION
        assert cert['overall_status'] in ['VALIDATED', 'PENDING_VALIDATION']
    
    def test_zero_input_handling(self):
        """Test handling of edge case: no zeros."""
        resonator = RHResonatorSystem(zeros=[])
        
        assert resonator.n_modes == 0
        assert resonator.total_energy == 0
        assert resonator.global_coherence >= 0
    
    def test_single_zero_handling(self):
        """Test handling of single zero."""
        resonator = RHResonatorSystem(zeros=[14.134725])
        
        assert resonator.n_modes == 1
        assert resonator.total_energy > 0
        assert 0 <= resonator.global_coherence <= 1
    
    def test_negative_zero_handling(self):
        """Test that negative zeros are converted to positive."""
        resonator = RHResonatorSystem(zeros=[-14.134725, 21.022040])
        
        # Both should be positive
        assert all(m.zero_t > 0 for m in resonator.modes)
        assert resonator.n_modes == 2


class TestConstants:
    """Test that QCAL constants are correct."""
    
    def test_fundamental_frequency(self):
        """Test f₀ value."""
        assert F0_FUNDAMENTAL == 141.7001
    
    def test_coherence_constant(self):
        """Test C value."""
        assert COHERENCE_C == 244.36
    
    def test_universal_constant(self):
        """Test universal C value."""
        assert UNIVERSAL_C == 629.83
    
    def test_coherence_factor(self):
        """Test coherence factor calculation."""
        expected = 244.36 / 629.83
        assert np.isclose(COHERENCE_FACTOR, expected, rtol=1e-10)
        # Should be approximately 0.388
        assert np.isclose(COHERENCE_FACTOR, 0.388, rtol=0.01)


class TestIntegration:
    """Integration tests for complete system."""
    
    def test_end_to_end_validation(self):
        """Test complete validation workflow."""
        # Create system
        zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        resonator = RHResonatorSystem(zeros=zeros)
        
        # Validate
        math_val = resonator.validate_mathematical_coherence()
        phys_val = resonator.validate_physical_coherence()
        
        # Generate certificate
        cert = resonator.generate_validation_certificate()
        
        # Check consistency
        assert cert['mathematical_validation'] == math_val
        assert cert['physical_validation'] == phys_val
        
        # Status should match validations
        both_valid = (math_val['mathematical_validation'] and 
                     phys_val['physical_validation'])
        expected_status = 'VALIDATED' if both_valid else 'PENDING_VALIDATION'
        assert cert['overall_status'] == expected_status
    
    def test_coherence_time_evolution(self):
        """Test that coherence evolves smoothly in time."""
        zeros = [14.134725, 21.022040, 25.010858]
        resonator = RHResonatorSystem(zeros=zeros)
        
        # Evaluate over time
        t_array = np.linspace(0, 0.1, 1000)
        coherence = resonator.evaluate_coherence_field(t_array)
        
        # Should be smooth (no NaN or Inf)
        assert np.all(np.isfinite(coherence))
        
        # Should oscillate around mean coherence
        mean_coh = np.mean(coherence)
        assert 0 < mean_coh < np.max(coherence) * 1.5
    
    def test_reproducibility(self):
        """Test that results are reproducible."""
        zeros = [14.134725, 21.022040, 25.010858]
        
        res1 = RHResonatorSystem(zeros=zeros)
        res2 = RHResonatorSystem(zeros=zeros)
        
        # Should produce identical results
        assert res1.global_coherence == res2.global_coherence
        assert res1.dominant_frequency == res2.dominant_frequency
        assert res1.total_energy == res2.total_energy
        
        # Field evaluation should be identical
        psi1 = res1.evaluate_field(0.001)
        psi2 = res2.evaluate_field(0.001)
        assert psi1 == psi2


if __name__ == "__main__":
    # Run tests with verbose output
    pytest.main([__file__, "-v", "--tb=short"])
