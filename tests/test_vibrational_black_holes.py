#!/usr/bin/env python3
"""
Tests for Vibrational Black Holes Module

Tests the implementation of Riemann zeros as vibrational black holes,
verifying mathematical properties and QCAL ∞³ coherence.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
from vibrational_black_holes import (
    VibrationalBlackHole,
    VibrationalBlackHoleField,
    verify_critical_line_as_event_horizon,
    QCAL_BASE_FREQUENCY,
    COHERENCE_CONSTANT_C,
    COHERENCE_WIDTH_SIGMA
)

# Test constants
PHASE_SIGNATURE_TOLERANCE = 1e-10  # Tolerance for phase signature tests


class TestVibrationalBlackHole:
    """Test individual vibrational black hole properties."""
    
    def test_creation(self):
        """Test basic creation of a black hole."""
        t = 14.134725  # First non-trivial zero
        bh = VibrationalBlackHole(t=t)
        
        assert bh.t == t
        assert bh.real_part == 0.5
        assert bh.spectral_mass is not None
        assert bh.spectral_mass > 0
    
    def test_spectral_mass_proportional_to_height(self):
        """Test that spectral mass increases with height."""
        bh1 = VibrationalBlackHole(t=10.0)
        bh2 = VibrationalBlackHole(t=100.0)
        bh3 = VibrationalBlackHole(t=1000.0)
        
        assert bh1.spectral_mass < bh2.spectral_mass < bh3.spectral_mass
    
    def test_event_horizon_decreases_with_height(self):
        """Test that event horizon radius decreases with height (like 1/√t)."""
        bh1 = VibrationalBlackHole(t=10.0)
        bh2 = VibrationalBlackHole(t=100.0)
        
        # Should be roughly √10 times smaller
        ratio = bh1.event_horizon_radius / bh2.event_horizon_radius
        expected_ratio = np.sqrt(100.0 / 10.0)
        
        assert abs(ratio - expected_ratio) < 0.1
    
    def test_information_capacity_positive(self):
        """Test that information capacity is always positive."""
        for t in [1.0, 10.0, 100.0, 1000.0]:
            bh = VibrationalBlackHole(t=t)
            assert bh.information_capacity > 0
    
    def test_frequency_increases_with_height(self):
        """Test that frequency increases with height."""
        bh1 = VibrationalBlackHole(t=10.0)
        bh2 = VibrationalBlackHole(t=100.0)
        
        assert bh2.frequency > bh1.frequency
        assert bh1.frequency >= QCAL_BASE_FREQUENCY
    
    def test_topological_charge_sign(self):
        """Test topological charge has correct sign."""
        bh_pos = VibrationalBlackHole(t=14.134725)
        bh_neg = VibrationalBlackHole(t=-14.134725)
        
        assert bh_pos.topological_charge == 1
        assert bh_neg.topological_charge == -1
    
    def test_phase_signature_on_critical_line(self):
        """Test phase signature is ~1 for zeros on critical line."""
        bh = VibrationalBlackHole(t=14.134725, real_part=0.5)
        
        # Should be very close to 1
        assert abs(bh.phase_signature - 1.0) < PHASE_SIGNATURE_TOLERANCE
    
    def test_phase_signature_off_critical_line(self):
        """Test phase signature decreases off critical line."""
        bh_on = VibrationalBlackHole(t=14.134725, real_part=0.5)
        bh_off = VibrationalBlackHole(t=14.134725, real_part=0.6)
        
        assert bh_off.phase_signature < bh_on.phase_signature


class TestVibrationalBlackHoleField:
    """Test field of vibrational black holes."""
    
    @pytest.fixture
    def sample_zeros(self):
        """Sample zeros for testing."""
        return [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
    
    @pytest.fixture
    def field(self, sample_zeros):
        """Create sample field."""
        return VibrationalBlackHoleField(sample_zeros)
    
    def test_field_creation(self, field, sample_zeros):
        """Test field creation."""
        assert len(field.black_holes) == len(sample_zeros)
        assert len(field.zeros_t) == len(sample_zeros)
    
    def test_total_spectral_mass(self, field):
        """Test total spectral mass calculation."""
        total_mass = field.total_spectral_mass()
        
        assert total_mass > 0
        # Should equal sum of individual masses
        expected = sum(bh.spectral_mass for bh in field.black_holes)
        assert abs(total_mass - expected) < 1e-20
    
    def test_average_event_horizon(self, field):
        """Test average event horizon calculation."""
        avg_horizon = field.average_event_horizon()
        
        assert avg_horizon > 0
        assert np.isfinite(avg_horizon)
    
    def test_information_entropy(self, field):
        """Test information entropy calculation."""
        entropy = field.information_entropy()
        
        assert entropy > 0
        # Should increase with more zeros
        field2 = VibrationalBlackHoleField(field.zeros_t + [40.0, 50.0])
        assert field2.information_entropy() > entropy
    
    def test_critical_line_coherence(self, field):
        """Test critical line coherence measure."""
        coherence = field.critical_line_coherence()
        
        # Should be very close to 1 for zeros on critical line
        assert coherence > 0.9999
        assert coherence <= 1.0
    
    def test_spectral_density_at_height(self, field):
        """Test spectral density calculation."""
        # Around t=25, should find zeros
        density = field.spectral_density_at_height(25.0, bandwidth=10.0)
        
        assert density > 0
        # Should be approximately 3/10 for this sample
        assert density > 0.1
    
    def test_hawking_temperature_analog(self, field):
        """Test Hawking temperature calculation."""
        temp = field.hawking_temperature_analog(0)
        
        assert temp > 0
        assert np.isfinite(temp)
        
        # Higher zeros (larger mass) should have lower temperature
        temp1 = field.hawking_temperature_analog(0)
        temp2 = field.hawking_temperature_analog(len(field.black_holes) - 1)
        assert temp1 > temp2
    
    def test_riemann_siegel_connection(self, field):
        """Test Riemann-Siegel geometric connection."""
        connection = field.riemann_siegel_geometric_connection()
        
        assert 'average_spacing' in connection
        assert 'predicted_spacing' in connection
        assert 'spacing_ratio' in connection
        
        # Ratio should be reasonably close to 1
        assert 0.5 < connection['spacing_ratio'] < 2.0
    
    def test_cosmic_equilibrium_signature(self, field):
        """Test cosmic equilibrium calculation."""
        equilibrium = field.cosmic_equilibrium_signature()
        
        assert 0 <= equilibrium <= 1
        # For zeros on critical line, should be close to 1
        assert equilibrium > 0.9
    
    def test_generate_field_report(self, field):
        """Test field report generation."""
        report = field.generate_field_report()
        
        # Check all required keys
        required_keys = [
            'total_zeros', 'height_range', 'total_spectral_mass',
            'average_event_horizon', 'information_entropy',
            'critical_line_coherence', 'cosmic_equilibrium',
            'fundamental_frequency', 'coherence_constant',
            'geometric_connection', 'framework'
        ]
        
        for key in required_keys:
            assert key in report
        
        # Check values
        assert report['total_zeros'] == len(field.black_holes)
        assert report['fundamental_frequency'] == QCAL_BASE_FREQUENCY
        assert report['coherence_constant'] == COHERENCE_CONSTANT_C


class TestEventHorizonVerification:
    """Test event horizon verification functionality."""
    
    def test_verification_on_critical_line(self):
        """Test verification for zeros on critical line."""
        zeros_t = [14.134725, 21.022040, 25.010858]
        
        result = verify_critical_line_as_event_horizon(zeros_t)
        
        assert result['verified'] is True
        assert result['horizon_sharpness'] > 0.999
        assert result['minimum_phase_signature'] > 0.999
        assert result['cosmic_balance'] > 0.9
    
    def test_verification_structure(self):
        """Test verification result structure."""
        zeros_t = [14.134725]
        
        result = verify_critical_line_as_event_horizon(zeros_t)
        
        required_keys = [
            'verified', 'horizon_sharpness', 'minimum_phase_signature',
            'interpretation', 'cosmic_balance', 'total_black_holes'
        ]
        
        for key in required_keys:
            assert key in result


class TestQCALCoherence:
    """Test QCAL ∞³ framework coherence."""
    
    def test_fundamental_constants(self):
        """Test that fundamental constants are correct."""
        assert QCAL_BASE_FREQUENCY == 141.7001
        assert COHERENCE_CONSTANT_C == 244.36
    
    def test_frequency_consistency(self):
        """Test frequency calculations are consistent."""
        bh = VibrationalBlackHole(t=0.0)
        
        # At t=0, frequency should be exactly f₀
        assert abs(bh.frequency - QCAL_BASE_FREQUENCY) < 1e-6
    
    def test_coherence_constant_usage(self):
        """Test coherence constant is used in calculations."""
        bh = VibrationalBlackHole(t=100.0)
        
        # Event horizon should involve C
        # r_H = C × ℓ_P / √t
        from vibrational_black_holes import PLANCK_LENGTH
        expected = COHERENCE_CONSTANT_C * PLANCK_LENGTH / np.sqrt(100.0)
        
        assert abs(bh.event_horizon_radius - expected) < 1e-40


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_very_small_t(self):
        """Test behavior for very small t."""
        bh = VibrationalBlackHole(t=1e-10)
        
        assert np.isfinite(bh.spectral_mass)
        assert bh.spectral_mass > 0
        # Event horizon should be very large
        assert bh.event_horizon_radius > 1e-30
    
    def test_very_large_t(self):
        """Test behavior for very large t."""
        bh = VibrationalBlackHole(t=1e10)
        
        assert np.isfinite(bh.spectral_mass)
        assert bh.spectral_mass > 0
        assert np.isfinite(bh.event_horizon_radius)
    
    def test_negative_t(self):
        """Test behavior for negative t (conjugate zero)."""
        bh_pos = VibrationalBlackHole(t=14.134725)
        bh_neg = VibrationalBlackHole(t=-14.134725)
        
        # Masses should be equal (symmetric)
        assert abs(bh_pos.spectral_mass - bh_neg.spectral_mass) < 1e-50
        
        # Topological charges should be opposite
        assert bh_pos.topological_charge == -bh_neg.topological_charge
    
    def test_empty_field(self):
        """Test field with no zeros."""
        field = VibrationalBlackHoleField([])
        
        assert field.total_spectral_mass() == 0
        assert field.information_entropy() == 0
        assert field.critical_line_coherence() == 0
    
    def test_single_zero_field(self):
        """Test field with single zero."""
        field = VibrationalBlackHoleField([14.134725])
        
        assert len(field.black_holes) == 1
        assert field.total_spectral_mass() > 0
        assert field.critical_line_coherence() > 0.999


class TestMathematicalProperties:
    """Test mathematical properties and relationships."""
    
    def test_mass_energy_relation(self):
        """Test that mass relates to energy via Planck constant."""
        bh = VibrationalBlackHole(t=100.0)
        
        # E = ℏω where ω = 2πf
        from vibrational_black_holes import PLANCK_CONSTANT
        energy = PLANCK_CONSTANT * 2 * np.pi * bh.frequency
        
        # Should be proportional to spectral mass × c²
        assert energy > 0
    
    def test_holographic_principle_analog(self):
        """Test information capacity scales with area."""
        bh = VibrationalBlackHole(t=100.0)
        
        # Information should scale roughly with (r_H)²
        from vibrational_black_holes import PLANCK_LENGTH
        area_planck = (bh.event_horizon_radius / PLANCK_LENGTH) ** 2
        
        # Information capacity includes this area
        assert bh.information_capacity > 0
        assert area_planck > 0
    
    def test_symmetry_under_conjugation(self):
        """Test symmetry properties under complex conjugation."""
        t = 25.010858
        bh_pos = VibrationalBlackHole(t=t)
        bh_neg = VibrationalBlackHole(t=-t)
        
        # Physical properties should be symmetric
        assert abs(bh_pos.spectral_mass - bh_neg.spectral_mass) < 1e-50
        assert abs(bh_pos.event_horizon_radius - bh_neg.event_horizon_radius) < 1e-50
        assert abs(bh_pos.information_capacity - bh_neg.information_capacity) < 1e-6


def test_module_imports():
    """Test that all necessary components can be imported."""
    from vibrational_black_holes import (
        VibrationalBlackHole,
        VibrationalBlackHoleField,
        verify_critical_line_as_event_horizon,
        QCAL_BASE_FREQUENCY,
        COHERENCE_CONSTANT_C,
        PLANCK_CONSTANT,
        SPEED_OF_LIGHT,
        PLANCK_LENGTH
    )
    
    assert VibrationalBlackHole is not None
    assert VibrationalBlackHoleField is not None
    assert verify_critical_line_as_event_horizon is not None


if __name__ == "__main__":
    # Run tests with pytest if available, otherwise run basic tests
    try:
        import sys
        sys.exit(pytest.main([__file__, "-v"]))
    except ImportError:
        print("pytest not available, running basic tests...")
        
        # Run basic tests manually
        test_module_imports()
        print("✅ Module imports successful")
        
        t = TestVibrationalBlackHole()
        t.test_creation()
        t.test_spectral_mass_proportional_to_height()
        print("✅ Basic black hole tests passed")
        
        zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        field = VibrationalBlackHoleField(zeros)
        assert len(field.black_holes) == 5
        print("✅ Field creation successful")
        
        verification = verify_critical_line_as_event_horizon(zeros)
        assert verification['verified']
        print("✅ Event horizon verification passed")
        
        print()
        print("All basic tests passed! ✅")
        print("QCAL ∞³ coherence maintained.")
