"""
Tests for QCAL Biological Framework
====================================

Unit tests for the biological extension of QCAL theory.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-27
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from biological import (
    EnvironmentalSpectralField,
    SpectralComponent,
    BiologicalClock,
    BiologicalFilter,
    PhaseAccumulator,
    PhaseCollapse,
    create_cicada_environment,
)
from biological.cicada_model import MagicicadaModel


class TestSpectralComponent:
    """Test SpectralComponent class."""
    
    def test_creation(self):
        """Test creating a spectral component."""
        comp = SpectralComponent(
            amplitude=1.0,
            frequency=2*np.pi,
            phase=0.0,
            name="test"
        )
        assert comp.amplitude == 1.0
        assert comp.frequency == 2*np.pi
        assert comp.name == "test"
    
    def test_evaluation(self):
        """Test evaluating component at times."""
        comp = SpectralComponent(1.0, 2*np.pi, 0.0)
        t = np.array([0, 0.5, 1.0])
        result = comp.evaluate(t)
        
        assert len(result) == 3
        assert np.iscomplexobj(result)
        # At t=0, should be amplitude
        assert np.abs(result[0] - 1.0) < 1e-10


class TestEnvironmentalSpectralField:
    """Test EnvironmentalSpectralField class."""
    
    def test_default_creation(self):
        """Test creating field with default components."""
        field = EnvironmentalSpectralField()
        assert len(field.components) == 3  # annual, diurnal, lunar
    
    def test_evaluation(self):
        """Test field evaluation."""
        field = EnvironmentalSpectralField()
        t = np.linspace(0, 1000, 100)
        psi = field.evaluate(t)
        
        assert len(psi) == len(t)
        assert np.iscomplexobj(psi)
    
    def test_add_component(self):
        """Test adding custom component."""
        field = EnvironmentalSpectralField(components=[])
        assert len(field.components) == 0
        
        field.add_component(1.0, 2*np.pi, 0.0, "custom")
        assert len(field.components) == 1
        assert field.components[0].name == "custom"
    
    def test_spectral_density(self):
        """Test spectral density computation."""
        field = EnvironmentalSpectralField()
        omega = np.linspace(0, 1e-4, 100)
        density = field.spectral_density(omega)
        
        assert len(density) == len(omega)
        assert np.all(density >= 0)  # Density must be non-negative
    
    def test_dominant_frequencies(self):
        """Test getting dominant frequencies."""
        field = EnvironmentalSpectralField()
        dominant = field.get_dominant_frequencies(n=3)
        
        assert len(dominant) == 3
        # Should be sorted by amplitude
        amps = [d[2] for d in dominant]
        assert amps == sorted(amps, reverse=True)


class TestBiologicalFilter:
    """Test BiologicalFilter class."""
    
    def test_creation(self):
        """Test filter creation."""
        center = np.array([1.0])
        bandwidth = np.array([0.1])
        filt = BiologicalFilter(center, bandwidth)
        
        assert len(filt.center_frequencies) == 1
    
    def test_response(self):
        """Test filter response."""
        filt = BiologicalFilter(
            center_frequencies=np.array([1.0]),
            bandwidths=np.array([0.1]),
            gains=np.array([1.0])
        )
        
        omega = np.array([0.5, 1.0, 1.5])
        H = filt.response(omega)
        
        assert len(H) == 3
        assert np.iscomplexobj(H)
        # Maximum at center frequency
        assert np.abs(H[1]) >= np.abs(H[0])
    
    def test_annual_tuned_filter(self):
        """Test factory method for annual-tuned filter."""
        filt = BiologicalFilter.create_annual_tuned(q_factor=10.0)
        assert len(filt.center_frequencies) > 0
    
    def test_cicada_filter(self):
        """Test factory method for cicada filter."""
        filt = BiologicalFilter.create_cicada_filter(cycle_years=17)
        assert len(filt.center_frequencies) >= 1


class TestPhaseAccumulator:
    """Test PhaseAccumulator class."""
    
    def test_creation(self):
        """Test accumulator creation."""
        acc = PhaseAccumulator(memory_factor=0.1)
        assert acc.memory_factor == 0.1
        assert acc.current_phase == 0.0
    
    def test_accumulation(self):
        """Test phase accumulation."""
        acc = PhaseAccumulator(memory_factor=0.1, decay_rate=0.0)
        
        phase1 = acc.accumulate(spectral_energy=1.0, dt=1.0)
        assert phase1 > 0
        
        phase2 = acc.accumulate(spectral_energy=1.0, dt=1.0)
        assert phase2 > phase1  # Should increase
    
    def test_reset(self):
        """Test accumulator reset."""
        acc = PhaseAccumulator()
        acc.accumulate(1.0, 1.0)
        
        assert acc.current_phase > 0
        acc.reset()
        assert acc.current_phase == 0.0


class TestPhaseCollapse:
    """Test PhaseCollapse mechanism."""
    
    def test_creation(self):
        """Test collapse detector creation."""
        detector = PhaseCollapse(critical_threshold=10.0)
        assert detector.critical_threshold == 10.0
        assert not detector.activated
    
    def test_activation(self):
        """Test activation detection."""
        detector = PhaseCollapse(critical_threshold=5.0)
        
        # Below threshold
        assert not detector.check_condition(4.0, 1.0, 0.0)
        
        # Above threshold with positive rate
        assert detector.check_condition(6.0, 1.0, 1.0)
        assert detector.activated
        
        # Should not activate again immediately (already activated)
        assert not detector.check_condition(7.0, 1.0, 2.0)
    
    def test_reset(self):
        """Test detector reset."""
        detector = PhaseCollapse(critical_threshold=5.0)
        detector.check_condition(6.0, 1.0, 1.0)
        
        assert detector.activated
        detector.reset()
        assert not detector.activated


class TestBiologicalClock:
    """Test BiologicalClock integration."""
    
    def test_creation(self):
        """Test clock creation."""
        field = EnvironmentalSpectralField()
        filt = BiologicalFilter.create_annual_tuned()
        clock = BiologicalClock(field, filt)
        
        assert clock.time == 0.0
    
    def test_tick(self):
        """Test clock tick."""
        field = EnvironmentalSpectralField()
        filt = BiologicalFilter.create_annual_tuned()
        clock = BiologicalClock(field, filt)
        
        phase1, rate1 = clock.tick(dt=1000.0)
        assert clock.time == 1000.0
        assert phase1 >= 0
    
    def test_simulation(self):
        """Test running simulation."""
        field = EnvironmentalSpectralField()
        filt = BiologicalFilter.create_annual_tuned()
        clock = BiologicalClock(field, filt)
        
        times, phases = clock.run_simulation(duration=10000.0, dt=1000.0)
        
        assert len(times) > 0
        assert len(phases) == len(times)
        assert np.all(np.diff(times) > 0)  # Times increase


class TestCicadaModel:
    """Test Magicicada model."""
    
    def test_creation_17_year(self):
        """Test creating 17-year cicada model."""
        model = MagicicadaModel(cycle_years=17, population_size=100)
        assert model.cycle_years == 17
        assert model.population.size == 100
    
    def test_creation_13_year(self):
        """Test creating 13-year cicada model."""
        model = MagicicadaModel(cycle_years=13, population_size=50)
        assert model.cycle_years == 13
    
    def test_prime_advantage(self):
        """Test prime cycle advantage analysis."""
        model = MagicicadaModel(cycle_years=17, population_size=10)
        analysis = model.test_prime_cycle_advantage()
        
        assert analysis['cicada_cycle'] == 17
        assert analysis['is_prime'] is True
        assert 'overlaps' in analysis
        assert len(analysis['overlaps']) > 0
    
    def test_emergence_simulation_short(self):
        """Test short emergence simulation."""
        model = MagicicadaModel(cycle_years=17, population_size=50)
        
        # Run short simulation (just a few years)
        results = model.simulate_emergence(duration_years=5.0)
        
        assert 'statistics' in results
        assert 'synchrony_index' in results
        assert 'emergence_fraction' in results


class TestCicadaEnvironment:
    """Test cicada-specific environmental field."""
    
    def test_creation(self):
        """Test creating cicada environment."""
        env = create_cicada_environment(year_count=17)
        
        assert len(env.components) >= 4  # Should have multiple components
        
        # Should include QCAL resonance
        names = [c.name for c in env.components]
        assert any('qcal' in name.lower() for name in names)


class TestQCALIntegration:
    """Test integration with QCAL fundamental frequency."""
    
    def test_qcal_frequency_presence(self):
        """Test that QCAL base frequency (141.7001 Hz) is present."""
        env = create_cicada_environment()
        
        # Check for QCAL frequency component
        qcal_components = [c for c in env.components if 'qcal' in c.name.lower()]
        assert len(qcal_components) > 0
        
        # Verify frequency is close to 141.7001 Hz
        for comp in qcal_components:
            freq_hz = comp.frequency / (2 * np.pi)
            assert abs(freq_hz - 141.7001) < 1.0  # Within 1 Hz


# Run tests if executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
