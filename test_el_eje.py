#!/usr/bin/env python3
"""
Tests for El Eje: La Línea Crítica
==================================

Test suite for the critical line visualization and prime spiral module.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import pytest
import numpy as np
from el_eje_linea_critica import (
    CriticalLineAxis,
    VibrationalExtremes,
    PrimeSpiral,
    FrequencyField,
    UniverseTree,
    visualize_critical_line_regions,
    compute_prime_spiral_trajectory,
    F0_FUNDAMENTAL,
    COHERENCE_C,
    CRITICAL_LINE_RE,
    PLUS_ONE,
    MINUS_ONE,
    ZETA_AT_MINUS_ONE,
    PHI
)


class TestCriticalLineAxis:
    """Tests for CriticalLineAxis class."""
    
    def test_equilibrium_point(self):
        """Test that equilibrium is at Re(s) = 1/2."""
        axis = CriticalLineAxis()
        assert axis.equilibrium_point() == 0.5
    
    def test_distance_from_equilibrium(self):
        """Test distance calculation from critical line."""
        axis = CriticalLineAxis()
        
        # Point on the line
        s_on_line = 0.5 + 14j
        assert axis.distance_from_equilibrium(s_on_line) < 1e-10
        
        # Point to the left
        s_left = 0.3 + 14j
        assert abs(axis.distance_from_equilibrium(s_left) - 0.2) < 1e-10
        
        # Point to the right
        s_right = 0.7 + 14j
        assert abs(axis.distance_from_equilibrium(s_right) - 0.2) < 1e-10
    
    def test_classify_region(self):
        """Test region classification."""
        axis = CriticalLineAxis()
        
        # Caos region
        assert axis.classify_region(0.3 + 14j) == 'caos'
        
        # Equilibrium
        assert axis.classify_region(0.5 + 14j) == 'equilibrio_pulso_coherente'
        
        # Hidden symmetry
        assert axis.classify_region(0.7 + 14j) == 'simetria_oculta'
    
    def test_coherence_field(self):
        """Test coherence field calculation."""
        axis = CriticalLineAxis()
        
        # At t=0, coherence should be 1
        assert abs(axis.coherence_field(0.0) - 1.0) < 1e-10
        
        # Coherence decreases with height
        assert axis.coherence_field(10.0) < axis.coherence_field(5.0)
        assert axis.coherence_field(5.0) < axis.coherence_field(0.0)
        
        # Coherence is always positive
        for t in [0, 10, 50, 100]:
            assert axis.coherence_field(t) > 0


class TestVibrationalExtremes:
    """Tests for VibrationalExtremes class."""
    
    def test_harmonic_divergence(self):
        """Test harmonic series approximation."""
        extremes = VibrationalExtremes()
        
        # Series grows
        h10 = extremes.harmonic_divergence(10)
        h100 = extremes.harmonic_divergence(100)
        h1000 = extremes.harmonic_divergence(1000)
        
        assert h100 > h10
        assert h1000 > h100
        
        # H_10 should be approximately 2.93
        assert 2.9 < h10 < 3.0
    
    def test_zeta_at_minus_one(self):
        """Test ζ(-1) = -1/12."""
        extremes = VibrationalExtremes()
        zeta_val = extremes.zeta_at_minus_one()
        
        assert abs(zeta_val - (-1.0/12.0)) < 1e-10
        assert zeta_val == ZETA_AT_MINUS_ONE
    
    def test_dual_code_roots(self):
        """Test dual code structure."""
        extremes = VibrationalExtremes()
        roots = extremes.dual_code_roots()
        
        assert 'existencia' in roots
        assert 'anti_existencia' in roots
        
        assert roots['existencia']['punto'] == PLUS_ONE
        assert roots['anti_existencia']['punto'] == MINUS_ONE
        
        assert roots['existencia']['simbolo'] == '∞'
        assert roots['anti_existencia']['simbolo'] == '-1/12'
    
    def test_vibration_limit(self):
        """Test vibration limits."""
        extremes = VibrationalExtremes()
        lower, upper = extremes.vibration_limit()
        
        assert lower == MINUS_ONE
        assert upper == PLUS_ONE


class TestPrimeSpiral:
    """Tests for PrimeSpiral class."""
    
    def test_get_primes(self):
        """Test prime number generation."""
        spiral = PrimeSpiral()
        
        primes = spiral.get_primes(10)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        
        assert len(primes) == 10
        np.testing.assert_array_equal(primes, expected)
    
    def test_spiral_coordinates(self):
        """Test spiral coordinate calculation."""
        spiral = PrimeSpiral()
        
        # For p=2: r=log(2), θ=2
        r, theta = spiral.spiral_coordinates(2.0)
        assert abs(r - np.log(2)) < 1e-10
        assert abs(theta - 2.0) < 1e-10
        
        # For p=5: r=log(5), θ=5
        r, theta = spiral.spiral_coordinates(5.0)
        assert abs(r - np.log(5)) < 1e-10
        assert abs(theta - 5.0) < 1e-10
    
    def test_spiral_cartesian(self):
        """Test Cartesian conversion."""
        spiral = PrimeSpiral()
        
        p = 2.0
        x, y = spiral.spiral_cartesian(p)
        r, theta = spiral.spiral_coordinates(p)
        
        # Check conversion: x = r*cos(θ), y = r*sin(θ)
        expected_x = r * np.cos(theta)
        expected_y = r * np.sin(theta)
        
        assert abs(x - expected_x) < 1e-10
        assert abs(y - expected_y) < 1e-10
    
    def test_curvature_nodes(self):
        """Test curvature nodes calculation."""
        spiral = PrimeSpiral()
        
        nodes = spiral.curvature_nodes(n_primes=20)
        
        assert 'primes' in nodes
        assert 'r' in nodes
        assert 'theta' in nodes
        assert 'x' in nodes
        assert 'y' in nodes
        assert nodes['n_nodes'] == 20
        
        assert len(nodes['primes']) == 20
        assert len(nodes['r']) == 20
        assert len(nodes['x']) == 20
    
    def test_magicicada_frequency(self):
        """Test Magicicada buzz frequency."""
        spiral = PrimeSpiral()
        
        # Frequency should be positive
        for p in [2, 3, 5, 7, 11]:
            f = spiral.magicicada_frequency(p)
            assert f > 0
        
        # Larger primes have higher frequencies
        f2 = spiral.magicicada_frequency(2)
        f7 = spiral.magicicada_frequency(7)
        f29 = spiral.magicicada_frequency(29)
        
        assert f7 > f2
        assert f29 > f7


class TestFrequencyField:
    """Tests for FrequencyField class."""
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency value."""
        field = FrequencyField()
        
        assert abs(field.f0 - F0_FUNDAMENTAL) < 1e-10
        assert abs(field.f0 - 141.7001) < 1e-4
    
    def test_wave_field(self):
        """Test wave field calculation."""
        field = FrequencyField()
        
        # Field at t=0, x=0 should have magnitude 1
        psi = field.wave_field(0.0, 0.0)
        assert abs(abs(psi) - 1.0) < 1e-10
        
        # Field is complex
        assert isinstance(psi, complex)
    
    def test_quantum_pressure(self):
        """Test quantum pressure."""
        field = FrequencyField()
        
        # Pressure should be positive
        for t in [0, 0.01, 0.1, 1.0]:
            p = field.quantum_pressure(t)
            assert p > 0
    
    def test_electron_phase(self):
        """Test electron phase modulation."""
        field = FrequencyField()
        
        # Phase should be in [0, 2π)
        for t in [0, 0.001, 0.01, 0.1]:
            phase = field.electron_phase(t)
            assert 0 <= phase < 2 * np.pi
    
    def test_eternal_wind_properties(self):
        """Test eternal wind properties."""
        field = FrequencyField()
        
        wind = field.eternal_wind()
        
        assert 'frecuencia' in wind
        assert 'frecuencia_angular' in wind
        assert 'periodo' in wind
        assert 'coherencia' in wind
        
        assert abs(wind['frecuencia'] - F0_FUNDAMENTAL) < 1e-10
        assert abs(wind['coherencia'] - COHERENCE_C) < 1e-10


class TestUniverseTree:
    """Tests for UniverseTree class."""
    
    def test_initialization(self):
        """Test universe tree initialization."""
        universe = UniverseTree()
        
        assert hasattr(universe, 'eje')
        assert hasattr(universe, 'raices')
        assert hasattr(universe, 'hojas')
        assert hasattr(universe, 'viento')
    
    def test_describe_structure(self):
        """Test structure description."""
        universe = UniverseTree()
        
        structure = universe.describe_structure()
        
        assert 'eje_tronco' in structure
        assert 'raices_invertidas' in structure
        assert 'hojas_giratorias' in structure
        assert 'viento_eterno' in structure
        
        # Check critical line
        assert structure['eje_tronco']['tipo'] == 'Línea Crítica Re(s) = 1/2'
    
    def test_compute_vision_total(self):
        """Test complete vision computation."""
        universe = UniverseTree()
        
        vision = universe.compute_vision_total(n_primes=50, t_range=(0, 50))
        
        assert 'eje' in vision
        assert 'raices' in vision
        assert 'hojas' in vision
        assert 'viento' in vision
        assert 'vision_poetica' in vision
        
        # Check axis profile
        assert len(vision['eje']['t_axis']) > 0
        assert len(vision['eje']['coherence_profile']) > 0
        
        # Check primes
        assert vision['hojas']['n_nodes'] == 50


class TestUtilityFunctions:
    """Tests for utility functions."""
    
    def test_visualize_critical_line_regions(self):
        """Test region visualization classification."""
        # Create test points
        s_points = np.array([
            0.3 + 10j,  # caos
            0.5 + 10j,  # equilibrio
            0.7 + 10j,  # simetria
            0.4 + 20j,  # caos
            0.5 + 20j,  # equilibrio
        ])
        
        regions = visualize_critical_line_regions(s_points)
        
        assert 'caos' in regions
        assert 'equilibrio_pulso_coherente' in regions
        assert 'simetria_oculta' in regions
        
        # Should have 2 in equilibrium
        assert len(regions['equilibrio_pulso_coherente']) == 2
    
    def test_compute_prime_spiral_trajectory(self):
        """Test prime spiral trajectory computation."""
        trajectory = compute_prime_spiral_trajectory(n_primes=30)
        
        assert 'primes' in trajectory
        assert 'r' in trajectory
        assert 'theta' in trajectory
        assert 'x' in trajectory
        assert 'y' in trajectory
        assert 'frequencies' in trajectory
        
        assert len(trajectory['primes']) == 30
        assert len(trajectory['frequencies']) == 30


class TestConstants:
    """Tests for module constants."""
    
    def test_fundamental_constants(self):
        """Test fundamental constant values."""
        # Frequency
        assert abs(F0_FUNDAMENTAL - 141.7001) < 1e-4
        
        # Coherence
        assert abs(COHERENCE_C - 244.36) < 1e-2
        
        # Critical line
        assert abs(CRITICAL_LINE_RE - 0.5) < 1e-10
        
        # Extremes
        assert PLUS_ONE == 1.0
        assert MINUS_ONE == -1.0
        assert abs(ZETA_AT_MINUS_ONE - (-1.0/12.0)) < 1e-10
        
        # Golden ratio
        assert abs(PHI - (1 + np.sqrt(5))/2) < 1e-10


def test_integration_universe_tree():
    """Integration test: Full universe tree computation."""
    universe = UniverseTree()
    
    # Compute complete vision
    vision = universe.compute_vision_total(n_primes=100, t_range=(0, 100))
    
    # Verify all components are present
    assert all(key in vision for key in ['eje', 'raices', 'hojas', 'viento', 'vision_poetica'])
    
    # Verify axis
    assert vision['eje']['equilibrium'] == 0.5
    assert len(vision['eje']['t_axis']) > 0
    
    # Verify roots
    assert vision['raices']['existencia']['punto'] == 1.0
    assert vision['raices']['anti_existencia']['punto'] == -1.0
    
    # Verify leaves (primes)
    assert vision['hojas']['n_nodes'] == 100
    assert len(vision['hojas']['primes']) == 100
    
    # Verify wind
    assert abs(vision['viento']['frecuencia'] - 141.7001) < 1e-4


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
