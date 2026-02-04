#!/usr/bin/env python3
"""
Tests for Emotional Stress-Energy Tensor T_μν(Φ)

Tests cover:
- Emotional field parameter validation
- Potential computation and derivatives
- Stress-energy tensor calculation
- Conservation law validation
- Collective sovereignty index
- Phase diagram analysis
"""

import numpy as np
import pytest
import sys
import os

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'utils'))

from emotional_stress_tensor import (
    EmotionalFieldParameters,
    EmotionalStressTensor,
    compute_collective_sovereignty_index
)


class TestEmotionalFieldParameters:
    """Test emotional field parameters."""
    
    def test_initialization(self):
        """Test parameter initialization."""
        params = EmotionalFieldParameters()
        assert params.lambda_rigidity == 1.0
        assert params.Phi_0 == 1.0
        assert params.mu_squared == 0.1
        assert params.f0 == 141.7001
        
    def test_phase_detection(self):
        """Test phase detection."""
        # Restored phase
        params_restored = EmotionalFieldParameters(mu_squared=0.1)
        assert params_restored.is_restored_phase
        assert not params_restored.is_broken_symmetry
        
        # Broken symmetry
        params_broken = EmotionalFieldParameters(mu_squared=-0.1)
        assert params_broken.is_broken_symmetry
        assert not params_broken.is_restored_phase


class TestEmotionalPotential:
    """Test emotional potential V(Φ)."""
    
    def setup_method(self):
        """Setup for each test."""
        self.params = EmotionalFieldParameters(
            lambda_rigidity=1.0,
            Phi_0=1.0,
            mu_squared=-0.1  # Broken symmetry
        )
        self.tensor = EmotionalStressTensor(self.params)
        
    def test_potential_computation(self):
        """Test potential computation."""
        Phi = np.array([0.0, 0.5, 1.0])
        V = self.tensor.emotional_potential(Phi)
        
        assert len(V) == len(Phi)
        assert isinstance(V, np.ndarray)
        
        # At Phi = 0, should have positive potential (local maximum in broken phase)
        assert V[0] > V[1] or V[0] > V[2]
        
    def test_potential_derivative(self):
        """Test potential derivative."""
        Phi = np.array([0.5])
        dV = self.tensor.potential_derivative(Phi)
        
        assert len(dV) == 1
        assert isinstance(dV[0], (float, np.floating))
        
    def test_equilibria_in_broken_phase(self):
        """Test that broken symmetry phase has multiple equilibria."""
        Phi_range = np.linspace(-2, 2, 200)
        phase_data = self.tensor.phase_diagram(Phi_range)
        
        assert phase_data['phase'] == 'broken_symmetry'
        # Should have at least 2 equilibria (±Φ₀)
        assert len(phase_data['equilibria']) >= 2


class TestStressTensor:
    """Test stress-energy tensor computation."""
    
    def setup_method(self):
        """Setup for each test."""
        self.params = EmotionalFieldParameters()
        self.tensor = EmotionalStressTensor(self.params)
        
    def test_tensor_shape(self):
        """Test tensor has correct shape."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric)
        
        assert T_mu_nu.shape == (4, 4)
        
    def test_tensor_symmetry(self):
        """Test tensor is symmetric T_μν = T_νμ."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric)
        
        # Check symmetry
        np.testing.assert_allclose(T_mu_nu, T_mu_nu.T, rtol=1e-10)
        
    def test_energy_density(self):
        """Test energy density T₀₀."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric)
        T00 = self.tensor.energy_density(T_mu_nu)
        
        assert isinstance(T00, (float, np.floating))
        
    def test_momentum_flux(self):
        """Test momentum flux T₀ᵢ."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric)
        T0i = self.tensor.momentum_flux(T_mu_nu)
        
        assert T0i.shape == (3,)
        
    def test_spatial_stress(self):
        """Test spatial stress tensor Tᵢⱼ."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric)
        Tij = self.tensor.spatial_stress(T_mu_nu)
        
        assert Tij.shape == (3, 3)
        # Should be symmetric
        np.testing.assert_allclose(Tij, Tij.T, rtol=1e-10)
        
    def test_trace(self):
        """Test trace Tr(T)."""
        Phi = 0.5
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        g_metric = np.diag([-1, 1, 1, 1])
        g_inverse = np.diag([-1, 1, 1, 1])
        
        T_mu_nu = self.tensor.compute_stress_tensor(Phi, dPhi, g_metric, g_inverse)
        trace = self.tensor.trace(T_mu_nu, g_inverse)
        
        assert isinstance(trace, (float, np.floating))


class TestStressClassification:
    """Test stress region classification."""
    
    def setup_method(self):
        """Setup for each test."""
        self.tensor = EmotionalStressTensor()
        
    def test_valley_of_peace(self):
        """Test valley of peace classification."""
        cls = self.tensor.classify_stress_region(T00=0.15, Psi=0.96)
        assert cls['region'] == 'Valley of peace'
        assert cls['risk_level'] == 'low'
        
    def test_work_plateau(self):
        """Test work plateau classification."""
        cls = self.tensor.classify_stress_region(T00=0.30, Psi=0.90)
        assert cls['region'] == 'Work plateau'
        assert cls['risk_level'] == 'moderate'
        
    def test_alert_zone(self):
        """Test alert zone classification."""
        cls = self.tensor.classify_stress_region(T00=0.50, Psi=0.80)
        assert cls['region'] == 'Alert zone'
        assert cls['risk_level'] == 'high'
        
    def test_singularity(self):
        """Test singularity classification."""
        cls = self.tensor.classify_stress_region(T00=0.65, Psi=0.70)
        assert cls['region'] == 'Singularity'
        assert cls['risk_level'] == 'critical'


class TestCollectiveSovereignty:
    """Test collective sovereignty index."""
    
    def test_perfect_sovereignty(self):
        """Test perfect sovereignty case."""
        N = 100
        Psi_values = np.ones(N)  # Perfect coherence
        T00_values = np.zeros(N)  # No stress
        curvature_values = np.zeros(N)  # No curvature
        
        S_col = compute_collective_sovereignty_index(
            Psi_values, T00_values, curvature_values
        )
        
        # Should be very close to 1.0
        assert S_col > 0.99
        
    def test_low_sovereignty(self):
        """Test low sovereignty case."""
        N = 100
        Psi_values = np.full(N, 0.5)  # Low coherence
        T00_values = np.full(N, 0.8)  # High stress
        curvature_values = np.full(N, 0.9)  # High curvature
        
        S_col = compute_collective_sovereignty_index(
            Psi_values, T00_values, curvature_values
        )
        
        # Should be low
        assert S_col < 0.3
        
    def test_mixed_sovereignty(self):
        """Test mixed case."""
        N = 100
        Psi_values = np.random.uniform(0.7, 0.95, N)
        T00_values = np.random.uniform(0.1, 0.5, N)
        curvature_values = np.random.uniform(0.0, 0.8, N)
        
        S_col = compute_collective_sovereignty_index(
            Psi_values, T00_values, curvature_values
        )
        
        # Should be somewhere in middle
        assert 0.0 < S_col < 1.0


class TestConservationLaw:
    """Test conservation law and source terms."""
    
    def setup_method(self):
        """Setup for each test."""
        self.tensor = EmotionalStressTensor()
        
    def test_conservation_violation_shape(self):
        """Test conservation violation has correct shape."""
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        
        violation = self.tensor.conservation_violation(
            f_current=141.7, dPhi=dPhi, t=0.0
        )
        
        assert violation.shape == (4,)
        
    def test_zero_violation_at_resonance(self):
        """Test violation is small at resonance frequency."""
        dPhi = np.array([0.1, 0.2, 0.1, 0.0])
        
        # At exact resonance, first term should be zero
        violation = self.tensor.conservation_violation(
            f_current=141.7001, dPhi=dPhi, t=0.0
        )
        
        # First term (radiative cooling) should be very small
        # (only spectral term remains)
        assert abs(violation[0]) < abs(dPhi[0]) * 0.01


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
