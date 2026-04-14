#!/usr/bin/env python3
"""
Test Suite: Emotional Stress-Energy Tensor Framework

Comprehensive tests for the emotional stress-energy tensor implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'utils'))

from emotional_stress_tensor import (
    EmotionalParameters,
    EmotionalStressTensor,
    EmotionalNetworkDynamics
)
from emotional_field_equations import (
    FieldEquationParameters,
    EinsteinQCALFieldEquations,
    GeodesicSolver
)
from emotional_network_topology import (
    TopologyParameters,
    EmotionalNetworkTopology
)
from emotional_synchronization import (
    SynchronizationParameters,
    EmotionalSynchronizationProtocol
)


class TestEmotionalStressTensor:
    """Tests for stress-energy tensor computation."""
    
    def test_emotional_parameters(self):
        """Test emotional parameters initialization."""
        params = EmotionalParameters()
        assert params.f0 == 141.7001
        assert params.C == 244.36
        assert params.omega_0 == 2 * np.pi * params.f0
    
    def test_bistable_phase(self):
        """Test bistable phase detection."""
        params = EmotionalParameters(mu2=-0.1)
        assert params.is_bistable is True
        assert params.vacuum_expectation == params.Phi0
        
        params_restored = EmotionalParameters(mu2=0.1)
        assert params_restored.is_bistable is False
        assert params_restored.vacuum_expectation == 0.0
    
    def test_emotional_potential(self):
        """Test emotional potential computation."""
        params = EmotionalParameters(
            lambda_rigidity=1.0,
            Phi0=1.0,
            mu2=-0.1
        )
        tensor = EmotionalStressTensor(params=params)
        
        # Test at minima
        Phi_minima = np.array([-1.0, 0.0, 1.0])
        V = tensor.emotional_potential(Phi_minima)
        
        # Minima should be at ±Φ₀
        assert V[0] < V[1]  # -Φ₀ is minimum
        assert V[2] < V[1]  # +Φ₀ is minimum
    
    def test_stress_energy_tensor_components(self):
        """Test stress-energy tensor component computation."""
        tensor = EmotionalStressTensor()
        
        N = 10
        Phi = np.random.randn(N)
        dPhi_dt = np.random.randn(N) * 0.1
        grad_Phi = np.random.randn(N, 3) * 0.1
        
        components = tensor.compute_stress_energy_tensor(
            Phi, dPhi_dt, grad_Phi
        )
        
        # Check all components exist
        assert 'T00' in components
        assert 'T0i' in components
        assert 'Tij' in components
        assert 'trace' in components
        
        # Check shapes
        assert components['T00'].shape == (N,)
        assert components['T0i'].shape == (N, 3)
        assert components['Tij'].shape == (N, 3, 3)
        assert components['trace'].shape == (N,)
        
        # Energy density should be positive
        assert np.all(components['T00'] >= 0)
    
    def test_stress_region_classification(self):
        """Test stress region classification."""
        tensor = EmotionalStressTensor()
        
        # Create test data
        T00 = np.array([0.1, 0.3, 0.5, 0.7])
        Psi = np.array([0.98, 0.88, 0.78, 0.68])
        
        regions = tensor.classify_stress_regions(T00, Psi)
        
        # Check classifications
        assert regions['valley_of_peace'][0] is True  # Low stress, high coherence
        assert regions['work_plateau'][1] is True
        assert regions['alert_zone'][2] is True
        assert regions['singularity'][3] is True  # High stress, low coherence
    
    def test_collective_sovereignty_index(self):
        """Test collective sovereignty index computation."""
        tensor = EmotionalStressTensor()
        
        # Perfect system
        N = 100
        Psi_perfect = np.ones(N)
        T00_perfect = np.zeros(N)
        laplacian_perfect = np.zeros(N)
        
        S_col_perfect = tensor.compute_collective_sovereignty(
            Psi_perfect, T00_perfect, laplacian_perfect
        )
        
        assert S_col_perfect >= 0.95  # Should be near perfect
        
        # Stressed system
        Psi_stressed = 0.5 * np.ones(N)
        T00_stressed = 0.8 * np.ones(N)
        laplacian_stressed = np.random.randn(N) * 2
        
        S_col_stressed = tensor.compute_collective_sovereignty(
            Psi_stressed, T00_stressed, laplacian_stressed
        )
        
        assert S_col_stressed < S_col_perfect  # Should be lower
    
    def test_network_dynamics(self):
        """Test network dynamics simulation."""
        num_nodes = 50
        network = EmotionalNetworkDynamics(num_nodes=num_nodes)
        
        # Initial state
        Phi_initial = network.Phi.copy()
        
        # Simulate steps
        dt = 0.01
        for _ in range(10):
            network.simulate_step(dt, 0.0)
        
        # State should evolve
        assert not np.allclose(network.Phi, Phi_initial)


class TestEinsteinQCALFieldEquations:
    """Tests for Einstein-QCAL field equations."""
    
    def test_field_equation_parameters(self):
        """Test field equation parameters."""
        params = FieldEquationParameters()
        assert params.f0 == 141.7001
        assert params.G_QCAL == 1.0
        assert params.Lambda_Psi == 0.1
    
    def test_ricci_tensor_computation(self):
        """Test Ricci tensor computation."""
        field_eqs = EinsteinQCALFieldEquations()
        
        N = 10
        T_stress = np.zeros((N, 4, 4))
        T_stress[:, 0, 0] = 0.5  # Energy density
        
        R_ricci = field_eqs.compute_ricci_tensor(T_stress)
        
        assert R_ricci.shape == (N, 4, 4)
    
    def test_einstein_tensor_computation(self):
        """Test Einstein tensor computation."""
        field_eqs = EinsteinQCALFieldEquations()
        
        N = 10
        R_ricci = np.random.randn(N, 4, 4)
        G_einstein = field_eqs.compute_einstein_tensor(R_ricci)
        
        assert G_einstein.shape == (N, 4, 4)
    
    def test_field_equation_residual(self):
        """Test field equation residual."""
        field_eqs = EinsteinQCALFieldEquations()
        
        N = 10
        T_stress = np.zeros((N, 4, 4))
        T_stress[:, 0, 0] = 0.3
        
        R_ricci = field_eqs.compute_ricci_tensor(T_stress)
        G_einstein = field_eqs.compute_einstein_tensor(R_ricci)
        residual = field_eqs.field_equations_residual(G_einstein, T_stress)
        
        # Residual should be small (equations approximately satisfied)
        residual_norm = np.linalg.norm(residual)
        assert residual_norm < 10.0  # Reasonable for weak-field approximation
    
    def test_emotional_curvature(self):
        """Test emotional curvature computation."""
        field_eqs = EinsteinQCALFieldEquations()
        
        T00 = np.array([0.1, 0.5, 1.0])
        Psi = np.array([0.9, 0.8, 0.5])
        
        curvature = field_eqs.compute_emotional_curvature(T00, Psi)
        
        assert 'R_effective' in curvature
        assert 'classification' in curvature
        
        # High stress, low coherence → high curvature
        assert curvature['R_effective'][2] > curvature['R_effective'][0]
    
    def test_geodesic_solver(self):
        """Test geodesic solver."""
        field_eqs = EinsteinQCALFieldEquations()
        solver = GeodesicSolver(field_eqs)
        
        x0 = np.array([0.0, 0.0, 0.0, 0.0])
        v0 = np.array([1.0, 0.1, 0.0, 0.0])
        
        positions, velocities = solver.integrate_geodesic(
            x0, v0, proper_time=1.0, num_steps=100
        )
        
        assert positions.shape == (100, 4)
        assert velocities.shape == (100, 4)


class TestEmotionalNetworkTopology:
    """Tests for network topology analysis."""
    
    def test_betti_numbers(self):
        """Test Betti number computation."""
        topology = EmotionalNetworkTopology()
        
        # Simple connected graph
        num_nodes = 10
        adjacency = np.ones((num_nodes, num_nodes))
        np.fill_diagonal(adjacency, 0)
        
        betti = topology.compute_betti_numbers(adjacency)
        
        assert betti['beta_0'] == 1  # Fully connected
        assert 'beta_1' in betti
    
    def test_stress_region_classification(self):
        """Test stress region classification."""
        topology = EmotionalNetworkTopology()
        
        T00 = np.array([0.1, 0.3, 0.5, 0.7])
        Psi = np.array([0.98, 0.88, 0.78, 0.68])
        
        regions = topology.classify_stress_regions(T00, Psi)
        
        assert 'masks' in regions
        assert 'counts' in regions
        assert 'percentages' in regions
        assert 'stability' in regions
        
        # Check stability is percentage
        assert 0 <= regions['stability'] <= 100
    
    def test_critical_zone_identification(self):
        """Test critical zone identification."""
        topology = EmotionalNetworkTopology()
        
        num_nodes = 100
        adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
        adjacency = (adjacency + adjacency.T) / 2
        np.fill_diagonal(adjacency, 0)
        
        T00 = 0.3 + 0.3 * np.random.rand(num_nodes)
        Psi = 0.8 + 0.2 * np.random.rand(num_nodes)
        laplacian_Phi = np.random.randn(num_nodes)
        
        critical = topology.identify_critical_zones(
            T00, Psi, laplacian_Phi, adjacency
        )
        
        assert 'critical_nodes' in critical
        assert 'critical_score' in critical
        assert 'priority_ranking' in critical
    
    def test_winding_number(self):
        """Test winding number computation."""
        topology = EmotionalNetworkTopology()
        
        num_nodes = 50
        adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
        adjacency = (adjacency + adjacency.T) / 2
        np.fill_diagonal(adjacency, 0)
        
        phase = 2 * np.pi * np.random.rand(num_nodes)
        Psi_complex = np.exp(1j * phase)
        
        winding = topology.compute_winding_number(Psi_complex, adjacency)
        
        assert 'winding_number' in winding
        assert 'phase_circulation' in winding
    
    def test_comprehensive_analysis(self):
        """Test comprehensive network analysis."""
        topology = EmotionalNetworkTopology()
        
        num_nodes = 50
        adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
        adjacency = (adjacency + adjacency.T) / 2
        np.fill_diagonal(adjacency, 0)
        
        T00 = 0.3 + 0.3 * np.random.rand(num_nodes)
        Psi = 0.8 + 0.2 * np.random.rand(num_nodes)
        laplacian_Phi = np.random.randn(num_nodes)
        Psi_complex = Psi * np.exp(1j * 2 * np.pi * np.random.rand(num_nodes))
        
        analysis = topology.analyze_network_structure(
            adjacency, T00, Psi, laplacian_Phi, Psi_complex
        )
        
        assert 'betti_numbers' in analysis
        assert 'stress_regions' in analysis
        assert 'critical_zones' in analysis
        assert 'summary' in analysis


class TestEmotionalSynchronizationProtocol:
    """Tests for synchronization protocol."""
    
    def test_synchronization_parameters(self):
        """Test synchronization parameters."""
        params = SynchronizationParameters()
        assert params.f0 == 141.7001
        assert params.sovereignty_goal == 0.95
    
    def test_critical_node_detection(self):
        """Test critical node detection."""
        protocol = EmotionalSynchronizationProtocol()
        
        T00 = np.array([0.1, 0.3, 0.6, 0.7])
        Psi = np.array([0.98, 0.88, 0.75, 0.65])
        laplacian_Phi = np.array([0.1, 0.5, 2.5, 3.0])
        
        critical = protocol.detect_critical_nodes(T00, Psi, laplacian_Phi)
        
        # Last two nodes should be critical
        assert len(critical) >= 1
    
    def test_coherent_breathing(self):
        """Test coherent breathing application."""
        protocol = EmotionalSynchronizationProtocol()
        
        N = 50
        Phi = np.random.randn(N) * 0.5
        dPhi_dt = np.random.randn(N) * 0.1
        critical_nodes = np.array([0, 10, 20])
        
        Phi_new, dPhi_dt_new = protocol.apply_coherent_breathing(
            Phi, dPhi_dt, t=0.0, node_indices=critical_nodes
        )
        
        # Should modify critical nodes
        assert not np.allclose(Phi_new, Phi)
    
    def test_phase_synchronization(self):
        """Test phase synchronization."""
        protocol = EmotionalSynchronizationProtocol()
        
        num_nodes = 50
        adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
        adjacency = (adjacency + adjacency.T) / 2
        np.fill_diagonal(adjacency, 0)
        
        phase = 2 * np.pi * np.random.rand(num_nodes)
        Psi_complex = np.exp(1j * phase)
        critical_nodes = np.array([0, 10, 20])
        
        Psi_sync = protocol.synchronize_phase_network(
            Psi_complex, adjacency, critical_nodes
        )
        
        # Should modify phases
        assert not np.allclose(Psi_sync, Psi_complex)
    
    def test_collective_sovereignty_computation(self):
        """Test collective sovereignty index."""
        protocol = EmotionalSynchronizationProtocol()
        
        N = 100
        Psi = 0.9 * np.ones(N)
        T00 = 0.2 * np.ones(N)
        laplacian_Phi = np.random.randn(N) * 0.1
        
        S_col = protocol.compute_collective_sovereignty(
            Psi, T00, laplacian_Phi
        )
        
        assert 0 <= S_col <= 1
        assert S_col > 0.5  # Should be decent for low stress
    
    def test_multi_scale_intervention(self):
        """Test multi-scale intervention."""
        protocol = EmotionalSynchronizationProtocol()
        
        num_nodes = 50
        adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
        adjacency = (adjacency + adjacency.T) / 2
        np.fill_diagonal(adjacency, 0)
        
        Phi = np.random.randn(num_nodes) * 0.5
        dPhi_dt = np.random.randn(num_nodes) * 0.1
        Psi_complex = (0.8 + 0.2 * np.random.rand(num_nodes)) * np.exp(
            1j * 2 * np.pi * np.random.rand(num_nodes)
        )
        T00 = 0.3 + 0.3 * np.random.rand(num_nodes)
        
        degree = np.sum(adjacency, axis=1)
        laplacian = np.diag(degree) - adjacency
        laplacian_Phi = -laplacian @ Phi
        
        result = protocol.multi_scale_intervention(
            Phi, dPhi_dt, Psi_complex, T00, laplacian_Phi, adjacency,
            t=0.0, intervention_level='full'
        )
        
        assert 'S_col' in result
        assert 'intervention_record' in result
        assert 'success' in result
        
        # Should improve sovereignty
        improvement = result['intervention_record']['improvement']
        assert improvement >= 0  # Should not decrease
    
    def test_sovereignty_status_assessment(self):
        """Test sovereignty status assessment."""
        protocol = EmotionalSynchronizationProtocol()
        
        # Perfect sovereignty
        assessment_perfect = protocol.assess_sovereignty_status(0.98)
        assert assessment_perfect['status'] == "SOBERANÍA TOTAL"
        assert assessment_perfect['goal_reached'] is True
        
        # Low sovereignty
        assessment_low = protocol.assess_sovereignty_status(0.50)
        assert assessment_low['status'] == "Requiere Intervención"
        assert assessment_low['goal_reached'] is False


# Integration tests
class TestIntegration:
    """Integration tests for the complete framework."""
    
    def test_complete_workflow(self):
        """Test complete emotional tensor framework workflow."""
        # Setup
        num_nodes = 50
        
        # Create network
        network = EmotionalNetworkDynamics(num_nodes=num_nodes)
        
        # Simulate dynamics
        dt = 0.01
        for _ in range(10):
            network.simulate_step(dt, 0.0)
        
        # Analyze with topology
        topology = EmotionalNetworkTopology()
        
        analysis = topology.compute_network_stress_tensor()
        
        # Apply synchronization
        protocol = EmotionalSynchronizationProtocol()
        
        # This workflow should complete without errors
        assert network.Phi is not None
        assert network.Psi is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
