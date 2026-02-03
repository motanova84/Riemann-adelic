#!/usr/bin/env python3
"""
Tests for Emotional Synchronization Protocol

Tests cover:
- Coherent breathing signal generation
- Individual node interventions
- Phase synchronization U(κ_Π)
- Network stress reduction
- Collective sovereignty improvement
"""

import numpy as np
import pytest
import sys
import os

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'utils'))

from emotional_synchronization import (
    SynchronizationParameters,
    Node,
    EmotionalNetwork,
    EmotionalSynchronization,
    QCAL_FREQUENCY
)


class TestSynchronizationParameters:
    """Test synchronization parameters."""
    
    def test_initialization(self):
        """Test parameter initialization."""
        params = SynchronizationParameters()
        assert params.f0 == QCAL_FREQUENCY
        assert params.gamma_cooling > 0
        assert params.duration == 600
        
    def test_thresholds(self):
        """Test stress thresholds."""
        params = SynchronizationParameters()
        assert params.T00_critical == 0.58
        assert params.T00_alert == 0.40
        assert params.Psi_target == 0.95


class TestNode:
    """Test Node class."""
    
    def test_node_creation(self):
        """Test node creation."""
        node = Node(node_id=1, Phi=0.5, Psi=0.9, T00=0.3)
        assert node.id == 1
        assert node.Phi == 0.5
        assert node.Psi == 0.9
        assert node.T00 == 0.3
        
    def test_add_neighbor(self):
        """Test adding neighbors."""
        node1 = Node(1)
        node2 = Node(2)
        
        node1.add_neighbor(node2)
        assert node2 in node1.neighbors
        
        # Adding again should not duplicate
        node1.add_neighbor(node2)
        assert len(node1.neighbors) == 1
        
    def test_phase_rotation(self):
        """Test phase rotation."""
        node = Node(1)
        initial_phase = node.phase
        
        node.apply_rotation(np.pi / 4)
        
        # Phase should have changed
        assert node.phase != initial_phase
        
        # Magnitude should remain 1
        np.testing.assert_almost_equal(abs(node.phase), 1.0)
        
    def test_state_recording(self):
        """Test state recording."""
        node = Node(1, Phi=0.5, Psi=0.9, T00=0.3)
        
        node.record_state()
        assert len(node.stress_history) == 1
        assert len(node.coherence_history) == 1
        assert node.stress_history[0] == 0.3
        assert node.coherence_history[0] == 0.9


class TestEmotionalNetwork:
    """Test EmotionalNetwork class."""
    
    def setup_method(self):
        """Setup for each test."""
        self.nodes = [
            Node(0, Phi=0.0, Psi=0.95, T00=0.1),
            Node(1, Phi=0.5, Psi=0.85, T00=0.45),
            Node(2, Phi=1.0, Psi=0.70, T00=0.65),
        ]
        self.network = EmotionalNetwork(self.nodes)
        
    def test_get_critical_nodes(self):
        """Test getting critical nodes."""
        critical = self.network.get_critical_nodes(threshold=0.58)
        assert len(critical) == 1
        assert critical[0].id == 2
        
    def test_get_alert_nodes(self):
        """Test getting alert nodes."""
        alert = self.network.get_alert_nodes(threshold=0.40)
        assert len(alert) == 2  # Nodes 1 and 2
        
    def test_network_coherence(self):
        """Test network coherence calculation."""
        Psi_net = self.network.compute_network_coherence()
        expected = np.mean([0.95, 0.85, 0.70])
        np.testing.assert_almost_equal(Psi_net, expected)
        
    def test_collective_phase(self):
        """Test collective phase calculation."""
        phase = self.network.compute_collective_phase()
        assert isinstance(phase, complex)
        assert abs(phase) <= 1.0  # Phase order parameter bounded by 1


class TestCoherentBreathing:
    """Test coherent breathing signal."""
    
    def setup_method(self):
        """Setup for each test."""
        self.protocol = EmotionalSynchronization()
        
    def test_signal_frequency(self):
        """Test signal has correct frequency."""
        # Sample signal over one period
        T = 1.0 / QCAL_FREQUENCY  # Period
        t_values = np.linspace(0, T, 1000)
        signals = [self.protocol.coherent_breathing_signal(t) for t in t_values]
        
        # Signal should complete one full cycle
        # Check that it crosses zero twice (up and down)
        zero_crossings = np.where(np.diff(np.sign(signals)))[0]
        assert len(zero_crossings) >= 2
        
    def test_signal_amplitude(self):
        """Test signal amplitude."""
        t = 0.0
        amplitude = 2.0
        signal = self.protocol.coherent_breathing_signal(t, amplitude)
        
        # At t=0, sin(0) = 0
        np.testing.assert_almost_equal(signal, 0.0)
        
        # Check maximum amplitude
        t_max = 1.0 / (4 * QCAL_FREQUENCY)  # Quarter period
        signal_max = self.protocol.coherent_breathing_signal(t_max, amplitude)
        np.testing.assert_almost_equal(abs(signal_max), amplitude, decimal=2)


class TestIndividualIntervention:
    """Test individual node intervention."""
    
    def setup_method(self):
        """Setup for each test."""
        self.protocol = EmotionalSynchronization()
        
    def test_stress_reduction(self):
        """Test that intervention reduces stress."""
        node = Node(1, Phi=0.5, Psi=0.75, T00=0.60)
        initial_T00 = node.T00
        
        result = self.protocol.apply_coherent_breathing(node, duration=10)
        
        assert result['final_T00'] < initial_T00
        assert result['T00_reduction'] > 0
        
    def test_coherence_increase(self):
        """Test that intervention increases coherence."""
        node = Node(1, Phi=0.5, Psi=0.75, T00=0.60)
        initial_Psi = node.Psi
        
        result = self.protocol.apply_coherent_breathing(node, duration=10)
        
        assert result['final_Psi'] > initial_Psi
        assert result['Psi_increase'] > 0
        
    def test_external_field_injection(self):
        """Test external field injection."""
        node = Node(1, Phi=0.5, Psi=0.75, T00=0.60)
        initial_Phi = node.Phi
        initial_T00 = node.T00
        
        self.protocol.inject_external_field(node, Phi_0=1.0)
        
        # Phi should increase
        assert node.Phi > initial_Phi
        
        # Stress should decrease
        assert node.T00 < initial_T00


class TestPhaseSynchronization:
    """Test phase synchronization protocol."""
    
    def setup_method(self):
        """Setup for each test."""
        self.protocol = EmotionalSynchronization()
        
        # Create network with some critical nodes
        self.nodes = [
            Node(0, Phi=0.0, Psi=0.95, T00=0.1),
            Node(1, Phi=0.5, Psi=0.75, T00=0.65),  # Critical
            Node(2, Phi=1.0, Psi=0.70, T00=0.70),  # Critical
        ]
        
        # Add neighbors
        self.nodes[1].add_neighbor(self.nodes[0])
        self.nodes[2].add_neighbor(self.nodes[0])
        
        self.network = EmotionalNetwork(self.nodes)
        
    def test_synchronization_improves_coherence(self):
        """Test that synchronization improves network coherence."""
        initial_coherence = self.network.compute_network_coherence()
        
        results = self.protocol.synchronize_phase_U(self.network)
        
        assert results['final_coherence'] >= initial_coherence
        
    def test_synchronization_processes_critical_nodes(self):
        """Test that critical nodes are processed."""
        results = self.protocol.synchronize_phase_U(self.network)
        
        # Should process 2 critical nodes (nodes 1 and 2)
        assert results['n_critical_nodes'] == 2
        assert len(results['node_results']) >= 1  # At least one has neighbors


class TestFullProtocol:
    """Test complete synchronization protocol."""
    
    def setup_method(self):
        """Setup for each test."""
        np.random.seed(42)
        self.protocol = EmotionalSynchronization()
        
        # Create network
        N = 10
        self.nodes = []
        for i in range(N):
            Phi = np.random.uniform(-0.5, 0.5)
            Psi = np.random.uniform(0.70, 0.95)
            T00 = np.random.uniform(0.1, 0.7)
            self.nodes.append(Node(i, Phi, Psi, T00))
        
        # Add random connections
        for node in self.nodes:
            n_neighbors = np.random.randint(1, 4)
            neighbors = np.random.choice(self.nodes, n_neighbors, replace=False)
            for neighbor in neighbors:
                if neighbor != node:
                    node.add_neighbor(neighbor)
        
        self.network = EmotionalNetwork(self.nodes)
        
    def test_protocol_returns_results(self):
        """Test that protocol returns complete results."""
        results = self.protocol.full_protocol(self.network)
        
        assert 'initial_coherence' in results
        assert 'final_coherence' in results
        assert 'collective_sovereignty' in results
        assert 'success' in results
        
    def test_protocol_improves_or_maintains_coherence(self):
        """Test that protocol doesn't decrease coherence."""
        initial = self.network.compute_network_coherence()
        
        results = self.protocol.full_protocol(self.network)
        
        # Should improve or at least maintain
        assert results['final_coherence'] >= initial - 0.01  # Small tolerance
        
    def test_sovereignty_index_range(self):
        """Test sovereignty index is in valid range."""
        results = self.protocol.full_protocol(self.network)
        
        S_col = results['collective_sovereignty']
        assert 0.0 <= S_col <= 1.0


class TestMonitoring:
    """Test stabilization monitoring."""
    
    def setup_method(self):
        """Setup for each test."""
        self.protocol = EmotionalSynchronization()
        
    def test_stabilization_detection(self):
        """Test that stabilization is detected."""
        node = Node(1, Phi=0.5, Psi=0.8, T00=0.3)
        
        result = self.protocol.monitor_stabilization(
            node, 
            laplacian_threshold=0.1, 
            max_iterations=100
        )
        
        assert 'stabilized' in result
        assert 'iterations' in result
        assert 'final_laplacian' in result
        
    def test_stabilization_threshold(self):
        """Test stabilization threshold."""
        node = Node(1, Phi=0.5, Psi=0.8, T00=0.3)
        
        result = self.protocol.monitor_stabilization(
            node, 
            laplacian_threshold=0.01,  # Stricter threshold
            max_iterations=100
        )
        
        if result['stabilized']:
            assert result['final_laplacian'] < 0.01


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])
