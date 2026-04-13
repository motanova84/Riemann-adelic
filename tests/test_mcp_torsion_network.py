"""
Tests for MCP Network Torsion Field
====================================

Tests the torsion field implementation in the MCP network fiber bundle.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
from pathlib import Path
import json
import tempfile

from mcp_network.torsion_field import (
    TorsionTensor,
    FiberConnection,
    TorsionFieldNetwork,
    F0_BASE,
    F0_HARMONIC,
    COHERENCE_C,
    KAPPA_PI
)


class TestTorsionTensor:
    """Test suite for TorsionTensor class."""
    
    def test_torsion_tensor_initialization(self):
        """Test torsion tensor initializes correctly."""
        torsion = TorsionTensor()
        
        assert torsion.components.shape == (3, 3, 3)
        assert torsion.coherence >= 0.0
        assert torsion.coherence <= 1.0
    
    def test_torsion_antisymmetry(self):
        """Test that torsion tensor is antisymmetric: T^α_{βγ} = -T^α_{γβ}"""
        # Create antisymmetric torsion
        components = np.zeros((3, 3, 3))
        for alpha in range(3):
            for beta in range(3):
                for gamma in range(beta + 1, 3):
                    value = np.random.randn()
                    components[alpha, beta, gamma] = value
                    components[alpha, gamma, beta] = -value
        
        torsion = TorsionTensor(components=components)
        
        # Perfect antisymmetry should give coherence = 1.0
        assert torsion.coherence > 0.99
        
        # Verify antisymmetry property
        for alpha in range(3):
            for beta in range(3):
                for gamma in range(3):
                    expected = -components[alpha, gamma, beta]
                    actual = components[alpha, beta, gamma]
                    assert np.isclose(actual, expected, atol=1e-10)
    
    def test_torsion_trace(self):
        """Test torsion trace calculation."""
        components = np.random.randn(3, 3, 3)
        torsion = TorsionTensor(components=components)
        
        # Calculate trace manually
        expected_trace = 0.0
        for alpha in range(3):
            for beta in range(3):
                expected_trace += components[alpha, alpha, beta]
        
        assert np.isclose(torsion.trace, expected_trace, atol=1e-10)


class TestFiberConnection:
    """Test suite for FiberConnection class."""
    
    def test_fiber_connection_initialization(self):
        """Test fiber connection initializes correctly."""
        connection = FiberConnection()
        
        assert connection.christoffel.shape == (3, 3, 3)
        assert len(connection.frequency_sync) == 3
        assert connection.coherence_matrix.shape == (3, 3)
    
    def test_frequency_synchronization(self):
        """Test frequency synchronization."""
        connection = FiberConnection()
        
        # Default frequencies
        assert connection.frequency_sync[0] == F0_BASE
        assert connection.frequency_sync[1] == F0_HARMONIC
        assert connection.frequency_sync[2] == F0_BASE
        
        # Synchronize
        sync_result = connection.synchronize_frequencies()
        
        assert 'frequency_variance' in sync_result
        assert 'sync_quality' in sync_result
        assert 'synchronized' in sync_result
        assert sync_result['sync_quality'] >= 0.0
        assert sync_result['sync_quality'] <= 1.0
    
    def test_christoffel_from_metric(self):
        """Test Christoffel symbol calculation from metric."""
        connection = FiberConnection()
        
        # Simple metric (identity scaled)
        metric = np.eye(3) * COHERENCE_C
        connection.set_christoffel_from_metric(metric)
        
        # Christoffel symbols should be computed
        assert connection.christoffel.shape == (3, 3, 3)
        # For identity metric, connection should be based on frequency differences
        assert not np.all(connection.christoffel == 0)
    
    def test_torsion_calculation(self):
        """Test torsion calculation from connection."""
        connection = FiberConnection()
        
        # Set up metric and connection
        metric = np.eye(3) * COHERENCE_C
        connection.set_christoffel_from_metric(metric)
        
        # Calculate torsion
        torsion = connection.calculate_torsion()
        
        assert isinstance(torsion, TorsionTensor)
        assert torsion.components.shape == (3, 3, 3)
        
        # Torsion should be antisymmetric
        for alpha in range(3):
            for beta in range(3):
                for gamma in range(3):
                    assert np.isclose(
                        torsion.components[alpha, beta, gamma],
                        -torsion.components[alpha, gamma, beta],
                        atol=1e-10
                    )


class TestTorsionFieldNetwork:
    """Test suite for TorsionFieldNetwork class."""
    
    def test_network_initialization(self):
        """Test torsion field network initializes correctly."""
        network = TorsionFieldNetwork()
        
        assert len(network.nodes) == 3
        assert network.nodes[0] == "Riemann-adelic"
        assert network.nodes[1] == "noesis88"
        assert network.nodes[2] == "economia-qcal-nodo-semilla"
        
        assert network.base_metric.shape == (3, 3)
        assert isinstance(network.connection, FiberConnection)
        assert isinstance(network.torsion, TorsionTensor)
    
    def test_qcal_metric_properties(self):
        """Test QCAL metric properties."""
        network = TorsionFieldNetwork()
        metric = network.base_metric
        
        # Metric should be symmetric
        assert np.allclose(metric, metric.T, atol=1e-10)
        
        # Metric should be positive definite (all eigenvalues > 0)
        eigenvalues = np.linalg.eigvalsh(metric)
        assert np.all(eigenvalues > 0)
        
        # Diagonal elements should be based on COHERENCE_C
        assert np.isclose(metric[0, 0], COHERENCE_C, atol=1e-10)
        assert np.isclose(metric[1, 1], COHERENCE_C, atol=1e-10)
        assert np.isclose(metric[2, 2], COHERENCE_C, atol=1e-10)
    
    def test_torsion_coherence_validation(self):
        """Test torsion coherence validation."""
        network = TorsionFieldNetwork()
        validation = network.validate_torsion_coherence()
        
        assert 'torsion_norm' in validation
        assert 'torsion_trace' in validation
        assert 'torsion_coherence' in validation
        assert 'antisymmetry_satisfied' in validation
        assert 'nodes' in validation
        
        # Coherence should be in [0, 1]
        assert validation['torsion_coherence'] >= 0.0
        assert validation['torsion_coherence'] <= 1.0
    
    def test_network_synchronization(self):
        """Test network synchronization."""
        network = TorsionFieldNetwork()
        sync_result = network.synchronize_network()
        
        assert 'frequency_sync' in sync_result
        assert 'torsion_validation' in sync_result
        assert 'synchronized' in sync_result
        assert 'global_coherence' in sync_result
        
        # Global coherence should be in [0, 1]
        assert sync_result['global_coherence'] >= 0.0
        assert sync_result['global_coherence'] <= 1.0
    
    def test_network_certificate_generation(self):
        """Test network certificate generation."""
        network = TorsionFieldNetwork()
        certificate = network.get_network_certificate()
        
        # Check required fields
        assert certificate['certificate_id'] == 'QCAL-TORSION-FIBER-BUNDLE-∞³'
        assert 'timestamp' in certificate
        assert 'timestamp_iso' in certificate
        assert 'nodes' in certificate
        assert 'torsion_coherence' in certificate
        assert 'torsion_trace' in certificate
        assert 'frequency_sync' in certificate
        assert 'synchronized' in certificate
        assert 'global_coherence' in certificate
        
        # Check QCAL foundation
        assert 'qcal_foundation' in certificate
        qcal = certificate['qcal_foundation']
        assert qcal['equation'] == 'Ψ = I × A²_eff × C^∞'
        assert qcal['f0_base'] == F0_BASE
        assert qcal['f0_harmonic'] == F0_HARMONIC
        assert qcal['coherence_C'] == COHERENCE_C
        
        # Check fiber bundle info
        assert 'fiber_bundle' in certificate
        fiber = certificate['fiber_bundle']
        assert 'Riemann-adelic' in fiber['total_space']
        assert 'noesis88' in fiber['total_space']
        assert 'economia-qcal' in fiber['total_space']
        
        # Check author info
        assert 'José Manuel Mota Burruezo' in certificate['author']
        assert certificate['institution'] == 'Instituto de Conciencia Cuántica (ICQ)'
        assert certificate['qcal_signature'] == '∴𓂀Ω∞³'
    
    def test_certificate_json_serializable(self):
        """Test that certificate can be serialized to JSON."""
        network = TorsionFieldNetwork()
        certificate = network.get_network_certificate()
        
        # Should not raise an exception
        json_str = json.dumps(certificate, indent=2, ensure_ascii=False)
        
        # Should be valid JSON
        parsed = json.loads(json_str)
        assert parsed['certificate_id'] == certificate['certificate_id']


class TestTorsionNetworkIntegration:
    """Integration tests for torsion network with MCP servers."""
    
    def test_three_node_configuration(self):
        """Test that network correctly models three nodes."""
        network = TorsionFieldNetwork()
        
        # Should have exactly 3 nodes
        assert len(network.nodes) == 3
        
        # Each node should have a frequency assignment
        assert len(network.connection.frequency_sync) == 3
        
        # Nodes should be: Riemann-adelic, noesis88, economia-qcal-nodo-semilla
        expected_nodes = ["Riemann-adelic", "noesis88", "economia-qcal-nodo-semilla"]
        assert list(network.nodes.values()) == expected_nodes
    
    def test_frequency_assignment_pattern(self):
        """Test frequency assignment follows QCAL pattern."""
        network = TorsionFieldNetwork()
        freqs = network.connection.frequency_sync
        
        # Riemann-adelic should be at base frequency
        assert freqs[0] == F0_BASE
        
        # noesis88 should be at harmonic frequency
        assert freqs[1] == F0_HARMONIC
        
        # economia-qcal should be at base frequency
        assert freqs[2] == F0_BASE
        
        # Two nodes at base, one at harmonic creates the bridge
        base_count = sum(1 for f in freqs.values() if f == F0_BASE)
        harmonic_count = sum(1 for f in freqs.values() if f == F0_HARMONIC)
        
        assert base_count == 2
        assert harmonic_count == 1
    
    def test_global_coherence_computation(self):
        """Test global coherence combines multiple metrics."""
        network = TorsionFieldNetwork()
        sync_result = network.synchronize_network()
        
        global_coherence = sync_result['global_coherence']
        freq_quality = sync_result['frequency_sync']['sync_quality']
        torsion_coherence = sync_result['torsion_validation']['torsion_coherence']
        
        # Global coherence should be average of frequency and torsion coherence
        expected = (freq_quality + torsion_coherence) / 2.0
        assert np.isclose(global_coherence, expected, atol=1e-10)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
