#!/usr/bin/env python3
"""
Test Suite for QCAL Core V4.1 Axiomatic Framework
=================================================

Tests for the core module implementing RAM-IX axiomatic integration.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Version: V4.1
Date: 2026-01-10
"""

import pytest
import sys
from pathlib import Path

# Añadir raíz del repositorio al path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from core import (
    F0_ORIGEN,
    F0_AXIOMATIC,
    KAPPA_PI_RIGID,
    RH_EMERGENT,
    C_PRIMARY,
    C_COHERENCE,
    PSI_EQUATION,
    verify_axiomatic_coherence,
    get_axiomatic_status,
    manifest_intent,
    manifest_intent_real,
    heartbeat,
    DIAHYGRHMGDaemon
)


class TestAxiomaticConstants:
    """Tests for axiomatic constants."""
    
    def test_f0_identity(self):
        """Test that F0_AXIOMATIC equals F0_ORIGEN (identity, not approximation)."""
        assert F0_AXIOMATIC == F0_ORIGEN
        assert abs(F0_AXIOMATIC - F0_ORIGEN) < 1e-15
    
    def test_f0_precision(self):
        """Test that F0 has the correct high precision value."""
        expected_f0 = 141.700010083578160030654028447231151926974628612204
        assert abs(F0_AXIOMATIC - expected_f0) < 1e-10
    
    def test_kappa_pi_rigid(self):
        """Test that KAPPA_PI_RIGID is in expected range."""
        assert KAPPA_PI_RIGID == 2.578208
        assert 2.0 < KAPPA_PI_RIGID < 3.0
    
    def test_rh_emergent(self):
        """Test that RH_EMERGENT is True (axiometric state)."""
        assert RH_EMERGENT is True
    
    def test_spectral_constants(self):
        """Test spectral constants values."""
        assert C_PRIMARY == 629.83
        assert C_COHERENCE == 244.36
        
        # Test coherence factor
        coherence_factor = C_COHERENCE / C_PRIMARY
        assert 0.385 < coherence_factor < 0.390
    
    def test_psi_equation(self):
        """Test that PSI equation is defined correctly."""
        assert PSI_EQUATION == "Ψ = I × A_eff² × C^∞"


class TestAxiomaticCoherence:
    """Tests for axiomatic coherence verification."""
    
    def test_verify_axiomatic_coherence(self):
        """Test that axiomatic coherence verification passes."""
        results = verify_axiomatic_coherence()
        
        assert results['coherent'] is True
        assert results['status'] == 'AXIOMATIC_PLEROMA'
        assert results['version'] == '4.1.0'
        
        # Check individual validations
        assert results['checks']['f0_identity']['passed'] is True
        assert results['checks']['kappa_rigid']['passed'] is True
        assert results['checks']['rh_emergent']['passed'] is True
        assert results['checks']['coherence_level']['passed'] is True
        assert results['checks']['coherence_factor']['passed'] is True
    
    def test_get_axiomatic_status(self):
        """Test getting axiomatic status."""
        status = get_axiomatic_status()
        
        assert status['version'] == '4.1.0'
        assert status['system_status'] == 'AXIOMATIC_PLEROMA'
        assert status['rh_emergent'] is True
        assert 'All non-trivial zeros on Re(s)=1/2' in status['rh_status']
        
        # Check frequency information
        assert status['frequency']['value_hz'] == F0_AXIOMATIC
        assert 'Deducida por rigidez global' in status['frequency']['origin']
        assert status['frequency']['nature'] == 'Axiomática (no observada)'
        
        # Check constants
        assert status['constants']['kappa_pi_rigid'] == KAPPA_PI_RIGID
        assert status['constants']['c_primary'] == C_PRIMARY
        assert status['constants']['c_coherence'] == C_COHERENCE


class TestManifestIntent:
    """Tests for manifest_intent function."""
    
    def test_manifest_intent_basic(self):
        """Test basic manifest_intent functionality."""
        psi = manifest_intent("Test intention")
        
        # Should return a complex number
        assert isinstance(psi, complex)
        
        # Magnitude should be positive
        assert abs(psi) > 0
    
    def test_manifest_intent_with_love(self):
        """Test manifest_intent with different love_effective values."""
        psi1 = manifest_intent("Intention 1", love_effective=1.0)
        psi2 = manifest_intent("Intention 2", love_effective=2.0)
        
        # Higher love_effective should give larger magnitude
        assert abs(psi2) > abs(psi1)
    
    def test_manifest_intent_real(self):
        """Test manifest_intent_real (amplitude only)."""
        psi_real = manifest_intent_real("Test intention")
        
        # Should return a float
        assert isinstance(psi_real, float)
        
        # Should be positive
        assert psi_real > 0
    
    def test_manifest_intent_axiomatic_correction(self):
        """Test that axiomatic correction is applied when RH_EMERGENT."""
        import numpy as np
        
        # Base value without correction
        base_love = 1.0
        base_psi = np.pi * (base_love ** 2)
        
        # With axiomatic correction
        psi_real = manifest_intent_real("Test", love_effective=base_love)
        
        if RH_EMERGENT:
            # Should have small correction applied
            expected_correction = 1.0 + (KAPPA_PI_RIGID * 1e-6)
            expected_psi = base_psi * expected_correction
            assert abs(psi_real - expected_psi) < 1e-10


class TestHeartbeat:
    """Tests for heartbeat function."""
    
    def test_heartbeat_returns_status(self):
        """Test that heartbeat returns proper status dictionary."""
        status = heartbeat()
        
        assert isinstance(status, dict)
        assert 'version' in status
        assert 'system_status' in status
        assert 'rh_emergent' in status
    
    def test_heartbeat_v4_1_seal(self):
        """Test that heartbeat includes V4.1 seal when RH_EMERGENT."""
        status = heartbeat()
        
        if RH_EMERGENT:
            assert 'rh_status' in status
            assert 'All non-trivial zeros on Re(s)=1/2' in status['rh_status']
            assert 'emergent identity' in status['rh_status']
            
            assert 'coherence_level' in status
            assert 'AXIOMATIC PLEROMA' in status['coherence_level']
            
            assert 'v4_1_seal' in status
            assert 'SafeCreative' in status['v4_1_seal']
            
            assert 'frequency_origin' in status
            assert 'rigidez global' in status['frequency_origin']


class TestDaemon:
    """Tests for DIAHYGRHMGDaemon."""
    
    def test_daemon_creation(self):
        """Test that daemon can be created."""
        daemon = DIAHYGRHMGDaemon(mqtt_enabled=False, websocket_enabled=False)
        assert daemon is not None
        assert daemon.running is False
    
    def test_daemon_activation(self):
        """Test daemon activation."""
        daemon = DIAHYGRHMGDaemon(mqtt_enabled=False, websocket_enabled=False)
        daemon.activate()
        
        assert daemon.running is True
        assert daemon.seal is not None
        assert daemon.cycle_count == 0
        
        daemon.deactivate()
        assert daemon.running is False
    
    def test_daemon_heartbeat(self):
        """Test daemon heartbeat emission."""
        daemon = DIAHYGRHMGDaemon(mqtt_enabled=False, websocket_enabled=False)
        daemon.activate()
        
        status = daemon.heartbeat()
        
        assert isinstance(status, dict)
        assert 'cycle' in status
        assert status['cycle']['count'] == 1
        
        # Second heartbeat should increment count
        status2 = daemon.heartbeat()
        assert status2['cycle']['count'] == 2
        
        daemon.deactivate()


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "-s"])
