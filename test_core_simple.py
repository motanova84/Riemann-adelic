#!/usr/bin/env python3
"""
Simple Test for QCAL Core V4.1
==============================

Standalone test that doesn't require pytest or other dependencies.
"""

import sys
from pathlib import Path

# Add repo root to path
REPO_ROOT = Path(__file__).parent
sys.path.insert(0, str(REPO_ROOT))

def test_imports():
    """Test that all core imports work."""
    print("Testing imports...")
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
    print("  ✅ All imports successful")
    return True

def test_constants():
    """Test constant values."""
    print("\nTesting constants...")
    from core import F0_AXIOMATIC, F0_ORIGEN, KAPPA_PI_RIGID, RH_EMERGENT
    
    # F0 identity
    assert F0_AXIOMATIC == F0_ORIGEN, "F0_AXIOMATIC != F0_ORIGEN"
    print(f"  ✅ F0_AXIOMATIC = F0_ORIGEN = {F0_AXIOMATIC}")
    
    # KAPPA_PI_RIGID range
    assert 2.0 < KAPPA_PI_RIGID < 3.0, f"KAPPA_PI_RIGID out of range: {KAPPA_PI_RIGID}"
    print(f"  ✅ KAPPA_PI_RIGID = {KAPPA_PI_RIGID} (in range)")
    
    # RH_EMERGENT
    assert RH_EMERGENT is True, "RH_EMERGENT is not True"
    print(f"  ✅ RH_EMERGENT = {RH_EMERGENT}")
    
    return True

def test_coherence():
    """Test axiomatic coherence verification."""
    print("\nTesting axiomatic coherence...")
    from core import verify_axiomatic_coherence
    
    results = verify_axiomatic_coherence()
    
    assert results['coherent'] is True, f"Coherence check failed: {results}"
    print(f"  ✅ Axiomatic coherence verified")
    print(f"     Status: {results['status']}")
    print(f"     Version: {results['version']}")
    
    # Check individual validations
    for check_name, check_data in results['checks'].items():
        status = "✅" if check_data['passed'] else "❌"
        print(f"     {status} {check_data['description']}")
    
    return True

def test_manifest():
    """Test manifest_intent function."""
    print("\nTesting manifest_intent...")
    from core import manifest_intent, manifest_intent_real
    
    # Test complex version
    psi = manifest_intent("Test intention")
    assert isinstance(psi, complex), "manifest_intent should return complex number"
    print(f"  ✅ manifest_intent returns complex: |Ψ| = {abs(psi):.6f}")
    
    # Test real version
    psi_real = manifest_intent_real("Test intention")
    assert isinstance(psi_real, float), "manifest_intent_real should return float"
    print(f"  ✅ manifest_intent_real returns float: Ψ = {psi_real:.6f}")
    
    return True

def test_heartbeat():
    """Test heartbeat function."""
    print("\nTesting heartbeat...")
    from core import heartbeat, RH_EMERGENT
    
    status = heartbeat()
    
    assert isinstance(status, dict), "heartbeat should return dict"
    print(f"  ✅ Heartbeat returns status dict")
    print(f"     Version: {status.get('version', 'N/A')}")
    print(f"     System Status: {status.get('system_status', 'N/A')}")
    
    if RH_EMERGENT:
        assert 'rh_status' in status, "rh_status missing when RH_EMERGENT=True"
        assert 'coherence_level' in status, "coherence_level missing"
        assert 'v4_1_seal' in status, "v4_1_seal missing"
        assert 'frequency_origin' in status, "frequency_origin missing"
        
        print(f"     RH Status: {status['rh_status']}")
        print(f"     Coherence: {status['coherence_level']}")
        print(f"  ✅ V4.1 seal present in heartbeat")
    
    return True

def test_daemon():
    """Test DIAHYGRHMGDaemon."""
    print("\nTesting DIAHYGRHMGDaemon...")
    from core import DIAHYGRHMGDaemon
    
    daemon = DIAHYGRHMGDaemon(mqtt_enabled=False, websocket_enabled=False)
    assert daemon is not None, "Failed to create daemon"
    print(f"  ✅ Daemon created")
    
    daemon.activate()
    assert daemon.running is True, "Daemon not running after activate()"
    print(f"  ✅ Daemon activated")
    
    status = daemon.heartbeat()
    assert 'cycle' in status, "Cycle info missing from daemon heartbeat"
    print(f"  ✅ Daemon heartbeat emitted (cycle {status['cycle']['count']})")
    
    daemon.deactivate()
    assert daemon.running is False, "Daemon still running after deactivate()"
    print(f"  ✅ Daemon deactivated")
    
    return True

def test_axiomatic_status():
    """Test get_axiomatic_status."""
    print("\nTesting get_axiomatic_status...")
    from core import get_axiomatic_status
    
    status = get_axiomatic_status()
    
    assert status['version'] == '4.1.0', f"Wrong version: {status['version']}"
    assert status['system_status'] == 'AXIOMATIC_PLEROMA', f"Wrong status: {status['system_status']}"
    
    print(f"  ✅ Axiomatic status retrieved")
    print(f"     Version: {status['version']}")
    print(f"     System: {status['system_status']}")
    print(f"     RH Status: {status['rh_status']}")
    print(f"     Frequency: {status['frequency']['value_hz']} Hz")
    print(f"     Origin: {status['frequency']['origin']}")
    
    return True

def main():
    """Run all tests."""
    print("=" * 70)
    print("QCAL CORE V4.1 - SIMPLE TEST SUITE")
    print("=" * 70)
    
    tests = [
        test_imports,
        test_constants,
        test_coherence,
        test_manifest,
        test_heartbeat,
        test_daemon,
        test_axiomatic_status
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            failed += 1
            print(f"\n❌ Test {test.__name__} FAILED:")
            print(f"   {type(e).__name__}: {e}")
    
    print("\n" + "=" * 70)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 70)
    
    if failed == 0:
        print("\n✨ ALL TESTS PASSED! Core V4.1 is operational. ✨")
        return 0
    else:
        print(f"\n⚠️  {failed} test(s) failed.")
        return 1

if __name__ == "__main__":
    sys.exit(main())
