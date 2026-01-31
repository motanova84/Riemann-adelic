#!/usr/bin/env python3
"""
QCAL-CLOUD Synchronization Validation Test

This script validates that the QCAL-CLOUD synchronization is working correctly.
"""

import json
import sys
from pathlib import Path


def validate_sync_state():
    """Validate synchronization state file exists and is valid"""
    state_file = Path("data/qcal_cloud_sync_state.json")
    
    if not state_file.exists():
        print("❌ Sync state file not found")
        return False
    
    with open(state_file, 'r') as f:
        state = json.load(f)
    
    # Check required fields
    required = ["status", "node_id", "coherence_state", "registry"]
    for field in required:
        if field not in state:
            print(f"❌ Missing field: {field}")
            return False
    
    # Check coherence
    if state["coherence_state"] < 0.999:
        print(f"❌ Coherence too low: {state['coherence_state']}")
        return False
    
    print(f"✅ Sync state valid - Coherence: {state['coherence_state']}")
    return True


def validate_certificate():
    """Validate synchronization certificate"""
    cert_file = Path("data/certificates/qcal_cloud_sync_certificate.json")
    
    if not cert_file.exists():
        print("❌ Certificate not found")
        return False
    
    with open(cert_file, 'r') as f:
        cert = json.load(f)
    
    # Check certificate fields
    if cert.get("certificate_type") != "QCAL-CLOUD-SYNC":
        print("❌ Invalid certificate type")
        return False
    
    if not cert.get("coherence_verified"):
        print("❌ Coherence not verified in certificate")
        return False
    
    print("✅ Certificate valid")
    return True


def validate_qcal_state():
    """Validate QCAL state integration"""
    state_file = Path(".qcal_state.json")
    
    if not state_file.exists():
        print("❌ .qcal_state.json not found")
        return False
    
    with open(state_file, 'r') as f:
        state = json.load(f)
    
    if "qcal_cloud_sync" not in state:
        print("❌ qcal_cloud_sync section not in state")
        return False
    
    sync = state["qcal_cloud_sync"]
    
    # Check sync is active
    if sync.get("status") != "ACTIVE ✓":
        print(f"❌ Sync not active: {sync.get('status')}")
        return False
    
    # Check sync targets
    expected_targets = ["QCAL-CLOUD", "Noesis88", "PI-CODE-NET"]
    if sync.get("sync_targets") != expected_targets:
        print("❌ Incorrect sync targets")
        return False
    
    print("✅ QCAL state integration valid")
    return True


def validate_beacon():
    """Validate beacon updates"""
    beacon_file = Path(".qcal_beacon")
    
    if not beacon_file.exists():
        print("❌ .qcal_beacon not found")
        return False
    
    with open(beacon_file, 'r') as f:
        beacon = f.read()
    
    # Check for sync markers
    if "QCAL-CLOUD Synchronization" not in beacon:
        print("❌ QCAL-CLOUD sync markers not in beacon")
        return False
    
    if "qcal_cloud_sync_status" not in beacon:
        print("❌ Sync status not in beacon")
        return False
    
    print("✅ Beacon updates valid")
    return True


def main():
    """Run all validation tests"""
    print("=" * 60)
    print("🔍 QCAL-CLOUD Synchronization Validation")
    print("=" * 60)
    print()
    
    tests = [
        ("Sync State", validate_sync_state),
        ("Certificate", validate_certificate),
        ("QCAL State", validate_qcal_state),
        ("Beacon", validate_beacon),
    ]
    
    results = []
    for name, test_func in tests:
        print(f"Testing {name}...")
        result = test_func()
        results.append(result)
        print()
    
    print("=" * 60)
    print("📊 Validation Results")
    print("=" * 60)
    print()
    
    passed = sum(results)
    total = len(results)
    
    for i, (name, _) in enumerate(tests):
        status = "✅ PASS" if results[i] else "❌ FAIL"
        print(f"{status} - {name}")
    
    print()
    print(f"Total: {passed}/{total} tests passed")
    
    if passed == total:
        print("\n✅ All validation tests passed!")
        print("∴ QCAL-CLOUD synchronization verified ∞³")
        return 0
    else:
        print(f"\n❌ {total - passed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
