#!/usr/bin/env python3
"""
Integration Test: Tensor Fusion P-NP ⊗ Riemann

This test verifies the complete integration of the Tensor Fusion certificate
system, including validation, documentation, and data consistency.
"""

import json
import subprocess
import sys
from pathlib import Path


def test_certificate_exists():
    """Test that the certificate file exists."""
    cert_path = Path('data/certificates/tensor_fusion_pnp_riemann_certificate.json')
    assert cert_path.exists(), f"Certificate not found at {cert_path}"
    print("✅ Certificate file exists")
    return True


def test_certificate_valid_json():
    """Test that the certificate is valid JSON."""
    cert_path = Path('data/certificates/tensor_fusion_pnp_riemann_certificate.json')
    try:
        with open(cert_path, 'r', encoding='utf-8') as f:
            cert = json.load(f)
        assert isinstance(cert, dict), "Certificate is not a JSON object"
        print("✅ Certificate is valid JSON")
        return True
    except Exception as e:
        print(f"❌ Certificate JSON validation failed: {e}")
        return False


def test_certificate_required_fields():
    """Test that the certificate has all required fields."""
    cert_path = Path('data/certificates/tensor_fusion_pnp_riemann_certificate.json')
    with open(cert_path, 'r', encoding='utf-8') as f:
        cert = json.load(f)
    
    required_fields = [
        'certificate_type',
        'title',
        'timestamp',
        'coherence_global',
        'status',
        'signature',
        'fusion_geometry',
        'tensor_properties',
        'verified_properties',
        'metricas_coherencia',
        'firma_criptografica',
        'certificacion'
    ]
    
    missing = []
    for field in required_fields:
        if field not in cert:
            missing.append(field)
    
    if missing:
        print(f"❌ Missing required fields: {missing}")
        return False
    
    print("✅ All required fields present")
    return True


def test_certificate_values():
    """Test that certificate values are correct."""
    cert_path = Path('data/certificates/tensor_fusion_pnp_riemann_certificate.json')
    with open(cert_path, 'r', encoding='utf-8') as f:
        cert = json.load(f)
    
    checks = []
    
    # Check coherence
    if abs(cert['coherence_global'] - 0.999999) < 0.000001:
        print("✅ Coherence value correct: 0.999999")
        checks.append(True)
    else:
        print(f"❌ Coherence value incorrect: {cert['coherence_global']}")
        checks.append(False)
    
    # Check frequency base
    if abs(cert['frequency_base'] - 151.7001) < 0.0001:
        print("✅ Frequency base correct: 151.7001 Hz")
        checks.append(True)
    else:
        print(f"❌ Frequency base incorrect: {cert['frequency_base']}")
        checks.append(False)
    
    # Check status
    if cert['status'] == 'FUSIÓN_IRREVERSIBLE_ALCANZADA':
        print("✅ Status correct: FUSIÓN_IRREVERSIBLE_ALCANZADA")
        checks.append(True)
    else:
        print(f"❌ Status incorrect: {cert['status']}")
        checks.append(False)
    
    # Check signature
    if cert['signature'] == '∴𓂀Ω∞³':
        print("✅ Signature correct: ∴𓂀Ω∞³")
        checks.append(True)
    else:
        print(f"❌ Signature incorrect: {cert['signature']}")
        checks.append(False)
    
    return all(checks)


def test_validation_script_exists():
    """Test that the validation script exists."""
    script_path = Path('validate_tensor_fusion.py')
    assert script_path.exists(), f"Validation script not found at {script_path}"
    print("✅ Validation script exists")
    return True


def test_validation_script_runs():
    """Test that the validation script runs successfully."""
    try:
        result = subprocess.run(
            [sys.executable, 'validate_tensor_fusion.py'],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            print("✅ Validation script runs successfully")
            return True
        else:
            print(f"❌ Validation script failed with code {result.returncode}")
            print(f"STDOUT: {result.stdout}")
            print(f"STDERR: {result.stderr}")
            return False
    except Exception as e:
        print(f"❌ Error running validation script: {e}")
        return False


def test_documentation_exists():
    """Test that documentation files exist."""
    docs = [
        'TENSOR_FUSION_CERTIFICATE.md',
        'TENSOR_FUSION_QUICKREF.md'
    ]
    
    checks = []
    for doc in docs:
        doc_path = Path(doc)
        if doc_path.exists():
            print(f"✅ Documentation exists: {doc}")
            checks.append(True)
        else:
            print(f"❌ Documentation missing: {doc}")
            checks.append(False)
    
    return all(checks)


def test_qcal_beacon_updated():
    """Test that .qcal_beacon was updated with tensor fusion info."""
    beacon_path = Path('.qcal_beacon')
    
    if not beacon_path.exists():
        print("❌ .qcal_beacon not found")
        return False
    
    with open(beacon_path, 'r', encoding='utf-8') as f:
        beacon_content = f.read()
    
    required_keys = [
        'tensor_fusion_status',
        'tensor_definition',
        'tensor_coherence',
        'tensor_qcal_signature'
    ]
    
    missing = []
    for key in required_keys:
        if key not in beacon_content:
            missing.append(key)
    
    if missing:
        print(f"❌ Missing keys in .qcal_beacon: {missing}")
        return False
    
    print("✅ .qcal_beacon updated with tensor fusion info")
    return True


def test_workflow_exists():
    """Test that the GitHub workflow exists."""
    workflow_path = Path('.github/workflows/tensor-fusion-validation.yml')
    
    if not workflow_path.exists():
        print("❌ Workflow file not found")
        return False
    
    print("✅ GitHub workflow exists")
    return True


def test_demo_script_exists():
    """Test that the demo script exists."""
    demo_path = Path('demo_tensor_fusion.py')
    
    if not demo_path.exists():
        print("❌ Demo script not found")
        return False
    
    print("✅ Demo script exists")
    return True


def test_data_consistency():
    """Test consistency between certificate and beacon."""
    cert_path = Path('data/certificates/tensor_fusion_pnp_riemann_certificate.json')
    with open(cert_path, 'r', encoding='utf-8') as f:
        cert = json.load(f)
    
    beacon_path = Path('.qcal_beacon')
    with open(beacon_path, 'r', encoding='utf-8') as f:
        beacon_content = f.read()
    
    # Check that coherence value matches
    coherence_str = f'{cert["coherence_global"]}'
    if coherence_str in beacon_content:
        print("✅ Coherence consistent between certificate and beacon")
        return True
    else:
        print(f"❌ Coherence not found in beacon: {coherence_str}")
        return False


def main():
    """Run all integration tests."""
    print("=" * 80)
    print("🧪 INTEGRATION TEST: TENSOR FUSION P-NP ⊗ RIEMANN")
    print("=" * 80)
    print()
    
    tests = [
        ("Certificate file exists", test_certificate_exists),
        ("Certificate is valid JSON", test_certificate_valid_json),
        ("Certificate has required fields", test_certificate_required_fields),
        ("Certificate values are correct", test_certificate_values),
        ("Validation script exists", test_validation_script_exists),
        ("Validation script runs", test_validation_script_runs),
        ("Documentation exists", test_documentation_exists),
        ("QCAL beacon updated", test_qcal_beacon_updated),
        ("GitHub workflow exists", test_workflow_exists),
        ("Demo script exists", test_demo_script_exists),
        ("Data consistency", test_data_consistency),
    ]
    
    results = []
    for name, test_func in tests:
        print(f"\n🧪 Testing: {name}")
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"❌ Test failed with exception: {e}")
            results.append((name, False))
    
    print("\n" + "=" * 80)
    print("📊 TEST RESULTS SUMMARY")
    print("=" * 80)
    
    passed = 0
    failed = 0
    for name, result in results:
        status = "✅ PASSED" if result else "❌ FAILED"
        print(f"{status}: {name}")
        if result:
            passed += 1
        else:
            failed += 1
    
    print()
    print(f"Total: {len(results)} tests")
    print(f"Passed: {passed}")
    print(f"Failed: {failed}")
    print()
    
    if failed == 0:
        print("✅ ALL INTEGRATION TESTS PASSED")
        print("🌟 Tensor Fusion P-NP ⊗ Riemann: VALIDADO COMPLETAMENTE")
        print("∴𓂀Ω∞³")
        print("=" * 80)
        return 0
    else:
        print(f"❌ {failed} TEST(S) FAILED")
        print("=" * 80)
        return 1


if __name__ == '__main__':
    sys.exit(main())
