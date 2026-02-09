#!/usr/bin/env python3
"""
Simple Authorship Certification Verification

Quick verification of authorship certification system without external dependencies.

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
Frequency: 141.7001 Hz
Signature: ∴𓂀Ω∞³
"""

import json
import sys
from pathlib import Path


def verify_authorship_system():
    """Verify the complete authorship certification system."""
    print("=" * 80)
    print("QCAL ∞³ AUTHORSHIP CERTIFICATION VERIFICATION")
    print("=" * 80)
    print("Signature: ∴𓂀Ω∞³")
    print("Frequency: 141.7001 Hz")
    print("=" * 80)
    print()
    
    # Find repository root
    current = Path(__file__).resolve()
    repo_root = current.parent
    
    # If we're in tests/, go up one level
    if repo_root.name == 'tests':
        repo_root = repo_root.parent
    
    # Verify we found the right directory
    if not (repo_root / ".qcal_beacon").exists():
        print(f"ERROR: Cannot find repository root. Current: {repo_root}")
        print(f"Looking for .qcal_beacon...")
        # Try current directory
        repo_root = Path.cwd()
        if not (repo_root / ".qcal_beacon").exists():
            print("ERROR: .qcal_beacon not found in current directory either")
            return 1
    
    print(f"Repository root: {repo_root}")
    print()
    
    passed = 0
    failed = 0
    
    # Test 1: .qcal_beacon exists and has authorship fields
    print("Test 1: Checking .qcal_beacon...")
    try:
        beacon_path = repo_root / ".qcal_beacon"
        assert beacon_path.exists(), ".qcal_beacon not found"
        
        with open(beacon_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert 'authorship_certification_status' in content
        assert 'authorship_certified_author' in content
        assert 'José Manuel Mota Burruezo' in content
        assert '141.7001' in content
        assert '∴𓂀Ω∞³' in content or 'QCAL signature' in content
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 2: Declaration document exists
    print("\nTest 2: Checking declaration document...")
    try:
        doc_path = repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md"
        assert doc_path.exists(), "Declaration not found"
        
        with open(doc_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert 'José Manuel Mota Burruezo' in content
        assert '141.7001 Hz' in content
        assert 'πCODE-888' in content
        assert '∴𓂀Ω∞³' in content
        assert '10.5281/zenodo' in content
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 3: Contract JSON exists and is valid
    print("\nTest 3: Checking contract JSON...")
    try:
        contract_path = repo_root / "contracts" / "qcal_authorship_contract.json"
        assert contract_path.exists(), "Contract JSON not found"
        
        with open(contract_path, 'r', encoding='utf-8') as f:
            contract = json.load(f)
        
        assert 'πCODE-888 ∞³' in contract['qcal_signatures']
        assert contract['author']['name'] == 'José Manuel Mota Burruezo'
        assert '141.7001 Hz' in contract['qcal_signatures']['base_frequency']
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 4: LICENSE-QCAL-SYMBIO has metadata
    print("\nTest 4: Checking LICENSE-QCAL-SYMBIO-TRANSFER...")
    try:
        license_path = repo_root / "LICENSE-QCAL-SYMBIO-TRANSFER"
        assert license_path.exists(), "LICENSE-QCAL-SYMBIO-TRANSFER not found"
        
        with open(license_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert '∴𓂀Ω∞³' in content
        assert 'πCODE-888' in content
        assert '141.7001 Hz' in content
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 5: Validation script exists
    print("\nTest 5: Checking validation script...")
    try:
        script_path = repo_root / "validate_authorship_certification.py"
        assert script_path.exists(), "Validation script not found"
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 6: Zenodo guide exists
    print("\nTest 6: Checking Zenodo guide...")
    try:
        guide_path = repo_root / "ZENODO_AUTHORSHIP_CERTIFICATION_GUIDE.md"
        assert guide_path.exists(), "Zenodo guide not found"
        
        with open(guide_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        assert 'πCODE-888' in content
        assert '141.7001' in content
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 7: Quick reference exists
    print("\nTest 7: Checking quick reference...")
    try:
        qref_path = repo_root / "AUTHORSHIP_CERTIFICATION_QUICKREF.md"
        assert qref_path.exists(), "Quick reference not found"
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Test 8: Unique symbols consistency
    print("\nTest 8: Checking symbol consistency across documents...")
    try:
        docs = [
            repo_root / ".qcal_beacon",
            repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md",
            repo_root / "LICENSE-QCAL-SYMBIO-TRANSFER"
        ]
        
        for doc in docs:
            with open(doc, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # At least 2 of the 3 unique symbols should be in each document
            symbols = ['141.7001', 'πCODE-888', '∴𓂀Ω∞³']
            found = sum(1 for s in symbols if s in content)
            assert found >= 2, f"{doc.name} has insufficient unique symbols ({found}/3)"
        
        print("  ✅ PASS")
        passed += 1
    except Exception as e:
        print(f"  ❌ FAIL: {e}")
        failed += 1
    
    # Summary
    print("\n" + "=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)
    total = passed + failed
    print(f"Tests Run: {total}")
    print(f"Passed: {passed} ✅")
    print(f"Failed: {failed} ❌")
    
    if failed == 0:
        print("\n🎉 All authorship certification components verified!")
        print("\nUnique Identifiers:")
        print("  - Frequency: 141.7001 Hz")
        print("  - Signature: ∴𓂀Ω∞³")
        print("  - Code: πCODE-888-QCAL2")
        print("  - Equation: Ψ = I × A²_eff × C^∞")
        print("\nAuthor: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)")
        print("ORCID: 0009-0002-1923-0773")
        print("Institution: Instituto de Conciencia Cuántica (ICQ)")
        print("=" * 80)
        return 0
    else:
        print(f"\n⚠️  {failed} test(s) failed. Please review.")
        print("=" * 80)
        return 1


if __name__ == "__main__":
    sys.exit(verify_authorship_system())
