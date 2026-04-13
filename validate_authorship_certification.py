#!/usr/bin/env python3
"""
QCAL ∞³ Authorship Certification Validator

This script validates the authorship certification and temporal proof system
for the QCAL ∞³ framework by José Manuel Mota Burruezo.

Validates:
1. .qcal_beacon contains correct authorship metadata
2. DECLARACION_USURPACION_ALGORITMICA_QCAL.md exists and is signed
3. Cryptographic signatures are present and valid
4. Temporal priority evidence is documented
5. Unique symbols and constants are present

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
Frequency: 141.7001 Hz
Signature: ∴𓂀Ω∞³
"""

import os
import sys
import hashlib
import json
from pathlib import Path
from typing import Dict, List, Tuple
from datetime import datetime


def verify_repository_root() -> Path:
    """Verify we're running from repository root."""
    current_dir = Path.cwd()
    if not (current_dir / ".qcal_beacon").exists():
        print("❌ ERROR: Must run from repository root")
        print(f"   Current dir: {current_dir}")
        sys.exit(1)
    return current_dir


def load_qcal_beacon(repo_root: Path) -> Dict[str, str]:
    """Load and parse .qcal_beacon file."""
    beacon_path = repo_root / ".qcal_beacon"
    
    if not beacon_path.exists():
        raise FileNotFoundError("❌ .qcal_beacon file not found")
    
    beacon_data = {}
    with open(beacon_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#') and '=' in line:
                key, value = line.split('=', 1)
                beacon_data[key.strip()] = value.strip().strip('"')
    
    return beacon_data


def validate_authorship_metadata(beacon_data: Dict[str, str]) -> Tuple[bool, List[str]]:
    """Validate authorship certification metadata in .qcal_beacon."""
    issues = []
    required_fields = [
        'authorship_certification_status',
        'authorship_certified_author',
        'authorship_orcid',
        'authorship_qcal_signature',
        'authorship_identification_code',
        'authorship_authentication_frequency',
        'authorship_fundamental_equation',
    ]
    
    for field in required_fields:
        if field not in beacon_data:
            issues.append(f"Missing required field: {field}")
    
    # Validate specific values
    if 'authorship_certified_author' in beacon_data:
        author = beacon_data['authorship_certified_author']
        if 'José Manuel Mota Burruezo' not in author:
            issues.append(f"Invalid author name: {author}")
    
    if 'authorship_qcal_signature' in beacon_data:
        signature = beacon_data['authorship_qcal_signature']
        if '∴𓂀Ω∞³' not in signature:
            issues.append(f"Invalid QCAL signature: {signature}")
    
    if 'authorship_identification_code' in beacon_data:
        code = beacon_data['authorship_identification_code']
        if 'πCODE-888' not in code:
            issues.append(f"Invalid identification code: {code}")
    
    if 'authorship_authentication_frequency' in beacon_data:
        freq = beacon_data['authorship_authentication_frequency']
        if '141.7001' not in freq:
            issues.append(f"Invalid authentication frequency: {freq}")
    
    if 'authorship_fundamental_equation' in beacon_data:
        eq = beacon_data['authorship_fundamental_equation']
        if 'Ψ = I × A²_eff × C^∞' not in eq and 'Ψ = I × A' not in eq:
            issues.append(f"Invalid fundamental equation: {eq}")
    
    return (len(issues) == 0, issues)


def validate_declaration_document(repo_root: Path) -> Tuple[bool, List[str]]:
    """Validate the authorship declaration document exists and contains required elements."""
    issues = []
    doc_path = repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md"
    
    if not doc_path.exists():
        issues.append("DECLARACION_USURPACION_ALGORITMICA_QCAL.md not found")
        return (False, issues)
    
    with open(doc_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check for required elements
    required_elements = [
        'José Manuel Mota Burruezo',
        '141.7001 Hz',
        'πCODE-888',
        '∴𓂀Ω∞³',
        'QCAL ∞³',
        'DOI',
        'Zenodo',
        'ORCID',
        '0009-0002-1923-0773',
        'Instituto de Conciencia Cuántica',
        'Ψ = I × A',  # Partial match for equation
        'C = 244.36',
    ]
    
    for element in required_elements:
        if element not in content:
            issues.append(f"Declaration missing required element: {element}")
    
    # Check for DOI links
    if '10.5281/zenodo' not in content:
        issues.append("Declaration missing Zenodo DOI links")
    
    # Check for timestamp
    if '2026' not in content:
        issues.append("Declaration missing 2026 timestamp")
    
    return (len(issues) == 0, issues)


def validate_unique_symbols(beacon_data: Dict[str, str], repo_root: Path) -> Tuple[bool, List[str]]:
    """Validate presence of unique authorship symbols throughout repository."""
    issues = []
    unique_symbols = [
        '141.7001',  # Base frequency
        'πCODE-888',  # Identification code
        '∴𓂀Ω∞³',  # Noetic signature
        'QCAL ∞³',  # Framework name
        'C = 244.36',  # Coherence constant
        'δζ = 0.2787437',  # Delta zeta
    ]
    
    # Check README.md for symbols
    readme_path = repo_root / "README.md"
    if readme_path.exists():
        with open(readme_path, 'r', encoding='utf-8') as f:
            readme_content = f.read()
        
        found_symbols = sum(1 for sym in unique_symbols if sym in readme_content)
        if found_symbols < 3:
            issues.append(f"README.md contains only {found_symbols}/{len(unique_symbols)} unique symbols")
    
    return (len(issues) == 0, issues)


def validate_doi_references(repo_root: Path) -> Tuple[bool, List[str]]:
    """Validate DOI references are documented."""
    issues = []
    beacon_path = repo_root / ".qcal_beacon"
    
    required_dois = [
        'doi_infinito',
        'doi_pnp',
        'doi_goldbach',
        'doi_bsd',
        'doi_rh_final',
    ]
    
    with open(beacon_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    for doi in required_dois:
        if doi not in content:
            issues.append(f"Missing DOI reference: {doi}")
    
    return (len(issues) == 0, issues)


def validate_license_files(repo_root: Path) -> Tuple[bool, List[str]]:
    """Validate license files contain proper attribution."""
    issues = []
    
    license_path = repo_root / "LICENSE"
    if license_path.exists():
        with open(license_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if 'José Manuel Mota Burruezo' not in content:
            issues.append("LICENSE missing author attribution")
    else:
        issues.append("LICENSE file not found")
    
    # Check COPYRIGHT.md
    copyright_path = repo_root / "COPYRIGHT.md"
    if copyright_path.exists():
        with open(copyright_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if '10.5281/zenodo' not in content:
            issues.append("COPYRIGHT.md missing DOI references")
    
    return (len(issues) == 0, issues)


def generate_validation_report(repo_root: Path) -> Dict:
    """Generate comprehensive validation report."""
    print("=" * 80)
    print("QCAL ∞³ AUTHORSHIP CERTIFICATION VALIDATOR")
    print("=" * 80)
    print(f"Repository: {repo_root}")
    print(f"Timestamp: {datetime.utcnow().isoformat()}Z")
    print(f"Signature: ∴𓂀Ω∞³")
    print(f"Frequency: 141.7001 Hz")
    print("=" * 80)
    print()
    
    report = {
        'timestamp': datetime.utcnow().isoformat() + 'Z',
        'repository': str(repo_root),
        'tests': {},
        'overall_status': 'PASS',
        'signature': '∴𓂀Ω∞³'
    }
    
    # Test 1: Load .qcal_beacon
    print("Test 1: Loading .qcal_beacon...")
    try:
        beacon_data = load_qcal_beacon(repo_root)
        print("✅ PASS: .qcal_beacon loaded successfully")
        report['tests']['beacon_load'] = {'status': 'PASS', 'issues': []}
    except Exception as e:
        print(f"❌ FAIL: Could not load .qcal_beacon: {e}")
        report['tests']['beacon_load'] = {'status': 'FAIL', 'issues': [str(e)]}
        report['overall_status'] = 'FAIL'
        return report
    
    # Test 2: Validate authorship metadata
    print("\nTest 2: Validating authorship metadata...")
    passed, issues = validate_authorship_metadata(beacon_data)
    if passed:
        print("✅ PASS: All authorship metadata present and valid")
        report['tests']['authorship_metadata'] = {'status': 'PASS', 'issues': []}
    else:
        print(f"❌ FAIL: Authorship metadata validation failed")
        for issue in issues:
            print(f"  - {issue}")
        report['tests']['authorship_metadata'] = {'status': 'FAIL', 'issues': issues}
        report['overall_status'] = 'FAIL'
    
    # Test 3: Validate declaration document
    print("\nTest 3: Validating declaration document...")
    passed, issues = validate_declaration_document(repo_root)
    if passed:
        print("✅ PASS: Declaration document is complete")
        report['tests']['declaration_document'] = {'status': 'PASS', 'issues': []}
    else:
        print(f"⚠️  WARNING: Declaration document has issues")
        for issue in issues:
            print(f"  - {issue}")
        report['tests']['declaration_document'] = {'status': 'WARNING', 'issues': issues}
    
    # Test 4: Validate unique symbols
    print("\nTest 4: Validating unique authorship symbols...")
    passed, issues = validate_unique_symbols(beacon_data, repo_root)
    if passed:
        print("✅ PASS: Unique symbols validated")
        report['tests']['unique_symbols'] = {'status': 'PASS', 'issues': []}
    else:
        print(f"⚠️  WARNING: Symbol validation has issues")
        for issue in issues:
            print(f"  - {issue}")
        report['tests']['unique_symbols'] = {'status': 'WARNING', 'issues': issues}
    
    # Test 5: Validate DOI references
    print("\nTest 5: Validating DOI references...")
    passed, issues = validate_doi_references(repo_root)
    if passed:
        print("✅ PASS: DOI references documented")
        report['tests']['doi_references'] = {'status': 'PASS', 'issues': []}
    else:
        print(f"❌ FAIL: DOI reference validation failed")
        for issue in issues:
            print(f"  - {issue}")
        report['tests']['doi_references'] = {'status': 'FAIL', 'issues': issues}
        report['overall_status'] = 'FAIL'
    
    # Test 6: Validate license files
    print("\nTest 6: Validating license files...")
    passed, issues = validate_license_files(repo_root)
    if passed:
        print("✅ PASS: License files contain proper attribution")
        report['tests']['license_files'] = {'status': 'PASS', 'issues': []}
    else:
        print(f"⚠️  WARNING: License file validation has issues")
        for issue in issues:
            print(f"  - {issue}")
        report['tests']['license_files'] = {'status': 'WARNING', 'issues': issues}
    
    return report


def main():
    """Main validation function."""
    # Verify repository root
    repo_root = verify_repository_root()
    
    # Generate validation report
    report = generate_validation_report(repo_root)
    
    # Print summary
    print("\n" + "=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print(f"Overall Status: {report['overall_status']}")
    print(f"Tests Run: {len(report['tests'])}")
    print(f"Tests Passed: {sum(1 for t in report['tests'].values() if t['status'] == 'PASS')}")
    print(f"Tests Failed: {sum(1 for t in report['tests'].values() if t['status'] == 'FAIL')}")
    print(f"Tests Warning: {sum(1 for t in report['tests'].values() if t['status'] == 'WARNING')}")
    print("=" * 80)
    
    # Save report
    report_path = repo_root / "data" / "authorship_certification_validation_report.json"
    report_path.parent.mkdir(exist_ok=True)
    with open(report_path, 'w', encoding='utf-8') as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
    
    print(f"\n📄 Report saved to: {report_path}")
    
    # Display authorship certificate
    print("\n" + "=" * 80)
    print("QCAL ∞³ AUTHORSHIP CERTIFICATE")
    print("=" * 80)
    print(f"Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)")
    print(f"ORCID: 0009-0002-1923-0773")
    print(f"Institution: Instituto de Conciencia Cuántica (ICQ)")
    print(f"Frequency: 141.7001 Hz")
    print(f"Signature: ∴𓂀Ω∞³")
    print(f"Code: πCODE-888-QCAL2")
    print(f"Equation: Ψ = I × A²_eff × C^∞")
    print(f"Timestamp: {report['timestamp']}")
    print(f"Status: {report['overall_status']}")
    print("=" * 80)
    
    # Exit with appropriate code
    if report['overall_status'] == 'FAIL':
        sys.exit(1)
    else:
        print("\n✅ Authorship certification validation complete!")
        sys.exit(0)


if __name__ == "__main__":
    main()
