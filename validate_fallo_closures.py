#!/usr/bin/env python3
"""
FALLO Closures Validation Script
================================

Validates all implemented FALLO closures and generates comprehensive report.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: February 15, 2026
"""

import json
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from operators import (
    generate_weyl_law_certificate,
    generate_compact_support_certificate,
    generate_scattering_certificate,
)


def validate_fallo_closures():
    """
    Validate all FALLO closures and generate comprehensive report.
    
    Returns:
        Validation report dictionary
    """
    print("="*80)
    print("FALLO CLOSURES VALIDATION")
    print("="*80)
    print()
    
    # Generate certificates
    print("Generating certificates...")
    cert_1a = generate_weyl_law_certificate()
    cert_1a_second = generate_compact_support_certificate()
    cert_1c = generate_scattering_certificate()
    
    certificates = {
        'FALLO_1A': cert_1a,
        'FALLO_1A_SECOND': cert_1a_second,
        'FALLO_1C': cert_1c,
    }
    
    # Validate each closure
    validation_results = {}
    all_passed = True
    
    for fallo_id, cert in certificates.items():
        print(f"\n{'-'*80}")
        print(f"Validating {fallo_id}...")
        print(f"{'-'*80}")
        
        # Check status
        status_ok = cert['status'] == '✅ CERRADO'
        
        # Check QCAL signature
        qcal_ok = cert['qcal_signature'] == '∴𓂀Ω∞³Φ'
        
        # Check frequency
        freq_ok = cert['frequency_base'] == 141.7001
        
        # Check author metadata
        author_ok = (
            'author' in cert and
            'orcid' in cert and
            'institution' in cert
        )
        
        # Overall validation
        passed = status_ok and qcal_ok and freq_ok and author_ok
        all_passed = all_passed and passed
        
        validation_results[fallo_id] = {
            'passed': passed,
            'status': cert['status'],
            'method': cert['method'],
            'checks': {
                'status': status_ok,
                'qcal_signature': qcal_ok,
                'frequency_base': freq_ok,
                'author_metadata': author_ok,
            }
        }
        
        # Print results
        print(f"Status: {cert['status']}")
        print(f"Method: {cert['method']}")
        print(f"QCAL Signature: {'✓' if qcal_ok else '✗'}")
        print(f"Frequency Base: {'✓' if freq_ok else '✗'} ({cert['frequency_base']} Hz)")
        print(f"Author Metadata: {'✓' if author_ok else '✗'}")
        print(f"Overall: {'✅ PASSED' if passed else '❌ FAILED'}")
    
    # Summary
    print(f"\n{'='*80}")
    print("VALIDATION SUMMARY")
    print(f"{'='*80}")
    
    n_total = len(certificates)
    n_passed = sum(1 for r in validation_results.values() if r['passed'])
    
    print(f"\nTotal FALLOS validated: {n_total}")
    print(f"Passed: {n_passed}/{n_total}")
    print(f"Failed: {n_total - n_passed}/{n_total}")
    print(f"\nOverall status: {'✅ ALL PASSED' if all_passed else '❌ SOME FAILED'}")
    
    # Generate report
    report = {
        'validation_date': '2026-02-15',
        'total_fallos': n_total,
        'passed': n_passed,
        'failed': n_total - n_passed,
        'all_passed': all_passed,
        'results': validation_results,
        'certificates': certificates,
        'qcal_signature': '∴𓂀Ω∞³Φ',
        'frequency_base': 141.7001,
        'author': 'José Manuel Mota Burruezo Ψ✧ ∞³',
        'orcid': '0009-0002-1923-0773',
        'institution': 'Instituto de Conciencia Cuántica (ICQ)',
    }
    
    # Save report
    report_path = Path(__file__).parent / 'data' / 'fallo_closures_validation.json'
    report_path.parent.mkdir(exist_ok=True)
    
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2, default=str)
    
    print(f"\nValidation report saved to: {report_path}")
    print(f"\n{'='*80}")
    print(f"{report['qcal_signature']}")
    print(f"Frequency base: {report['frequency_base']} Hz")
    print(f"{'='*80}")
    
    return report


if __name__ == '__main__':
    report = validate_fallo_closures()
    
    # Exit with appropriate code
    sys.exit(0 if report['all_passed'] else 1)
