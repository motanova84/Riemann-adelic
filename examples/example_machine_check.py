#!/usr/bin/env python3
"""
Example: Programmatic Usage of Machine-Check Verification System

This example demonstrates how to use the machine-check verification system
programmatically in your own Python scripts.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from machine_check_verification import MachineCheckVerifier


def example_basic_verification():
    """Example 1: Basic verification"""
    print("=" * 80)
    print("EXAMPLE 1: Basic Verification")
    print("=" * 80)
    
    # Create verifier with standard precision
    verifier = MachineCheckVerifier(precision=30, verbose=False)
    
    # Run individual verifications
    print("\n1. Verifying QCAL Coherence...")
    qcal_result = verifier.verify_qcal_coherence()
    print(f"   Result: {'✅ PASSED' if qcal_result else '❌ FAILED'}")
    
    print("\n2. Verifying Numerical Precision...")
    precision_result = verifier.verify_numerical_precision()
    print(f"   Result: {'✅ PASSED' if precision_result else '❌ FAILED'}")
    
    print("\n3. Verifying Spectral Properties...")
    spectral_result = verifier.verify_spectral_properties()
    print(f"   Result: {'✅ PASSED' if spectral_result else '❌ FAILED'}")
    
    # Access detailed results
    print("\n4. Detailed Results:")
    for key, value in verifier.results.items():
        status = value.get('status', 'UNKNOWN')
        print(f"   {key}: {status}")


def example_comprehensive_verification():
    """Example 2: Comprehensive verification with certificate"""
    print("\n" + "=" * 80)
    print("EXAMPLE 2: Comprehensive Verification with Certificate")
    print("=" * 80)
    
    # Create verifier with verbose logging
    verifier = MachineCheckVerifier(precision=30, verbose=True)
    
    # Run comprehensive verification
    print("\nRunning comprehensive verification...\n")
    results = verifier.run_comprehensive_verification()
    
    # Print summary
    print("\n" + "=" * 80)
    print("VERIFICATION RESULTS SUMMARY")
    print("=" * 80)
    print(f"Overall Status: {results['overall_status']}")
    print(f"Total Verifications: {results['summary']['total']}")
    print(f"Passed: {results['summary']['passed']}")
    print(f"Failed: {results['summary']['failed']}")
    print(f"Skipped: {results['summary']['skipped']}")
    print(f"Execution Time: {results['execution_time']:.3f} seconds")
    
    # Generate certificate
    print("\nGenerating certificate...")
    certificate = verifier.generate_certificate(
        results,
        output_path='/tmp/example_certificate.json'
    )
    
    if certificate:
        print("✅ Certificate generated successfully!")
        print(f"   Type: {certificate['certificate_type']}")
        print(f"   Version: {certificate['version']}")
        print(f"   Status: {certificate['riemann_hypothesis_status']}")


def example_custom_verification():
    """Example 3: Custom verification with specific checks"""
    print("\n" + "=" * 80)
    print("EXAMPLE 3: Custom Verification Workflow")
    print("=" * 80)
    
    # Create verifier with high precision
    verifier = MachineCheckVerifier(precision=50, verbose=False)
    
    print("\nCustom verification workflow:")
    
    # Step 1: Critical checks
    print("\n1. Running critical checks...")
    critical_checks = [
        ('QCAL Coherence', verifier.verify_qcal_coherence),
        ('Numerical Precision', verifier.verify_numerical_precision)
    ]
    
    all_critical_passed = True
    for name, check_func in critical_checks:
        result = check_func()
        status = '✅ PASSED' if result else '❌ FAILED'
        print(f"   {name}: {status}")
        if not result:
            all_critical_passed = False
    
    if not all_critical_passed:
        print("\n❌ Critical checks failed! Stopping verification.")
        return
    
    # Step 2: Optional checks
    print("\n2. Running optional checks...")
    optional_checks = [
        ('Spectral Properties', verifier.verify_spectral_properties),
        ('Mathematical Certificates', verifier.verify_mathematical_certificates)
    ]
    
    for name, check_func in optional_checks:
        try:
            result = check_func()
            status = '✅ PASSED' if result else '⚠️ WARNING'
            print(f"   {name}: {status}")
        except Exception as e:
            print(f"   {name}: ⚠️ SKIPPED ({e})")
    
    # Step 3: Summary
    print("\n3. Verification complete!")
    print(f"   Precision used: {verifier.precision} decimal places")
    print(f"   QCAL Coherence: {verifier.qcal_config['coherence']}")
    print(f"   Base Frequency: {verifier.qcal_config['base_frequency']} Hz")


def example_error_handling():
    """Example 4: Error handling and graceful degradation"""
    print("\n" + "=" * 80)
    print("EXAMPLE 4: Error Handling")
    print("=" * 80)
    
    verifier = MachineCheckVerifier(precision=25, verbose=False)
    
    print("\nDemonstrating graceful error handling:")
    
    # Attempt verification with error handling
    checks = [
        ('V5 Coronación', verifier.verify_v5_coronacion),
        ('Adelic Structure', verifier.verify_adelic_structure),
        ('YOLO Integration', verifier.verify_yolo_integration)
    ]
    
    for name, check_func in checks:
        try:
            print(f"\nTrying {name}...")
            result = check_func()
            
            # Get status from results
            result_key = name.lower().replace(' ', '_').replace('ó', 'o')
            status = verifier.results.get(result_key, {}).get('status', 'UNKNOWN')
            
            if status == 'PASSED':
                print(f"   ✅ {name}: Available and passed")
            elif status in ['SKIPPED', 'WARNING']:
                print(f"   ⚠️  {name}: Not available, continuing...")
            else:
                print(f"   ⚠️  {name}: {status}")
                
        except Exception as e:
            print(f"   ⚠️  {name}: Exception caught: {e}")
            print("      Verification continues despite error")
    
    print("\n✅ Verification completed with graceful error handling")


def example_results_analysis():
    """Example 5: Analyzing verification results"""
    print("\n" + "=" * 80)
    print("EXAMPLE 5: Results Analysis")
    print("=" * 80)
    
    verifier = MachineCheckVerifier(precision=30, verbose=False)
    
    # Run verification
    print("\nRunning verification for analysis...")
    results = verifier.run_comprehensive_verification()
    
    # Analyze results
    print("\n" + "=" * 80)
    print("DETAILED RESULTS ANALYSIS")
    print("=" * 80)
    
    # 1. Verification status breakdown
    print("\n1. Verification Status Breakdown:")
    status_counts = {}
    for v in results['verifications']:
        status = v['status']
        status_counts[status] = status_counts.get(status, 0) + 1
    
    for status, count in sorted(status_counts.items()):
        print(f"   {status}: {count}")
    
    # 2. Critical verifications
    print("\n2. Critical Verifications:")
    critical_names = ['QCAL Coherence', 'Numerical Precision']
    for v in results['verifications']:
        if v['name'] in critical_names:
            print(f"   {v['name']}: {v['status']}")
    
    # 3. Performance metrics
    print("\n3. Performance Metrics:")
    print(f"   Total Execution Time: {results['execution_time']:.3f}s")
    if 'detailed_results' in results:
        for key, value in results['detailed_results'].items():
            if 'execution_time' in value:
                print(f"   {key}: {value['execution_time']:.3f}s")
    
    # 4. QCAL configuration
    print("\n4. QCAL Configuration:")
    config = results['qcal_config']
    print(f"   Base Frequency: {config['base_frequency']} Hz")
    print(f"   Coherence: {config['coherence']}")
    print(f"   Critical Line: {config['critical_line']}")
    print(f"   Precision: {config['precision']} dps")
    
    # 5. Recommendation
    print("\n5. Recommendation:")
    if results['overall_status'] == 'PASSED':
        print("   ✅ All critical verifications passed")
        print("   👍 System is ready for production use")
    elif results['overall_status'] == 'PARTIAL':
        print("   ⚠️  Some non-critical verifications need attention")
        print("   👍 System is usable but review warnings")
    else:
        print("   ❌ Critical verifications failed")
        print("   ⚠️  System needs attention before use")


def main():
    """Run all examples"""
    print("\n" + "🤖" * 40)
    print("MACHINE-CHECK VERIFICATION SYSTEM - EXAMPLES")
    print("🤖" * 40)
    
    examples = [
        example_basic_verification,
        example_comprehensive_verification,
        example_custom_verification,
        example_error_handling,
        example_results_analysis
    ]
    
    for i, example in enumerate(examples, 1):
        try:
            example()
        except Exception as e:
            print(f"\n❌ Example {i} failed: {e}")
            import traceback
            traceback.print_exc()
    
    print("\n" + "=" * 80)
    print("ALL EXAMPLES COMPLETED")
    print("=" * 80)
    print("\n✨ Thank you for using the Machine-Check Verification System!")
    print("♾️  QCAL ∞³ — Instituto de Conciencia Cuántica (ICQ)")
    print("=" * 80 + "\n")


if __name__ == '__main__':
    main()
