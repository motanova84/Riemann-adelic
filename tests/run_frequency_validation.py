#!/usr/bin/env python3
"""
Standalone Frequency Validation Executable

Demonstrates the complete dual EEG-LIGO validation process for
f₀ = 141.7001 Hz as the consciousness activation frequency.

This script can be run independently to verify the experimental validation
framework and generate validation reports.

Usage:
    python tests/run_frequency_validation.py
    python tests/run_frequency_validation.py --duration 5.0 --channels 128
    python tests/run_frequency_validation.py --bootstrap 200 --verbose

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import sys
import os
import argparse
import json
from datetime import datetime
import numpy as np

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from experiments.frequency_activation_validator import (
    FrequencyActivationValidator,
    SystemParameters,
    F0
)


def parse_arguments():
    """
    Parse command-line arguments.
    
    Returns:
        Parsed arguments
    """
    parser = argparse.ArgumentParser(
        description="Dual EEG-LIGO Frequency Activation Validation",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    
    # System parameters
    parser.add_argument(
        '--duration',
        type=float,
        default=10.0,
        help='Data duration in seconds'
    )
    
    parser.add_argument(
        '--channels',
        type=int,
        default=256,
        help='Number of EEG channels'
    )
    
    parser.add_argument(
        '--bootstrap',
        type=int,
        default=100,
        help='Number of bootstrap iterations'
    )
    
    parser.add_argument(
        '--frequency',
        type=float,
        default=F0,
        help='Target frequency to validate (Hz)'
    )
    
    # Output options
    parser.add_argument(
        '--output',
        type=str,
        default=None,
        help='Output JSON file for results'
    )
    
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Print detailed output'
    )
    
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Suppress output (only write to file)'
    )
    
    return parser.parse_args()


def validation_result_to_dict(result):
    """
    Convert ValidationResult to dictionary for JSON serialization.
    
    Args:
        result: ValidationResult object
        
    Returns:
        Dictionary representation
    """
    return {
        'system_name': result.system_name,
        'detected_frequency': float(result.detected_frequency),
        'target_frequency': float(result.target_frequency),
        'coherence': float(result.coherence),
        'snr_db': float(result.snr_db),
        'p_value': float(result.p_value),
        'confidence_interval': [float(result.confidence_interval[0]), 
                               float(result.confidence_interval[1])],
        'passed': bool(result.passed)
    }


def save_results(results, output_file):
    """
    Save validation results to JSON file.
    
    Args:
        results: Validation results dictionary
        output_file: Output file path
    """
    # Convert results to serializable format
    output_data = {
        'timestamp': datetime.now().isoformat(),
        'eeg': validation_result_to_dict(results['eeg']),
        'ligo': validation_result_to_dict(results['ligo']),
        'cross_correlation': {
            'correlation': float(results['cross_correlation']['correlation']),
            'p_value': float(results['cross_correlation']['p_value']),
            't_statistic': float(results['cross_correlation']['t_statistic']),
            'n_samples': int(results['cross_correlation']['n_samples'])
        },
        'overall_passed': bool(results['overall_passed'])
    }
    
    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")


def print_summary(results, verbose=False):
    """
    Print validation summary.
    
    Args:
        results: Validation results
        verbose: Print detailed information
    """
    print("\n" + "="*70)
    print("FREQUENCY ACTIVATION VALIDATION SUMMARY")
    print("="*70)
    
    eeg = results['eeg']
    ligo = results['ligo']
    cc = results['cross_correlation']
    
    print(f"\nTarget Frequency: {eeg.target_frequency:.4f} Hz")
    print(f"\nEEG Detection:")
    print(f"  Frequency: {eeg.detected_frequency:.2f} Hz")
    print(f"  Coherence: {eeg.coherence:.3f}")
    print(f"  SNR:       {eeg.snr_db:.2f} dB")
    print(f"  p-value:   {eeg.p_value:.6f}")
    print(f"  Status:    {'✅ PASS' if eeg.passed else '❌ FAIL'}")
    
    print(f"\nLIGO Detection:")
    print(f"  Frequency: {ligo.detected_frequency:.2f} Hz")
    print(f"  Coherence: {ligo.coherence:.3f}")
    print(f"  SNR:       {ligo.snr_db:.2f} dB")
    print(f"  p-value:   {ligo.p_value:.6f}")
    print(f"  Status:    {'✅ PASS' if ligo.passed else '❌ FAIL'}")
    
    print(f"\nCross-System Correlation:")
    print(f"  r = {cc['correlation']:.4f}")
    print(f"  p = {cc['p_value']:.6f}")
    
    print(f"\n{'='*70}")
    print(f"OVERALL: {'✅ VALIDATION PASSED' if results['overall_passed'] else '❌ VALIDATION FAILED'}")
    print(f"{'='*70}\n")
    
    if verbose:
        print("\nDetailed Statistics:")
        print(f"\nEEG:")
        print(f"  Confidence Interval: [{eeg.confidence_interval[0]:.2f}, {eeg.confidence_interval[1]:.2f}] dB")
        
        print(f"\nLIGO:")
        print(f"  Confidence Interval: [{ligo.confidence_interval[0]:.2f}, {ligo.confidence_interval[1]:.2f}] dB")
        
        print(f"\nCross-Correlation:")
        print(f"  t-statistic: {cc['t_statistic']:.2f}")
        print(f"  n_samples:   {cc['n_samples']}")
        print()


def main():
    """Main execution function."""
    args = parse_arguments()
    
    # Create system parameters
    params = SystemParameters(
        f0=args.frequency,
        duration=args.duration,
        eeg_channels=args.channels,
        n_bootstrap=args.bootstrap
    )
    
    if not args.quiet:
        print("="*70)
        print("DUAL EEG-LIGO FREQUENCY ACTIVATION VALIDATION")
        print("="*70)
        print(f"\nParameters:")
        print(f"  Target Frequency: {args.frequency:.4f} Hz")
        print(f"  Duration:         {args.duration} s")
        print(f"  EEG Channels:     {args.channels}")
        print(f"  Bootstrap:        {args.bootstrap} iterations")
        print()
    
    # Create validator
    validator = FrequencyActivationValidator(params)
    
    # Run validation
    if not args.quiet:
        print("Running validation...")
    
    results = validator.run()
    
    # Print results
    if not args.quiet:
        if args.verbose:
            # Detailed output from validator
            validator.print_results(results)
        else:
            # Summary output
            print_summary(results, verbose=args.verbose)
    
    # Save to file if requested
    if args.output:
        save_results(results, args.output)
    
    # Return exit code based on validation result
    return 0 if results['overall_passed'] else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\nValidation interrupted by user.")
        sys.exit(130)
    except Exception as e:
        print(f"\n\nERROR: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(1)
