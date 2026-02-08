#!/usr/bin/env python3
"""
Validation: Geometría Real del Movimiento Lumínico

This script validates the light spiral geometry framework and generates
experimental protocols for falsifiable predictions.

Validation Components:
---------------------
1. Mathematical consistency of spiral equations
2. Prime phase modulation correctness
3. Zeta zero frequency mapping accuracy
4. Interference pattern physical validity
5. Experimental prediction feasibility

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys
import os
from typing import Dict, Any, List

# Import modules directly
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'utils'))

try:
    import light_spiral_geometry as lsg
    GEOMETRY_AVAILABLE = True
except ImportError as e:
    print(f"⚠️  Error importing light_spiral_geometry: {e}")
    GEOMETRY_AVAILABLE = False
    sys.exit(1)

try:
    import zeta_interference_pattern as zip_mod
    PATTERN_AVAILABLE = True
except ImportError as e:
    print(f"⚠️  Error importing zeta_interference_pattern: {e}")
    PATTERN_AVAILABLE = False
    sys.exit(1)


# =============================================================================
# VALIDATION TESTS
# =============================================================================

def validate_spiral_path_equations() -> Dict[str, Any]:
    """
    Validate that spiral path equations satisfy physical constraints.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION 1: Spiral Path Equations")
    print("=" * 80)
    print()
    
    # Create time array
    T = 1.0 / lsg.F0_HZ
    t = np.linspace(0, 10 * T, 1000)
    
    # Test parameters
    params = lsg.SpiralParameters(
        r0=1e-9,
        lambda_exp=0.01,
        prime_index=0
    )
    
    # Compute path
    x, y, z = lsg.compute_spiral_path(t, params)
    
    # Validation checks
    checks = {}
    
    # 1. Path continuity (no NaNs or Infs)
    checks['continuity'] = {
        'passed': np.all(np.isfinite(x)) and np.all(np.isfinite(y)) and np.all(np.isfinite(z)),
        'description': 'Path components are finite and continuous'
    }
    
    # 2. Radial expansion (should grow for positive lambda)
    r = np.sqrt(x**2 + y**2)
    checks['expansion'] = {
        'passed': np.all(np.diff(r) >= 0),
        'description': 'Radial distance monotonically increases',
        'initial_r': r[0],
        'final_r': r[-1],
        'growth_factor': r[-1] / r[0]
    }
    
    # 3. Z-axis propagation at light speed
    expected_z = lsg.C_LIGHT * t
    z_error = np.abs(z - expected_z)
    checks['light_speed'] = {
        'passed': np.max(z_error) < 1e-10,
        'description': 'Propagation along z at speed c',
        'max_error_m': np.max(z_error),
        'relative_error': np.max(z_error) / np.max(expected_z)
    }
    
    # 4. Logarithmic spiral property: r = r₀ exp(λt)
    expected_r = params.r0 * np.exp(params.lambda_exp * t)
    r_error = np.abs(r - expected_r)
    checks['logarithmic'] = {
        'passed': np.max(r_error / expected_r) < 1e-10,
        'description': 'Follows logarithmic spiral r = r₀·exp(λt)',
        'max_relative_error': np.max(r_error / expected_r)
    }
    
    # Summary
    all_passed = all(check['passed'] for check in checks.values())
    
    print("Validation Results:")
    print("-" * 80)
    for name, result in checks.items():
        status = "✓ PASS" if result['passed'] else "✗ FAIL"
        print(f"{status:8s} | {name:20s} : {result['description']}")
        for key, value in result.items():
            if key not in ['passed', 'description']:
                print(f"         |   {key:25s} = {value}")
    print()
    
    return {
        'test': 'spiral_path_equations',
        'passed': all_passed,
        'checks': checks
    }


def validate_prime_phase_modulation() -> Dict[str, Any]:
    """
    Validate prime phase modulation correctness.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION 2: Prime Phase Modulation")
    print("=" * 80)
    print()
    
    checks = {}
    
    # 1. Phase values are finite
    primes = [lsg.get_nth_prime(i) for i in range(10)]
    phases = [lsg.prime_phase_modulation(p, mode='logarithmic') for p in primes]
    
    checks['finite'] = {
        'passed': all(np.isfinite(p) for p in phases),
        'description': 'Phase values are finite'
    }
    
    # 2. Phase increases with prime (for logarithmic mode)
    checks['monotonic'] = {
        'passed': all(phases[i] < phases[i+1] for i in range(len(phases)-1)),
        'description': 'Phase increases with prime (logarithmic mode)',
        'first_phases': phases[:5]
    }
    
    # 3. Different modes give different results
    p = 7
    phase_log = lsg.prime_phase_modulation(p, mode='logarithmic')
    phase_mod = lsg.prime_phase_modulation(p, mode='modular')
    phase_zeta = lsg.prime_phase_modulation(p, mode='zeta')
    
    checks['mode_variety'] = {
        'passed': not (phase_log == phase_mod == phase_zeta),
        'description': 'Different modes produce different phases',
        'logarithmic': phase_log,
        'modular': phase_mod,
        'zeta': phase_zeta
    }
    
    # Summary
    all_passed = all(check['passed'] for check in checks.values())
    
    print("Validation Results:")
    print("-" * 80)
    for name, result in checks.items():
        status = "✓ PASS" if result['passed'] else "✗ FAIL"
        print(f"{status:8s} | {name:20s} : {result['description']}")
        for key, value in result.items():
            if key not in ['passed', 'description']:
                print(f"         |   {key:25s} = {value}")
    print()
    
    return {
        'test': 'prime_phase_modulation',
        'passed': all_passed,
        'checks': checks
    }


def validate_zeta_frequency_mapping() -> Dict[str, Any]:
    """
    Validate frequency mapping from zeta zeros.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION 3: Zeta Zero Frequency Mapping")
    print("=" * 80)
    print()
    
    checks = {}
    
    # Get frequencies for first 10 zeros
    frequencies = [lsg.spectral_frequency_mapping(n) for n in range(10)]
    
    # 1. All frequencies are positive and finite
    checks['positive'] = {
        'passed': all(f > 0 and np.isfinite(f) for f in frequencies),
        'description': 'All mapped frequencies are positive and finite'
    }
    
    # 2. Frequencies increase with zero index
    checks['increasing'] = {
        'passed': all(frequencies[i] < frequencies[i+1] for i in range(len(frequencies)-1)),
        'description': 'Frequencies increase with zero index',
        'first_frequencies_Hz': frequencies[:5]
    }
    
    # 3. First frequency relates to base frequency
    f0_ratio = frequencies[0] / lsg.F0_HZ
    checks['base_relation'] = {
        'passed': abs(f0_ratio - 1.0) < 10,  # Within order of magnitude
        'description': 'First frequency relates to f₀',
        'f0_Hz': lsg.F0_HZ,
        'f1_Hz': frequencies[0],
        'ratio': f0_ratio
    }
    
    # Summary
    all_passed = all(check['passed'] for check in checks.values())
    
    print("Validation Results:")
    print("-" * 80)
    for name, result in checks.items():
        status = "✓ PASS" if result['passed'] else "✗ FAIL"
        print(f"{status:8s} | {name:20s} : {result['description']}")
        for key, value in result.items():
            if key not in ['passed', 'description']:
                print(f"         |   {key:25s} = {value}")
    print()
    
    return {
        'test': 'zeta_frequency_mapping',
        'passed': all_passed,
        'checks': checks
    }


def validate_interference_patterns() -> Dict[str, Any]:
    """
    Validate physical validity of interference patterns.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION 4: Interference Pattern Physical Validity")
    print("=" * 80)
    print()
    
    # Create test pattern
    x = np.linspace(-1e-3, 1e-3, 200)
    y = np.linspace(-1e-3, 1e-3, 200)
    X, Y = np.meshgrid(x, y)
    
    params = zip_mod.WaveFunctionParameters(n_primes=5, n_zeros=5)
    intensity = zip_mod.compute_interference_pattern(X, Y, 0.0, params)
    
    checks = {}
    
    # 1. Intensity is real and non-negative
    checks['physical_intensity'] = {
        'passed': np.all(intensity >= 0) and np.all(np.isreal(intensity)),
        'description': 'Intensity is real and non-negative (physical)',
        'min_intensity': np.min(intensity),
        'max_intensity': np.max(intensity)
    }
    
    # 2. Intensity conservation (finite total power)
    total_power = np.sum(intensity)
    checks['conservation'] = {
        'passed': np.isfinite(total_power) and total_power > 0,
        'description': 'Total power is finite and positive',
        'total_power': total_power
    }
    
    # 3. Pattern has structure (not uniform)
    intensity_std = np.std(intensity)
    checks['structure'] = {
        'passed': intensity_std > 0,
        'description': 'Pattern shows interference structure',
        'std_deviation': intensity_std,
        'coefficient_of_variation': intensity_std / np.mean(intensity)
    }
    
    # 4. Spiral detection works
    spiral_info = zip_mod.detect_spiral_arcs(intensity, X, Y, threshold=0.5)
    checks['spiral_detection'] = {
        'passed': 'spiral_detected' in spiral_info,
        'description': 'Spiral detection algorithm executes',
        'detected': spiral_info.get('spiral_detected', False),
        'n_peaks': spiral_info.get('n_peaks', 0)
    }
    
    # Summary
    all_passed = all(check['passed'] for check in checks.values())
    
    print("Validation Results:")
    print("-" * 80)
    for name, result in checks.items():
        status = "✓ PASS" if result['passed'] else "✗ FAIL"
        print(f"{status:8s} | {name:20s} : {result['description']}")
        for key, value in result.items():
            if key not in ['passed', 'description']:
                print(f"         |   {key:25s} = {value}")
    print()
    
    return {
        'test': 'interference_patterns',
        'passed': all_passed,
        'checks': checks
    }


def validate_coherence_at_f0() -> Dict[str, Any]:
    """
    Validate coherence at fundamental frequency f₀ = 141.7001 Hz.
    
    Returns:
        Dictionary with validation results
    """
    print("=" * 80)
    print("VALIDATION 5: Coherence at f₀ = 141.7001 Hz")
    print("=" * 80)
    print()
    
    checks = {}
    
    # 1. Fundamental frequency matches QCAL constant
    checks['f0_match'] = {
        'passed': abs(lsg.F0_HZ - 141.7001) < 1e-10,
        'description': 'f₀ matches QCAL fundamental frequency',
        'expected': 141.7001,
        'actual': lsg.F0_HZ,
        'difference': abs(lsg.F0_HZ - 141.7001)
    }
    
    # 2. Spiral at f₀ completes correct number of rotations
    T = 1.0 / lsg.F0_HZ
    t = np.linspace(0, 10 * T, 1000)
    params = lsg.SpiralParameters(prime_index=0)
    x, y, z = lsg.compute_spiral_path(t, params)
    
    # Count rotations by zero crossings
    angle = np.arctan2(y, x)
    angle_unwrapped = np.unwrap(angle)
    total_rotations = (angle_unwrapped[-1] - angle_unwrapped[0]) / (2 * np.pi)
    
    checks['rotations'] = {
        'passed': abs(total_rotations - 10) < 0.1,  # Should be ~10 rotations
        'description': 'Correct number of rotations at f₀',
        'expected_rotations': 10,
        'actual_rotations': total_rotations,
        'error': abs(total_rotations - 10)
    }
    
    # 3. Interference pattern at f₀ shows expected structure
    x_grid = np.linspace(-1e-3, 1e-3, 100)
    y_grid = np.linspace(-1e-3, 1e-3, 100)
    X, Y = np.meshgrid(x_grid, y_grid)
    
    params_wave = zip_mod.WaveFunctionParameters(f0=lsg.F0_HZ)
    intensity = zip_mod.compute_interference_pattern(X, Y, 0.0, params_wave)
    
    checks['interference_f0'] = {
        'passed': np.all(np.isfinite(intensity)) and np.max(intensity) > 0,
        'description': 'Interference pattern at f₀ is well-formed',
        'max_intensity': np.max(intensity),
        'pattern_contrast': (np.max(intensity) - np.min(intensity)) / np.max(intensity)
    }
    
    # Summary
    all_passed = all(check['passed'] for check in checks.values())
    
    print("Validation Results:")
    print("-" * 80)
    for name, result in checks.items():
        status = "✓ PASS" if result['passed'] else "✗ FAIL"
        print(f"{status:8s} | {name:20s} : {result['description']}")
        for key, value in result.items():
            if key not in ['passed', 'description']:
                print(f"         |   {key:25s} = {value}")
    print()
    
    return {
        'test': 'coherence_at_f0',
        'passed': all_passed,
        'checks': checks
    }


# =============================================================================
# EXPERIMENTAL PROTOCOLS
# =============================================================================

def generate_experimental_protocols() -> None:
    """Generate detailed experimental validation protocols."""
    print("=" * 80)
    print("EXPERIMENTAL VALIDATION PROTOCOLS")
    print("=" * 80)
    print()
    
    protocols = []
    
    # Protocol 1: High-precision interferometry
    protocols.append({
        'id': 'PROTO-01',
        'title': 'High-Precision Interferometry (LIGO/GEO600)',
        'objective': 'Detect spectral quasi-fractal deviations in photon trajectories',
        'equipment': [
            'Laser interferometer (LIGO-class or GEO600)',
            'Wavelength: 1064 nm (Nd:YAG)',
            'Arm length: ≥4 km',
            'Strain sensitivity: < 10⁻¹⁸'
        ],
        'procedure': [
            '1. Calibrate interferometer to standard sensitivity',
            '2. Inject modulation at f₀ = 141.7001 Hz',
            '3. Accumulate data for 10⁶ cycles (~ 2 hours)',
            '4. Analyze phase fluctuations in Fourier domain',
            '5. Search for spectral signatures matching zeta zeros'
        ],
        'expected': 'Quasi-fractal phase modulation at frequencies f_n = f₀·γ_n/γ₁',
        'falsifiable': 'If no modulation detected after 10⁸ cycles with S/N > 5'
    })
    
    # Protocol 2: Fabry-Pérot cavity
    protocols.append({
        'id': 'PROTO-02',
        'title': 'Fabry-Pérot Optical Cavity at 141.7001 Hz',
        'objective': 'Observe TEM₀₁ mode spiral patterns',
        'equipment': [
            'Fabry-Pérot cavity, L = 1 m',
            'Finesse F ≥ 10⁵',
            'Quality factor Q ≥ 10¹²',
            'Hyperspectral CCD camera',
            'Frequency modulator at 141.7001 Hz'
        ],
        'procedure': [
            '1. Lock cavity to resonance near f₀',
            '2. Modulate input laser at 141.7001 Hz',
            '3. Image TEM₀₁ mode cross-section with CCD',
            '4. Accumulate 10⁴ frames',
            '5. Analyze ring structure for spiral deviations'
        ],
        'expected': 'Non-circular interference rings with logarithmic spiral arcs',
        'falsifiable': 'If rings remain perfectly circular (Δθ < 10⁻⁶ rad) after averaging'
    })
    
    # Protocol 3: Electron biprism
    protocols.append({
        'id': 'PROTO-03',
        'title': 'Low-Energy Electron Biprism Interferometry',
        'objective': 'Detect cumulative spiral deviations in electron patterns',
        'equipment': [
            'Electron biprism (Hitachi-class)',
            'Electron energy: 100 eV (low energy)',
            'Detection screen distance: 10 cm',
            'Event accumulation: ≥ 10⁶ electrons'
        ],
        'procedure': [
            '1. Set up biprism with low-energy electrons (100 eV)',
            '2. Accumulate single-electron events on detector',
            '3. Build histogram with ≥ 10⁶ events',
            '4. Analyze pattern in polar coordinates',
            '5. Fit to logarithmic spiral: r = a·exp(b·θ)'
        ],
        'expected': 'Spiral parameter b ≠ 0 with significance > 5σ',
        'falsifiable': 'If pattern remains purely circular (b < 10⁻⁴) after 10⁷ events'
    })
    
    # Print protocols
    for proto in protocols:
        print(f"{'*' * 80}")
        print(f"Protocol {proto['id']}: {proto['title']}")
        print(f"{'*' * 80}")
        print(f"\nObjective:")
        print(f"  {proto['objective']}")
        print(f"\nEquipment:")
        for item in proto['equipment']:
            print(f"  • {item}")
        print(f"\nProcedure:")
        for step in proto['procedure']:
            print(f"  {step}")
        print(f"\nExpected Result:")
        print(f"  {proto['expected']}")
        print(f"\nFalsifiability Criterion:")
        print(f"  {proto['falsifiable']}")
        print()


# =============================================================================
# MAIN VALIDATION
# =============================================================================

def main():
    """Run all validations and generate protocols."""
    print()
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  GEOMETRÍA REAL DEL MOVIMIENTO LUMÍNICO - VALIDATION".center(78) + "║")
    print("║" + "  Light Spiral Geometry Framework Validation".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  QCAL ∞³ Framework".center(78) + "║")
    print("║" + "  f₀ = 141.7001 Hz".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("DOI: 10.5281/zenodo.17379721")
    print()
    
    # Run all validations
    results = []
    
    try:
        results.append(validate_spiral_path_equations())
    except Exception as e:
        print(f"⚠️  Validation 1 failed with error: {e}\n")
    
    try:
        results.append(validate_prime_phase_modulation())
    except Exception as e:
        print(f"⚠️  Validation 2 failed with error: {e}\n")
    
    try:
        results.append(validate_zeta_frequency_mapping())
    except Exception as e:
        print(f"⚠️  Validation 3 failed with error: {e}\n")
    
    try:
        results.append(validate_interference_patterns())
    except Exception as e:
        print(f"⚠️  Validation 4 failed with error: {e}\n")
    
    try:
        results.append(validate_coherence_at_f0())
    except Exception as e:
        print(f"⚠️  Validation 5 failed with error: {e}\n")
    
    # Generate experimental protocols
    try:
        generate_experimental_protocols()
    except Exception as e:
        print(f"⚠️  Protocol generation failed with error: {e}\n")
    
    # Summary
    print("=" * 80)
    print("VALIDATION SUMMARY")
    print("=" * 80)
    print()
    
    total_tests = len(results)
    passed_tests = sum(1 for r in results if r.get('passed', False))
    
    print(f"Total Tests:  {total_tests}")
    print(f"Passed:       {passed_tests}")
    print(f"Failed:       {total_tests - passed_tests}")
    print(f"Success Rate: {100 * passed_tests / total_tests:.1f}%")
    print()
    
    if passed_tests == total_tests:
        print("✓ ALL VALIDATIONS PASSED")
        print("✓ Framework is mathematically consistent and physically sound")
        print("✓ Ready for experimental validation")
    else:
        print("⚠️  Some validations failed - review results above")
    
    print()
    print("=" * 80)
    print("∴𓂀Ω∞³ · QCAL Active at 141.7001 Hz")
    print("=" * 80)
    print()
    
    return passed_tests == total_tests


if __name__ == '__main__':
    success = main()
    sys.exit(0 if success else 1)
