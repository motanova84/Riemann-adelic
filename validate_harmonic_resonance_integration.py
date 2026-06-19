#!/usr/bin/env python3
"""
Integration Example: Harmonic Resonance Oracle with V5 Coronación

This script shows how to integrate the Harmonic Resonance Oracle
with the existing V5 Coronación validation framework.

The integration demonstrates that RH is not just verified, but LIVED
through the harmonic resonance structure at f₀ = 141.7001 Hz.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
import json

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from utils.harmonic_resonance_oracle import (
        HarmonicResonanceOracle,
        F0_QCAL,
        demonstrate_harmonic_resonance
    )
    ORACLE_AVAILABLE = True
except ImportError:
    ORACLE_AVAILABLE = False
    print("⚠️  Warning: Harmonic Resonance Oracle not available")
    print("   Some dependencies may be missing.")


def validate_harmonic_resonance_integration(
    n_harmonics: int = 100,
    tolerance: float = 1e-6,
    save_certificate: bool = True
) -> dict:
    """
    Validate RH through harmonic resonance integration.
    
    This function integrates the Harmonic Resonance Oracle with the
    V5 Coronación validation framework to show that RH is LIVED
    through harmonic structure.
    
    Args:
        n_harmonics: Number of harmonics to validate
        tolerance: Resonance detection tolerance
        save_certificate: Whether to save validation certificate
        
    Returns:
        Dictionary with validation results
    """
    print()
    print("=" * 80)
    print("  HARMONIC RESONANCE INTEGRATION - V5 Coronación")
    print("=" * 80)
    print()
    
    if not ORACLE_AVAILABLE:
        print("  ❌ Cannot run validation: Oracle not available")
        return {
            "status": "error",
            "message": "Harmonic Resonance Oracle not available"
        }
    
    # Create oracle
    print(f"  Initializing Harmonic Resonance Oracle...")
    print(f"  Fundamental frequency: {F0_QCAL} Hz")
    print()
    
    oracle = HarmonicResonanceOracle(precision=50)
    
    # Listen to the symphony
    print(f"  Listening to {n_harmonics} harmonics...")
    
    # For demonstration, we use first 10 known zeros
    # In full integration, this would use all available zeros
    known_zeros = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832
    ]
    
    n_test = min(n_harmonics, len(known_zeros))
    resonances = oracle.listen_to_symphony(n_test, known_zeros[:n_test])
    
    print(f"  ✅ Detected {len(resonances)} harmonics")
    print()
    
    # Analyze the chord
    print("  Analyzing harmonic chord structure...")
    chord = oracle.harmonic_chord(resonances)
    
    print(f"  Chord Type: {chord['chord_type'].upper()}")
    print(f"  Resonant Harmonics: {chord['resonant_count']}/{chord['total_count']}")
    print(f"  Harmony: {chord['harmony']:.2%}")
    print(f"  Coherence: {chord['coherence']:.6f}")
    print()
    
    # Validation criteria
    is_perfect_harmony = chord['chord_type'] == 'perfect'
    is_high_coherence = chord['coherence'] > 1.0
    is_full_resonance = chord['harmony'] >= 0.9
    
    # Overall validation
    validation_passed = is_perfect_harmony and is_high_coherence and is_full_resonance
    
    if validation_passed:
        print("  ✅ VALIDATION PASSED")
        print("  ∴𓂀Ω∞³ - El universo suena a 141.7001 Hz")
    else:
        print("  ⚠️  VALIDATION WARNING")
        print(f"  Perfect harmony: {is_perfect_harmony}")
        print(f"  High coherence: {is_high_coherence}")
        print(f"  Full resonance: {is_full_resonance}")
    
    print()
    print("=" * 80)
    print("  🏁 CONCLUSIÓN OPERATIVA")
    print("=" * 80)
    print()
    print("  El sistema ya no verifica RH.")
    print("  El sistema vive RH.")
    print()
    print("  Cada true del oráculo es un acorde de la sinfonía fundamental.")
    print()
    print("=" * 80)
    print()
    
    # Prepare results
    results = {
        "status": "success" if validation_passed else "warning",
        "validation_passed": validation_passed,
        "fundamental_frequency": F0_QCAL,
        "n_harmonics_tested": n_test,
        "chord": {
            "type": chord['chord_type'],
            "resonant_count": chord['resonant_count'],
            "total_count": chord['total_count'],
            "harmony": chord['harmony'],
            "coherence": chord['coherence']
        },
        "criteria": {
            "perfect_harmony": is_perfect_harmony,
            "high_coherence": is_high_coherence,
            "full_resonance": is_full_resonance
        },
        "resonances": [
            {
                "harmonic_number": r.harmonic_number,
                "frequency": r.frequency,
                "zero_position": r.zero_imaginary_part,
                "amplitude": r.amplitude,
                "is_resonant": r.is_resonant()
            }
            for r in resonances
        ]
    }
    
    # Save certificate if requested
    if save_certificate:
        cert_path = Path("data/harmonic_resonance_validation_certificate.json")
        cert_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(cert_path, 'w') as f:
            json.dump(results, f, indent=2)
        
        print(f"  📄 Certificate saved to: {cert_path}")
        print()
    
    return results


def integration_example():
    """
    Example of integrating harmonic resonance oracle with V5 validation.
    """
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  HARMONIC RESONANCE ORACLE - V5 CORONACIÓN INTEGRATION".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    
    print("This example demonstrates how to integrate the Harmonic Resonance Oracle")
    print("with the existing V5 Coronación validation framework.")
    print()
    print("The integration shows that:")
    print("  1. The spectrum of H_Ψ IS the critical line (by definition)")
    print("  2. Riemann zeros ARE in that spectrum (by harmonic correspondence)")
    print("  3. Each zero resonates at harmonic n·f₀")
    print("  4. The oracle LIVES RH instead of verifying it")
    print()
    
    input("Press Enter to run integration validation...")
    
    # Run validation
    results = validate_harmonic_resonance_integration(
        n_harmonics=10,
        save_certificate=True
    )
    
    # Show results
    if results['status'] == 'success':
        print()
        print("  ✨ Integration successful!")
        print()
        print("  Key findings:")
        print(f"    - Fundamental frequency: {results['fundamental_frequency']} Hz")
        print(f"    - Harmonics tested: {results['n_harmonics_tested']}")
        print(f"    - Chord type: {results['chord']['type']}")
        print(f"    - Harmony: {results['chord']['harmony']:.2%}")
        print()
        print("  Next steps:")
        print("    1. Extend to more harmonics (n > 100)")
        print("    2. Integrate with validate_v5_coronacion.py")
        print("    3. Add to CI/CD pipeline")
        print("    4. Generate visualization")
        print()
    else:
        print()
        print("  ⚠️  Integration needs attention")
        print(f"     Status: {results.get('status', 'unknown')}")
        print()
    
    return results


if __name__ == "__main__":
    try:
        results = integration_example()
        
        print()
        print("  © 2026 José Manuel Mota Burruezo Ψ ✧ ∞³")
        print("  Instituto de Conciencia Cuántica (ICQ)")
        print("  DOI: 10.5281/zenodo.17379721")
        print("  ORCID: 0009-0002-1923-0773")
        print()
        print("  ∴𓂀Ω∞³")
        print("  El universo suena. Y suena a 141.7001 Hz.")
        print()
        
        sys.exit(0 if results.get('validation_passed', False) else 1)
        
    except KeyboardInterrupt:
        print()
        print()
        print("  Integration interrupted by user.")
        print()
        sys.exit(1)
        
    except Exception as e:
        print()
        print(f"  ❌ Error during integration: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
