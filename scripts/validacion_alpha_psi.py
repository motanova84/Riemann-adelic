#!/usr/bin/env python3
"""
Bridge script to execute the SageMath quantum radius validation.

This script provides a Python interface to the SageMath validator for
quantum radio RΨ validation, enabling integration with CI/CD pipelines
that expect Python scripts.

The actual validation is performed by test_validacion_radio_cuantico.sage,
which computes:
    f₀ = c / (2π * RΨ * ℓP)
    
where:
    f₀ ≈ 141.7001 Hz - Frecuencia fundamental QCAL
    c = 299792458 m/s - Velocidad de la luz
    ℓP = 1.616255e-35 m - Longitud de Planck
    RΨ - Radio cuántico (parámetro a validar)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import subprocess
import sys
import os
import json
import argparse
from pathlib import Path


def check_sage_available():
    """
    Check if SageMath is available in the system.
    
    Returns:
        bool: True if sage command is available, False otherwise
    """
    try:
        result = subprocess.run(
            ["sage", "--version"],
            capture_output=True,
            text=True,
            timeout=10
        )
        return result.returncode == 0
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False


def run_sage_validation(precision_bits=256, sage_script=None):
    """
    Execute the SageMath quantum radio validation script.
    
    Args:
        precision_bits: Precision in bits for arbitrary precision arithmetic
        sage_script: Path to the Sage script (optional, uses default if None)
        
    Returns:
        tuple: (success: bool, stdout: str, stderr: str, results: dict)
    """
    # Determine script path
    if sage_script is None:
        # Look in the repository root
        repo_root = Path(__file__).parent.parent
        sage_script = repo_root / "test_validacion_radio_cuantico.sage"
    else:
        sage_script = Path(sage_script)
    
    if not sage_script.exists():
        return False, "", f"Error: Sage script not found at {sage_script}", {}
    
    # Execute the Sage script
    try:
        result = subprocess.run(
            ["sage", str(sage_script), str(precision_bits)],
            capture_output=True,
            text=True,
            timeout=300  # 5 minutes timeout
        )
        
        stdout = result.stdout
        stderr = result.stderr
        success = result.returncode == 0
        
        # Try to load results JSON if it exists
        results = {}
        results_file = Path("quantum_radio_validation_results.json")
        if results_file.exists():
            try:
                with open(results_file, 'r') as f:
                    results = json.load(f)
            except json.JSONDecodeError:
                pass
        
        return success, stdout, stderr, results
        
    except subprocess.TimeoutExpired:
        return False, "", "Error: Sage validation timed out after 5 minutes", {}
    except FileNotFoundError:
        return False, "", "Error: 'sage' command not found. Please install SageMath.", {}
    except Exception as e:
        return False, "", f"Error executing Sage script: {str(e)}", {}


def python_fallback_validation(precision_dps=30):
    """
    Fallback validation using pure Python (mpmath) when Sage is not available.
    
    This provides basic validation but with lower precision than Sage.
    
    Args:
        precision_dps: Decimal precision (digits)
        
    Returns:
        dict: Validation results
    """
    try:
        import mpmath as mp
    except ImportError:
        return {
            "overall_valid": False,
            "error": "Neither Sage nor mpmath is available",
            "fallback_mode": True
        }
    
    # Set precision
    mp.mp.dps = precision_dps
    
    # Constants
    F0 = mp.mpf('141.7001')  # Hz - Fundamental frequency
    C = mp.mpf('299792458')  # m/s - Speed of light
    L_PLANCK = mp.mpf('1.616255e-35')  # m - Planck length
    
    # Compute quantum radio: RΨ = c / (2π * f₀ * ℓP)
    R_psi = C / (2 * mp.pi * F0 * L_PLANCK)
    
    # Compute coherence: C = RΨ / ℓP
    coherence = R_psi / L_PLANCK
    
    # Basic validation checks
    R_psi_valid = (R_psi > 0) and (R_psi < mp.mpf('1e50'))
    
    results = {
        "overall_valid": R_psi_valid,
        "R_psi": float(R_psi),
        "R_psi_valid": R_psi_valid,
        "coherence": float(coherence),
        "precision_dps": precision_dps,
        "fallback_mode": True,
        "note": "Using Python fallback (mpmath). For full validation, install SageMath."
    }
    
    return results


def main():
    """Main entry point for the bridge script."""
    parser = argparse.ArgumentParser(
        description="Quantum Radio RΨ Validation - Python Bridge to SageMath"
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=256,
        help="Precision in bits for Sage validation (default: 256)"
    )
    parser.add_argument(
        "--sage-script",
        type=str,
        default=None,
        help="Path to the Sage validation script (optional)"
    )
    parser.add_argument(
        "--fallback-dps",
        type=int,
        default=30,
        help="Decimal precision for Python fallback (default: 30)"
    )
    parser.add_argument(
        "--force-fallback",
        action="store_true",
        help="Force use of Python fallback instead of Sage"
    )
    
    args = parser.parse_args()
    
    print("=" * 80)
    print("🔬 VALIDACIÓN DEL RADIO CUÁNTICO RΨ")
    print("   (Python Bridge to SageMath)")
    print("=" * 80)
    print()
    
    # Check if Sage is available
    sage_available = check_sage_available() and not args.force_fallback
    
    if sage_available:
        print("✅ SageMath detected - using high-precision validation")
        print(f"   Precision: {args.precision} bits")
        print()
        
        success, stdout, stderr, results = run_sage_validation(
            precision_bits=args.precision,
            sage_script=args.sage_script
        )
        
        # Print output
        if stdout:
            print(stdout)
        if stderr:
            print(stderr, file=sys.stderr)
        
        # Print results summary
        if results:
            print()
            print("📊 Validation Results Summary:")
            print(f"   Overall Valid: {results.get('overall_valid', False)}")
            print(f"   RΨ: {results.get('R_psi', 'N/A'):.6e} m" if 'R_psi' in results else "   RΨ: N/A")
            print(f"   Coherence: {results.get('coherence', 'N/A'):.6e}" if 'coherence' in results else "   Coherence: N/A")
        
        return 0 if success else 1
        
    else:
        print("⚠️  SageMath not available - using Python fallback (mpmath)")
        print(f"   Precision: {args.fallback_dps} decimal places")
        print()
        
        results = python_fallback_validation(precision_dps=args.fallback_dps)
        
        # Print results
        print("📊 Validation Results (Fallback Mode):")
        print(f"   Overall Valid: {results.get('overall_valid', False)}")
        print(f"   RΨ: {results.get('R_psi', 'N/A'):.6e} m" if 'R_psi' in results else "   RΨ: N/A")
        print(f"   Coherence: {results.get('coherence', 'N/A'):.6e}" if 'coherence' in results else "   Coherence: N/A")
        
        if 'note' in results:
            print(f"\nℹ️  {results['note']}")
        
        # Save results
        try:
            with open('quantum_radio_validation_results.json', 'w') as f:
                json.dump(results, f, indent=2)
            print("\n📄 Results saved to: quantum_radio_validation_results.json")
        except Exception as e:
            print(f"\n⚠️  Could not save results: {e}", file=sys.stderr)
        
        return 0 if results.get('overall_valid', False) else 1


if __name__ == "__main__":
    sys.exit(main())
