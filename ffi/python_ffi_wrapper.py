#!/usr/bin/env python3
"""
Python FFI Wrapper - Exposing Python Functions to Lean via C Bridge
===================================================================

This module provides a comprehensive FFI interface between Python and Lean,
enabling Lean code to call Python functions for numerical computation,
validation, and QCAL framework operations.

The FFI architecture consists of three layers:
1. Python layer (this file): High-level QCAL functions exposed to FFI
2. C bridge layer (ffi_bridge.c): Type conversion and Python C API calls
3. Lean layer (FFI.lean): Lean wrappers around C extern functions

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import json
import sys
import traceback
from typing import Dict, Any, List, Optional, Tuple
from pathlib import Path
import numpy as np

# Import QCAL modules
try:
    from qcal.constants import (
        F0, C_PRIMARY, C_COHERENCE, DELTA_ZETA,
        validate_constants_coherence
    )
    from qcal.validation import QCALValidator
except ImportError:
    # Fallback for when running from different directories
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from qcal.constants import (
        F0, C_PRIMARY, C_COHERENCE, DELTA_ZETA,
        validate_constants_coherence
    )
    from qcal.validation import QCALValidator


# =============================================================================
# FFI EXPORTS - Core Functions Exposed to Lean
# =============================================================================

def ffi_get_constant(name: str) -> float:
    """
    Get a QCAL constant by name.
    
    Args:
        name: Name of the constant (e.g., "F0", "C_PRIMARY", "DELTA_ZETA")
    
    Returns:
        The constant value, or 0.0 if not found
    
    Example (from Lean):
        f0 ← ffiGetConstant "F0"  -- Returns 141.7001
    """
    constants_map = {
        "F0": F0,
        "C_PRIMARY": C_PRIMARY,
        "C_COHERENCE": C_COHERENCE,
        "DELTA_ZETA": DELTA_ZETA,
    }
    return float(constants_map.get(name, 0.0))


def ffi_validate_coherence() -> bool:
    """
    Validate QCAL constants coherence.
    
    Returns:
        True if all coherence checks pass, False otherwise
    
    Example (from Lean):
        ok ← ffiValidateCoherence
        if ok then IO.println "✅ Coherence OK"
    """
    try:
        return validate_constants_coherence()
    except Exception as e:
        print(f"FFI Error in validate_coherence: {e}", file=sys.stderr)
        return False


def ffi_compute_psi(intensity: float, area_eff: float, coherence: float) -> float:
    """
    Compute Ψ = I × A_eff² × C^∞ for given parameters.
    
    Args:
        intensity: Information intensity I
        area_eff: Effective area A_eff
        coherence: Coherence factor C
    
    Returns:
        Ψ value
    
    Example (from Lean):
        psi ← ffiComputePsi 1.0 10.0 244.36
    """
    try:
        # Ψ = I × A_eff² × C^∞
        # For practical computation, we use C^3 as approximation for C^∞
        psi = intensity * (area_eff ** 2) * (coherence ** 3)
        return float(psi)
    except Exception as e:
        print(f"FFI Error in compute_psi: {e}", file=sys.stderr)
        return 0.0


def ffi_run_validation(config_json: str) -> str:
    """
    Run comprehensive QCAL validation with custom configuration.
    
    Args:
        config_json: JSON string with validation configuration
                     Format: {"precision": 50, "tolerance": 1e-6, "verbose": false}
    
    Returns:
        JSON string with validation results
    
    Example (from Lean):
        result ← ffiRunValidation "{\"precision\": 50}"
        let report := Json.parse result
    """
    try:
        config = json.loads(config_json)
        
        precision = config.get("precision", 50)
        tolerance = config.get("tolerance", 1e-6)
        verbose = config.get("verbose", False)
        
        validator = QCALValidator(
            precision=precision,
            tolerance=tolerance,
            verbose=verbose
        )
        
        results = validator.validate()
        
        # Convert numpy types to Python types for JSON serialization
        def convert_to_serializable(obj):
            if isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, dict):
                return {k: convert_to_serializable(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_to_serializable(item) for item in obj]
            return obj
        
        results_serializable = convert_to_serializable(results)
        
        return json.dumps(results_serializable, indent=2)
        
    except json.JSONDecodeError as e:
        error_result = {
            "error": f"Invalid JSON configuration: {e}",
            "all_checks_passed": False
        }
        return json.dumps(error_result)
    except Exception as e:
        error_result = {
            "error": f"Validation error: {e}",
            "traceback": traceback.format_exc(),
            "all_checks_passed": False
        }
        return json.dumps(error_result)


def ffi_compute_riemann_zero(n: int) -> str:
    """
    Compute the n-th non-trivial Riemann zeta zero.
    
    Args:
        n: Zero index (1-based, n >= 1)
    
    Returns:
        JSON string with zero information:
        {"index": n, "imaginary": γ_n, "real": 0.5}
    
    Example (from Lean):
        zero ← ffiComputeRiemannZero 1  -- First zero
        -- Returns: {"index": 1, "imaginary": 14.134725..., "real": 0.5}
    """
    try:
        # Import mpmath for high-precision computation
        import mpmath as mp
        mp.mp.dps = 50  # 50 decimal places
        
        # Compute the n-th zero
        if n < 1:
            raise ValueError(f"Zero index must be >= 1, got {n}")
        
        # Use mpmath to compute zeros
        gamma_n = mp.zetazero(n)
        
        result = {
            "index": n,
            "real": 0.5,
            "imaginary": float(gamma_n.imag),
            "on_critical_line": True
        }
        
        return json.dumps(result)
        
    except ImportError:
        error_result = {
            "error": "mpmath not available",
            "index": n,
            "real": 0.5,
            "imaginary": 0.0
        }
        return json.dumps(error_result)
    except Exception as e:
        error_result = {
            "error": f"Error computing zero: {e}",
            "index": n,
            "real": 0.5,
            "imaginary": 0.0
        }
        return json.dumps(error_result)


def ffi_evaluate_zeta(s_real: float, s_imag: float) -> str:
    """
    Evaluate the Riemann zeta function at s = s_real + i*s_imag.
    
    Args:
        s_real: Real part of s
        s_imag: Imaginary part of s
    
    Returns:
        JSON string with zeta value:
        {"real": Re(ζ(s)), "imag": Im(ζ(s))}
    
    Example (from Lean):
        zeta ← ffiEvaluateZeta 0.5 14.134725
    """
    try:
        import mpmath as mp
        mp.mp.dps = 50
        
        s = mp.mpc(s_real, s_imag)
        zeta_s = mp.zeta(s)
        
        result = {
            "real": float(zeta_s.real),
            "imag": float(zeta_s.imag),
            "input": {"real": s_real, "imag": s_imag}
        }
        
        return json.dumps(result)
        
    except ImportError:
        error_result = {
            "error": "mpmath not available",
            "real": 0.0,
            "imag": 0.0
        }
        return json.dumps(error_result)
    except Exception as e:
        error_result = {
            "error": f"Error evaluating zeta: {e}",
            "real": 0.0,
            "imag": 0.0
        }
        return json.dumps(error_result)


def ffi_check_critical_line(s_real: float, s_imag: float, tolerance: float = 1e-10) -> bool:
    """
    Check if ζ(s) ≈ 0 at the given point (i.e., if s is near a zero).
    
    Args:
        s_real: Real part of s
        s_imag: Imaginary part of s
        tolerance: Maximum |ζ(s)| to consider it a zero
    
    Returns:
        True if |ζ(s)| < tolerance, False otherwise
    
    Example (from Lean):
        isZero ← ffiCheckCriticalLine 0.5 14.134725 1e-10
    """
    try:
        import mpmath as mp
        mp.mp.dps = 50
        
        s = mp.mpc(s_real, s_imag)
        zeta_s = mp.zeta(s)
        magnitude = abs(zeta_s)
        
        return float(magnitude) < tolerance
        
    except Exception as e:
        print(f"FFI Error in check_critical_line: {e}", file=sys.stderr)
        return False


def ffi_generate_certificate(output_path: str) -> bool:
    """
    Generate a mathematical certificate for the current validation state.
    
    Args:
        output_path: Path where to save the certificate JSON
    
    Returns:
        True if certificate was generated successfully, False otherwise
    
    Example (from Lean):
        ok ← ffiGenerateCertificate "data/ffi_cert.json"
    """
    try:
        validator = QCALValidator(precision=50, verbose=False)
        results = validator.validate()
        
        certificate = validator.generate_certificate()
        
        output_file = Path(output_path)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(certificate, f, indent=2, ensure_ascii=False)
        
        return True
        
    except Exception as e:
        print(f"FFI Error in generate_certificate: {e}", file=sys.stderr)
        traceback.print_exc()
        return False


# =============================================================================
# FFI API Information
# =============================================================================

def ffi_get_api_info() -> str:
    """
    Get information about the available FFI functions.
    
    Returns:
        JSON string with API documentation
    
    Example (from Lean):
        info ← ffiGetApiInfo
        IO.println info
    """
    api_info = {
        "version": "1.0.0",
        "description": "Python-Lean FFI Bridge for QCAL Framework",
        "functions": {
            "ffi_get_constant": {
                "args": ["name: str"],
                "returns": "float",
                "description": "Get a QCAL constant by name"
            },
            "ffi_validate_coherence": {
                "args": [],
                "returns": "bool",
                "description": "Validate QCAL constants coherence"
            },
            "ffi_compute_psi": {
                "args": ["intensity: float", "area_eff: float", "coherence: float"],
                "returns": "float",
                "description": "Compute Ψ = I × A_eff² × C^∞"
            },
            "ffi_run_validation": {
                "args": ["config_json: str"],
                "returns": "str (JSON)",
                "description": "Run comprehensive QCAL validation"
            },
            "ffi_compute_riemann_zero": {
                "args": ["n: int"],
                "returns": "str (JSON)",
                "description": "Compute the n-th Riemann zeta zero"
            },
            "ffi_evaluate_zeta": {
                "args": ["s_real: float", "s_imag: float"],
                "returns": "str (JSON)",
                "description": "Evaluate ζ(s) at given point"
            },
            "ffi_check_critical_line": {
                "args": ["s_real: float", "s_imag: float", "tolerance: float"],
                "returns": "bool",
                "description": "Check if ζ(s) ≈ 0"
            },
            "ffi_generate_certificate": {
                "args": ["output_path: str"],
                "returns": "bool",
                "description": "Generate mathematical certificate"
            }
        },
        "constants": {
            "F0": 141.7001,
            "C_PRIMARY": 244.36,
            "C_COHERENCE": 244.36,
            "DELTA_ZETA": 0.2787437627
        }
    }
    
    return json.dumps(api_info, indent=2)


# =============================================================================
# Test Functions
# =============================================================================

if __name__ == "__main__":
    """Test the FFI wrapper functions."""
    print("=" * 70)
    print("QCAL Python FFI Wrapper - Function Tests")
    print("=" * 70)
    
    # Test 1: Get constant
    print("\n[Test 1] Get constant F0:")
    f0 = ffi_get_constant("F0")
    print(f"  F0 = {f0} Hz")
    
    # Test 2: Validate coherence
    print("\n[Test 2] Validate coherence:")
    coherent = ffi_validate_coherence()
    print(f"  Coherence OK: {coherent}")
    
    # Test 3: Compute Ψ
    print("\n[Test 3] Compute Ψ:")
    psi = ffi_compute_psi(1.0, 10.0, 244.36)
    print(f"  Ψ = {psi}")
    
    # Test 4: Run validation
    print("\n[Test 4] Run validation:")
    config = json.dumps({"precision": 25, "verbose": False})
    result_json = ffi_run_validation(config)
    result = json.loads(result_json)
    print(f"  All checks passed: {result.get('all_checks_passed', False)}")
    
    # Test 5: Compute Riemann zero
    print("\n[Test 5] Compute first Riemann zero:")
    zero_json = ffi_compute_riemann_zero(1)
    zero = json.loads(zero_json)
    print(f"  γ₁ = {zero.get('imaginary', 'N/A')}")
    
    # Test 6: Evaluate zeta
    print("\n[Test 6] Evaluate ζ(1/2 + 14.134725i):")
    zeta_json = ffi_evaluate_zeta(0.5, 14.134725)
    zeta = json.loads(zeta_json)
    print(f"  ζ(s) = {zeta.get('real', 0)} + {zeta.get('imag', 0)}i")
    
    # Test 7: Check critical line
    print("\n[Test 7] Check if s = 1/2 + 14.134725i is a zero:")
    is_zero = ffi_check_critical_line(0.5, 14.134725, 1e-6)
    print(f"  Is zero: {is_zero}")
    
    # Test 8: API Info
    print("\n[Test 8] Get API info:")
    api_info = ffi_get_api_info()
    print("  API info available (see ffi_get_api_info())")
    
    print("\n" + "=" * 70)
    print("✅ All FFI wrapper tests completed")
    print("=" * 70)
