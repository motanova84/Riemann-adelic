"""
FFI Package - Python-Lean Foreign Function Interface
====================================================

This package provides a comprehensive FFI bridge between Python and Lean 4,
enabling bidirectional communication and integration with the QCAL framework.

Components:
- python_ffi_wrapper.py: Python functions exposed to Lean
- ffi_bridge.c: C bridge layer using Python C API
- FFI.lean: Lean bindings and high-level API
- test_ffi.py: Comprehensive test suite
- examples/: Usage examples

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"
__all__ = ["python_ffi_wrapper"]

# Import main FFI functions for convenience
from .python_ffi_wrapper import (
    ffi_get_constant,
    ffi_validate_coherence,
    ffi_compute_psi,
    ffi_run_validation,
    ffi_compute_riemann_zero,
    ffi_evaluate_zeta,
    ffi_check_critical_line,
    ffi_generate_certificate,
    ffi_get_api_info,
)
