"""
QCAL Master Lagrangian Module
Unified Lagrangian fibration geometry with QCAL field dynamics

This module implements the master Lagrangian unification:
L_MASTER = L_QCAL + L_FIBRATION + L_COUPLING

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

from .master_lagrangian import (
    MasterLagrangian,
    compute_qcal_lagrangian,
    compute_fibration_lagrangian,
    compute_coupling_lagrangian,
    derive_equations_of_motion,
    compute_quantized_spectrum,
    verify_energy_conservation,
)

__all__ = [
    "MasterLagrangian",
    "compute_qcal_lagrangian",
    "compute_fibration_lagrangian", 
    "compute_coupling_lagrangian",
    "derive_equations_of_motion",
    "compute_quantized_spectrum",
    "verify_energy_conservation",
]

__version__ = "1.0.0"
