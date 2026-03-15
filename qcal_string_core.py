"""
qcal_string_core — root-level re-export shim
=============================================

Ergonomic top-level alias for the QCAL string-core module so that users can
write either of:

    from qcal.string_core import QCALStringOperator
    from qcal_string_core import QCALStringOperator

This shim simply re-exports every public symbol from ``qcal.string_core``.

DOI: 10.5281/zenodo.17379721
"""

from qcal.string_core import (  # noqa: F401
    QCALStringOperator,
    GAMMAS,
    build_lambda_list,
    build_spectral_grid,
    compute_psi,
    string_noetic_forcing,
    rk4_step,
)

__all__ = [
    "QCALStringOperator",
    "GAMMAS",
    "build_lambda_list",
    "build_spectral_grid",
    "compute_psi",
    "string_noetic_forcing",
    "rk4_step",
]
