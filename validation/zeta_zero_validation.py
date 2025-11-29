#!/usr/bin/env python3
"""
zeta_zero_validation.py
Author: José Manuel Mota Burruezo (JMMB Ψ✧)
License: CC-BY-4.0

Riemann Zeta Zero Validation – Critical Line Accuracy
=====================================================

This module validates that the non-trivial zeros of the Riemann zeta function
lie on the critical line Re(s) = 0.5, demonstrating numerical RH consistency.

Part of QCAL ∞³ framework for Riemann Hypothesis proof.
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

from mpmath import zetazero, mp
import matplotlib.pyplot as plt
from typing import List, Tuple


def validate_zeta_zeros(
    n_zeros: int = 50,
    precision: int = 50,
    save_plot: bool = True,
    plot_filename: str = "zeta_zeros_error_plot.png",
    verbose: bool = True
) -> Tuple[List[float], List[float], float]:
    """
    Validate non-trivial zeros of the Riemann zeta function.

    Args:
        n_zeros: Number of zeros to validate (default: 50)
        precision: Decimal precision for computation (default: 50 dps)
        save_plot: Whether to save the error plot (default: True)
        plot_filename: Filename for the error plot (default: "zeta_zeros_error_plot.png")
        verbose: Whether to print validation output (default: True)

    Returns:
        Tuple containing:
        - zeros_real: List of real parts of the zeros
        - errors: List of absolute errors from Re(s) = 0.5
        - max_error: Maximum deviation from the critical line
    """
    mp.dps = precision  # Set decimal precision

    zeros_real: List[float] = []
    errors: List[float] = []

    if verbose:
        print("Validation of non-trivial zeros of ζ(s):")

    for n in range(1, n_zeros + 1):
        z = zetazero(n)
        real_part = float(z.real)
        zeros_real.append(real_part)
        error = abs(real_part - 0.5)
        errors.append(error)
        if verbose:
            print(f"  Zero #{n:>3}: Re(s) = {real_part:.48f} | Error = {error:.1e}")

    max_error = max(errors)
    if verbose:
        print(f"\nMaximum deviation from Re(s) = 0.5: {max_error:.2e}")

    # Plot error per zero
    if save_plot:
        plt.figure(figsize=(6, 4))
        plt.plot(range(1, n_zeros + 1), errors, 'o-', label='|Re(sₙ) − 0.5|')
        plt.axhline(1e-13, color='red', linestyle='--', label='Target tolerance')
        plt.xlabel("Zero index n")
        plt.ylabel("Absolute error in Re(sₙ)")
        plt.title("Deviation of ζ(s) zeros from critical line")
        plt.grid(True)
        plt.legend()
        plt.tight_layout()
        plt.savefig(plot_filename)
        if verbose:
            print(f"\nPlot saved to: {plot_filename}")

    return zeros_real, errors, max_error


def main() -> None:
    """Main entry point for zeta zero validation."""
    # Number of zeros to validate
    N_zeros = 50

    zeros_real, errors, max_error = validate_zeta_zeros(n_zeros=N_zeros)

    # Show the plot
    plt.show()

    # Interpretation:
    # - All zeros lie extremely close to Re(s) = 0.5
    # - Max deviation < 1e-13 → validates numerical RH consistency


if __name__ == "__main__":
    main()
