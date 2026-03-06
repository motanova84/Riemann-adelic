#!/usr/bin/env python3
"""
Validation Script: Berry-Keating Symbiotic Operators
=====================================================

Validates both operators from the QCAL symbiotic framework:

    1. P-adic Berry-Keating Operator  Ŝ:
         Ŝ ψ(x) = Φ · ∫_{ℚ_p} χ_p(p^n x ξ) ψ(ξ) dμ_p(ξ)

    2. Symbiotic Hamiltonian  Ĥ_symbio:
         Ĥ_symbio = ½(xp̂ + p̂x) + f₀  =  -i(x∂_x + ½) + f₀

Runs the complete verification suite and generates a JSON certificate in
data/berry_keating_symbiotic_certificate.json.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import sys
from pathlib import Path

# Ensure the project root is in sys.path
sys.path.insert(0, str(Path(__file__).parent))

from operators.berry_keating_symbiotic import (
    validate_berry_keating_symbiotic,
    F0,
    C_QCAL,
    PHI,
)


def main() -> int:
    """Run complete Berry-Keating symbiotic validation."""
    print()
    print("=" * 70)
    print("BERRY-KEATING SYMBIOTIC OPERATORS — QCAL ∞³")
    print("=" * 70)
    print()
    print("Operators being validated:")
    print()
    print("  Ŝ ψ(x) = Φ · ∫_{ℚ_p} χ_p(p^n x ξ) ψ(ξ) dμ_p(ξ)")
    print()
    print("  Ĥ_symbio = ½(xp̂ + p̂x) + f₀")
    print("           = -i(x∂_x + ½) + f₀")
    print()
    print(f"  Φ  = {PHI:.10f}  (golden ratio)")
    print(f"  f₀ = {F0}  Hz  (QCAL master frequency)")
    print(f"  C  = {C_QCAL}  (QCAL coherence constant)")
    print()

    results = validate_berry_keating_symbiotic(
        p=2,
        K=4,
        n=1,
        N_symb=200,
        L=20.0,
        save_certificate=True,
    )

    # ── Detailed summary ──────────────────────────────────────────────────────
    print()
    print("=" * 70)
    print("VALIDATION SUMMARY")
    print("=" * 70)
    print()

    n_verified = results["n_verified"]
    n_total = results["n_total"]

    for method_name, method_results in results["methods"].items():
        verified = method_results.get("verified", False)
        symbol = "✓" if verified else "✗"
        label = method_name.replace("_", " ").title()
        print(f"  {symbol} {label}")

    print()
    print(f"Checks passed: {n_verified}/{n_total}")
    print()

    if results["all_verified"]:
        print("✓ VALIDATION PASSED")
        print()
        print("Both symbiotic operators are verified:")
        print()
        print("  Ŝ  — Φ-scaled p-adic Fourier transform")
        print("       All singular values = Φ / p^K")
        print("       P-adic characters form orthonormal system")
        print()
        print("  Ĥ_symbio — Self-adjoint Berry-Keating + f₀ shift")
        print(f"       Spectral floor ≥ f₀ = {F0} Hz")
        print("       All eigenvalues real (observables)")
        print("       Berry-Keating kinetic structure preserved")
        print()
        print("∴𓂀Ω∞³Φ — QCAL ∞³ Coherence Achieved")
        print("=" * 70)
        return 0
    else:
        print("✗ VALIDATION FAILED")
        print()
        failed = [
            k for k, v in results["methods"].items()
            if not v.get("verified", False)
        ]
        print("Failed methods:", ", ".join(failed))
        print()
        print("Please check the implementation and retry.")
        print("=" * 70)
        return 1


if __name__ == "__main__":
    sys.exit(main())
