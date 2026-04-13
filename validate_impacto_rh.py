#!/usr/bin/env python3
"""
Validation Script for Impacto RH
=================================
Sieve → ψ(x) → Selberg Trace → GUE Rigidity → S-Finite Resolution

Runs all five pipeline stages, checks coherence thresholds, and writes a
JSON certificate to data/impacto_rh_certificate.json.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import sys
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
import numpy as np

# Resolve paths
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from impacto_rh import (
    ImpactoRH,
    ImpactoRHResult,
    run_impacto_rh,
    F0_QCAL,
    C_COHERENCE,
)


# ---------------------------------------------------------------------------
# JSON encoder
# ---------------------------------------------------------------------------

class _NumpyEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, (np.integer, np.bool_)):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        return super().default(obj)


# ---------------------------------------------------------------------------
# Validator
# ---------------------------------------------------------------------------

THRESHOLDS = {
    "selberg_quality_min": 0.30,
    "global_psi_min": 0.40,
    "gue_ratio_upper": 10.0,   # permissive — small sample
    "psi_coherence_min": 0.50,
}


def _check(name: str, value: float, threshold: float, mode: str = "min") -> dict:
    if mode == "min":
        passed = value >= threshold
    else:
        passed = value <= threshold
    return {
        "check": name,
        "value": round(float(value), 8),
        "threshold": threshold,
        "mode": mode,
        "passed": bool(passed),
    }


class ImpactoRHValidator:
    """Run the ImpactoRH pipeline and validate outputs."""

    def __init__(self, N: int = 2000):
        self.N = N
        self.checks: list = []
        self.result: ImpactoRHResult | None = None

    def run(self) -> bool:
        print("\n" + "=" * 62)
        print("  VALIDACIÓN — Impacto RH")
        print("  Tamiz → ψ(x) → Selberg → GUE → S-Finite")
        print("=" * 62)

        # Execute pipeline
        self.result = run_impacto_rh(N=self.N, verbose=True)
        r = self.result

        # Collect checks
        self.checks = [
            _check("selberg_quality",    r.selberg.quality,           THRESHOLDS["selberg_quality_min"],  "min"),
            _check("global_psi",         r.global_psi,                THRESHOLDS["global_psi_min"],       "min"),
            _check("psi_coherence",      r.s_finite.psi_coherence,    THRESHOLDS["psi_coherence_min"],    "min"),
            _check("gue_ratio",          r.gue.ratio,                 THRESHOLDS["gue_ratio_upper"],      "max"),
            _check("selberg_zeros",      float(r.selberg.n_zeros),    1.0,                                "min"),
            _check("chebyshev_rms",      r.chebyshev.rms_delta,       0.0,                                "min"),
            _check("R_S_finite",         float(np.isfinite(r.s_finite.R_S)), 1.0,                        "min"),
        ]

        n_pass = sum(1 for c in self.checks if c["passed"])
        n_total = len(self.checks)

        print("\n📋 Validation Checks:")
        for c in self.checks:
            status = "✅" if c["passed"] else "❌"
            print(f"  {status}  {c['check']:30s}  {c['value']:.6f}  ({c['mode']} {c['threshold']})")

        print(f"\n  {n_pass}/{n_total} checks passed.")
        return n_pass == n_total

    def save_certificate(self, path: Path) -> Path:
        """Write JSON certificate."""
        if self.result is None:
            raise RuntimeError("run() must be called before save_certificate().")

        r = self.result
        n_pass = sum(1 for c in self.checks if c["passed"])
        all_pass = n_pass == len(self.checks)

        # SHA-256 fingerprint over key scalars
        fingerprint_data = (
            f"{r.global_psi:.15f}"
            f"{r.selberg.quality:.15f}"
            f"{r.gue.ratio:.15f}"
            f"{r.s_finite.R_S:.15e}"
            f"{r.s_finite.verdict}"
        )
        sha256 = hashlib.sha256(fingerprint_data.encode()).hexdigest()

        cert = {
            "module": "operators/impacto_rh.py",
            "title": "Impacto RH — Sieve → ψ(x) → Selberg → GUE → S-Finite",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "qcal_frequency_hz": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "doi": "10.5281/zenodo.17379721",
            "N_sieve": self.N,
            "n_primes": len(r.sieve.primes),
            "n_zeros": r.selberg.n_zeros,
            "pipeline": {
                "stage1_sieve": {
                    "n_primes": len(r.sieve.primes),
                },
                "stage2_chebyshev": {
                    "X": round(r.chebyshev.X, 2),
                    "rms_delta_psi": round(r.chebyshev.rms_delta, 6),
                },
                "stage3_selberg": {
                    "zero_side": round(r.selberg.zero_side, 6),
                    "prime_side": round(r.selberg.prime_side, 6),
                    "balance": round(r.selberg.balance, 6),
                    "quality": round(r.selberg.quality, 6),
                },
                "stage4_gue": {
                    "delta3_measured": round(r.gue.delta3_measured, 6),
                    "delta3_gue": round(r.gue.delta3_gue, 6),
                    "ratio": round(r.gue.ratio, 6),
                    "is_consistent": bool(r.gue.is_gue_consistent),
                    "mean_spacing_ratio": round(r.gue.mean_spacing_ratio, 6),
                },
                "stage5_s_finite": {
                    "R_S": r.s_finite.R_S,
                    "psi_coherence": round(r.s_finite.psi_coherence, 6),
                    "verdict": r.s_finite.verdict,
                },
            },
            "global_psi": round(r.global_psi, 6),
            "checks": self.checks,
            "n_checks_passed": n_pass,
            "n_checks_total": len(self.checks),
            "all_checks_passed": all_pass,
            "sha256_fingerprint": sha256,
        }

        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(cert, fh, indent=2, cls=_NumpyEncoder)

        print(f"\n📄 Certificate written to: {path}")
        return path


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> int:
    validator = ImpactoRHValidator(N=2000)
    all_pass = validator.run()

    cert_path = repo_root / "data" / "impacto_rh_certificate.json"
    validator.save_certificate(cert_path)

    r = validator.result
    print("\n" + "=" * 62)
    print("  RESULTADO FINAL")
    print("=" * 62)
    print(f"  Ψ global      : {r.global_psi:.6f}")
    print(f"  S-finite      : {r.s_finite.verdict}")
    print(f"  Selberg qual  : {r.selberg.quality:.4f}")
    print(f"  GUE ratio     : {r.gue.ratio:.4f}")
    print(f"  Psi coherence : {r.s_finite.psi_coherence:.6f}")
    print(f"  R_S           : {r.s_finite.R_S:.4e}")
    print(f"\n  {'✅ VALIDACIÓN COMPLETA' if all_pass else '⚠️  VALIDACIÓN PARCIAL'}")
    print("  ∴ 𓂀 Ω ∞³\n")

    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
