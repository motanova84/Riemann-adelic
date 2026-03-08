#!/usr/bin/env python3
"""
Independent Validation Script — Riemann Quinto Postulado
=========================================================

16 independent validation checks covering all mathematical aspects of the
three operators, the geometric validation function, and the SHA-256 certificate.

Usage::

    python validate_riemann_quinto_postulado.py [--json]

Flags:
    --json      Write full results to data/riemann_quinto_postulado_validation.json

Exit code:
    0  All 16 validations passed
    1  One or more validations failed

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    F0_QCAL,
    C_COHERENCE,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    verificar_geometria,
    activar_quinto_postulado,
)


# ---------------------------------------------------------------------------
# NumpyEncoder for JSON serialization
# ---------------------------------------------------------------------------

class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder for NumPy types."""

    def default(self, obj):
        if isinstance(obj, (np.integer, np.bool_)):
            return int(obj)
        if isinstance(obj, np.floating):
            return float(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        return super().default(obj)


# ---------------------------------------------------------------------------
# Validator class
# ---------------------------------------------------------------------------

class QuintoPostuladoValidator:
    """
    Independent validator for the Quinto Postulado framework.

    Runs 16 checks grouped into five categories:

        A. Module constants (2 checks)
        B. ScaleIdentityOperator (3 checks)
        C. SymbioticHamiltonianOperator (3 checks)
        D. RiemannZetaSpectrum (3 checks)
        E. Integration and certification (5 checks)
    """

    def __init__(self) -> None:
        self.checks: List[Dict] = []
        self.passed = 0
        self.failed = 0

    # ------------------------------------------------------------------
    # Helper
    # ------------------------------------------------------------------

    def _record(
        self,
        name: str,
        passed: bool,
        metrics: Dict,
        detail: str = "",
    ) -> None:
        status = "PASS" if passed else "FAIL"
        self.checks.append({
            "name": name,
            "status": status,
            "passed": passed,
            "metrics": metrics,
            "detail": detail,
        })
        if passed:
            self.passed += 1
            print(f"  ✅ [{self.passed + self.failed:02d}] {name}")
        else:
            self.failed += 1
            msg = f" — {detail}" if detail else ""
            print(f"  ❌ [{self.passed + self.failed:02d}] {name}{msg}")

    # ------------------------------------------------------------------
    # Category A — Module constants (2 checks)
    # ------------------------------------------------------------------

    def check_A1_qcal_constants(self) -> None:
        """A1: QCAL constants have the correct values."""
        ok = (
            abs(F0_QCAL - 141.7001) < 1e-6
            and abs(C_COHERENCE - 244.36) < 1e-4
            and abs(PSI_THRESHOLD - 0.888) < 1e-6
        )
        self._record(
            "A1 — QCAL constants correct",
            ok,
            {"F0_QCAL": F0_QCAL, "C_COHERENCE": C_COHERENCE,
             "PSI_THRESHOLD": PSI_THRESHOLD},
        )

    def check_A2_riemann_zeros(self) -> None:
        """A2: 30 known Riemann zeros are present and ordered."""
        ok = (
            len(RIEMANN_ZEROS) == 30
            and bool(np.all(np.diff(RIEMANN_ZEROS) > 0))
            and abs(RIEMANN_ZEROS[0] - 14.134725141734693790) < 1e-10
        )
        self._record(
            "A2 — 30 Riemann zeros present and ordered",
            ok,
            {"n_zeros": len(RIEMANN_ZEROS), "first_zero": float(RIEMANN_ZEROS[0])},
        )

    # ------------------------------------------------------------------
    # Category B — ScaleIdentityOperator (3 checks)
    # ------------------------------------------------------------------

    def check_B1_haar_measure(self) -> None:
        """B1: Haar measure weights are strictly positive and decreasing."""
        op = ScaleIdentityOperator()
        w = op.haar_weights_at_primes()
        ok = (
            bool(np.all(w > 0))
            and bool(np.all(w[:, 0] > w[:, 1]))
            and bool(np.all(w[:, 1] > w[:, 2]))
        )
        self._record(
            "B1 — Haar measure weights positive & decreasing",
            ok,
            {"shape": list(w.shape), "min_weight": float(w.min()),
             "max_weight": float(w.max())},
        )

    def check_B2_adelic_character_unitarity(self) -> None:
        """B2: Adelic character has unit modulus for all test points."""
        op = ScaleIdentityOperator()
        x_test = np.linspace(0.1, 5.0, 30)
        max_err = 0.0
        for p in op.primes:
            for x in x_test:
                chi = op.adelic_character(x, p)
                max_err = max(max_err, abs(abs(chi) - 1.0))
        ok = max_err < 1e-12
        self._record(
            "B2 — Adelic character unit modulus",
            ok,
            {"max_modulus_error": max_err},
            f"max_err={max_err:.2e}",
        )

    def check_B3_scale_psi(self) -> None:
        """B3: ScaleIdentityOperator coherence Ψ_S ≥ threshold and ≈ 0.984."""
        op = ScaleIdentityOperator()
        result = op.compute()
        ok = result.psi >= PSI_THRESHOLD and abs(result.psi - 0.984) < 0.005
        self._record(
            "B3 — ScaleIdentityOperator Ψ_S ≥ 0.888 and ≈ 0.984",
            ok,
            {"psi_S": round(result.psi, 6),
             "p_adic_truncation_error": round(result.p_adic_truncation_error, 8)},
        )

    # ------------------------------------------------------------------
    # Category C — SymbioticHamiltonianOperator (3 checks)
    # ------------------------------------------------------------------

    def check_C1_hamiltonian_hermitian(self) -> None:
        """C1: Berry–Keating Hamiltonian is Hermitian after symmetrization."""
        op = SymbioticHamiltonianOperator()
        H = op.build_hamiltonian()
        herm_err = op.hermiticity_error(H)
        ok = herm_err < 1e-12
        self._record(
            "C1 — Hamiltonian Hermitian (‖H−H†‖/‖H‖ < 1e-12)",
            ok,
            {"hermiticity_error": herm_err},
        )

    def check_C2_commutator_finite(self) -> None:
        """C2: Scale-Hamiltonian commutator norm is finite and small."""
        op = SymbioticHamiltonianOperator()
        H = op.build_hamiltonian()
        comm = op.commutator_norm(H)
        ok = np.isfinite(comm) and comm >= 0.0 and comm < 0.5
        self._record(
            "C2 — Commutator ‖[S,H]‖ finite and < 0.5",
            ok,
            {"commutator_norm": round(comm, 6)},
        )

    def check_C3_hamiltonian_psi(self) -> None:
        """C3: SymbioticHamiltonianOperator coherence Ψ_H ≥ threshold and ≈ 0.892."""
        op = SymbioticHamiltonianOperator()
        result = op.compute()
        ok = result.psi >= PSI_THRESHOLD and abs(result.psi - 0.892) < 0.015
        self._record(
            "C3 — SymbioticHamiltonianOperator Ψ_H ≥ 0.888 and ≈ 0.892",
            ok,
            {"psi_H": round(result.psi, 6),
             "hermiticity_error": round(result.hermiticity_error, 10),
             "commutator_norm": round(result.commutator_norm, 6)},
        )

    # ------------------------------------------------------------------
    # Category D — RiemannZetaSpectrum (3 checks)
    # ------------------------------------------------------------------

    def check_D1_gue_statistics(self) -> None:
        """D1: Riemann zeros follow GUE spacing statistics (KS p-value > 0.3)."""
        op = RiemannZetaSpectrum()
        ks_gue, p_gue, ks_poi, p_poi = op.ks_distance()
        ok = p_gue > 0.3 and p_gue > p_poi
        self._record(
            "D1 — GUE spacing statistics (p_GUE > 0.3 > p_Poisson)",
            ok,
            {"ks_gue": round(ks_gue, 6), "p_gue": round(p_gue, 6),
             "ks_poisson": round(ks_poi, 6), "p_poisson": round(p_poi, 6)},
        )

    def check_D2_gue_cdf_valid(self) -> None:
        """D2: GUE CDF is a valid CDF (monotone, range [0,1])."""
        s = np.linspace(0, 5, 100)
        cdf = RiemannZetaSpectrum.gue_cdf(s)
        ok = (
            bool(np.all(cdf >= 0.0))
            and bool(np.all(cdf <= 1.0))
            and bool(np.all(np.diff(cdf) > 0))
        )
        self._record(
            "D2 — GUE CDF is monotone and bounded in [0,1]",
            ok,
            {"cdf_min": float(cdf.min()), "cdf_max": float(cdf.max()),
             "monotone": bool(np.all(np.diff(cdf) > 0))},
        )

    def check_D3_zeta_psi(self) -> None:
        """D3: RiemannZetaSpectrum coherence Ψ_Z ≥ threshold and ≈ 1.000."""
        op = RiemannZetaSpectrum()
        result = op.compute()
        ok = result.psi >= PSI_THRESHOLD and result.psi > 0.95
        self._record(
            "D3 — RiemannZetaSpectrum Ψ_Z ≥ 0.888 and ≈ 1.000",
            ok,
            {"psi_Z": round(result.psi, 6),
             "gue_ks_pvalue": round(result.gue_ks_pvalue, 6),
             "poisson_ks_pvalue": round(result.poisson_ks_pvalue, 6)},
        )

    # ------------------------------------------------------------------
    # Category E — Integration and certification (5 checks)
    # ------------------------------------------------------------------

    def check_E1_global_coherence(self) -> None:
        """E1: Global geometric-mean coherence Ψ_global ≥ threshold."""
        s_res = ScaleIdentityOperator().compute()
        h_res = SymbioticHamiltonianOperator().compute()
        z_res = RiemannZetaSpectrum().compute()
        psi_global = float((s_res.psi * h_res.psi * z_res.psi) ** (1.0 / 3.0))
        ok = psi_global >= PSI_THRESHOLD and abs(psi_global - 0.957) < 0.005
        self._record(
            "E1 — Global Ψ_global ≥ 0.888 and ≈ 0.957",
            ok,
            {"psi_S": round(s_res.psi, 6), "psi_H": round(h_res.psi, 6),
             "psi_Z": round(z_res.psi, 6), "psi_global": round(psi_global, 6)},
        )

    def check_E2_geometry_validation(self) -> None:
        """E2: verificar_geometria() returns True with canonical message."""
        s_res = ScaleIdentityOperator().compute()
        h_res = SymbioticHamiltonianOperator().compute()
        z_res = RiemannZetaSpectrum().compute()
        valid, msg = verificar_geometria(s_res, h_res, z_res)
        ok = valid and "✓ Quinto Postulado verificado" in msg and "QCAL ∞³" in msg
        self._record(
            "E2 — verificar_geometria() returns True with canonical message",
            ok,
            {"valid": valid, "message": msg},
        )

    def check_E3_sha256_certificate(self) -> None:
        """E3: activar_quinto_postulado() generates a valid 64-hex SHA-256."""
        tmp_dir = repo_root / "data"
        result = activar_quinto_postulado(
            save_certificate=True, output_dir=tmp_dir
        )
        sha = result.certificate_sha256
        ok = (
            len(sha) == 64
            and all(c in "0123456789abcdef" for c in sha)
            and result.geometry_valid
        )
        self._record(
            "E3 — SHA-256 certificate generated and valid",
            ok,
            {"sha256_prefix": sha[:16] + "…",
             "geometry_valid": result.geometry_valid},
        )

    def check_E4_certificate_json(self) -> None:
        """E4: Certificate JSON has all required fields and correct DOI."""
        cert_path = repo_root / "data" / "riemann_quinto_postulado_certificate.json"
        if not cert_path.exists():
            activar_quinto_postulado(
                save_certificate=True, output_dir=cert_path.parent
            )
        with open(cert_path, encoding="utf-8") as fh:
            cert = json.load(fh)
        required_keys = [
            "timestamp", "qcal_frequency", "operators",
            "psi_global", "geometry_valid", "sha256", "doi",
        ]
        has_all = all(k in cert for k in required_keys)
        doi_ok = cert.get("doi") == "10.5281/zenodo.17379721"
        has_ops = all(
            k in cert["operators"]
            for k in ["ScaleIdentityOperator",
                       "SymbioticHamiltonianOperator",
                       "RiemannZetaSpectrum"]
        )
        ok = has_all and doi_ok and has_ops
        self._record(
            "E4 — Certificate JSON complete with correct DOI",
            ok,
            {"has_required_keys": has_all, "doi_correct": doi_ok,
             "has_all_operators": has_ops},
        )

    def check_E5_full_activation_reproducible(self) -> None:
        """E5: Two separate activations both succeed (geometry_valid=True)."""
        r1 = activar_quinto_postulado(save_certificate=False)
        r2 = activar_quinto_postulado(save_certificate=False)
        ok = r1.geometry_valid and r2.geometry_valid
        self._record(
            "E5 — Two activations both pass geometry validation",
            ok,
            {"run1_valid": r1.geometry_valid, "run2_valid": r2.geometry_valid,
             "run1_psi": round(r1.psi_global, 6),
             "run2_psi": round(r2.psi_global, 6)},
        )

    # ------------------------------------------------------------------
    # Run all checks
    # ------------------------------------------------------------------

    def run_all(self) -> bool:
        """Run all 16 validation checks and return True iff all pass."""
        print("\n" + "=" * 65)
        print("  QUINTO POSTULADO — Validación Independiente  (16/16)")
        print(f"  f₀ = {F0_QCAL} Hz  ·  C^∞ = {C_COHERENCE}")
        print("=" * 65 + "\n")

        print("  Categoría A — Constantes del módulo")
        self.check_A1_qcal_constants()
        self.check_A2_riemann_zeros()

        print("\n  Categoría B — ScaleIdentityOperator")
        self.check_B1_haar_measure()
        self.check_B2_adelic_character_unitarity()
        self.check_B3_scale_psi()

        print("\n  Categoría C — SymbioticHamiltonianOperator")
        self.check_C1_hamiltonian_hermitian()
        self.check_C2_commutator_finite()
        self.check_C3_hamiltonian_psi()

        print("\n  Categoría D — RiemannZetaSpectrum")
        self.check_D1_gue_statistics()
        self.check_D2_gue_cdf_valid()
        self.check_D3_zeta_psi()

        print("\n  Categoría E — Integración y Certificación")
        self.check_E1_global_coherence()
        self.check_E2_geometry_validation()
        self.check_E3_sha256_certificate()
        self.check_E4_certificate_json()
        self.check_E5_full_activation_reproducible()

        total = self.passed + self.failed
        print(f"\n{'=' * 65}")
        if self.failed == 0:
            print(
                f"  ✅ {self.passed}/{total} validaciones PASADAS  "
                f"— Quinto Postulado CONFIRMADO"
            )
        else:
            print(
                f"  ❌ {self.passed}/{total} validaciones pasadas, "
                f"{self.failed} fallidas"
            )
        print("=" * 65 + "\n")

        return self.failed == 0


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def main() -> int:
    """Run validation and optionally save results to JSON."""
    save_json = "--json" in sys.argv

    validator = QuintoPostuladoValidator()
    all_passed = validator.run_all()

    if save_json:
        out_dir = repo_root / "data"
        out_dir.mkdir(exist_ok=True)
        summary = {
            "timestamp": datetime.utcnow().isoformat(),
            "qcal_frequency": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "total_checks": validator.passed + validator.failed,
            "passed": validator.passed,
            "failed": validator.failed,
            "all_passed": all_passed,
            "checks": validator.checks,
        }
        out_path = out_dir / "riemann_quinto_postulado_validation.json"
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(summary, fh, indent=2, cls=NumpyEncoder, ensure_ascii=False)
        print(f"  JSON results saved to: {out_path}\n")

    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
