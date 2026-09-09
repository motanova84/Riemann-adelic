#!/usr/bin/env python3
"""Irrefutable validation protocol: strict formal + numeric gating."""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from core.validate_weil_spectral_bridge import run_bridge_validation
from sabio_infinity4 import SABIO_Infinity4
from validation.rh_ds_core import RiemannHypothesisValidator, ValidationStatus


@dataclass
class GateResult:
    name: str
    passed: bool
    details: str
    evidence: Dict[str, Any]


class IrrefutableProtocol:
    """Strict protocol with explicit failure on formal or numeric invariant breaks."""

    def __init__(self, repo_root: Path, precision: int = 30, max_zeros: int = 200) -> None:
        self.repo_root = repo_root
        self.precision = precision
        self.max_zeros = max_zeros

    def _check_required_file(self, rel_path: str) -> GateResult:
        path = self.repo_root / rel_path
        return GateResult(
            name=f"required_file:{rel_path}",
            passed=path.exists(),
            details="present" if path.exists() else "missing",
            evidence={"path": str(path)},
        )

    def _check_no_sorry(self, rel_path: str) -> GateResult:
        path = self.repo_root / rel_path
        if not path.exists():
            return GateResult(
                name=f"no_sorry:{rel_path}",
                passed=False,
                details="missing file",
                evidence={"path": str(path)},
            )
        content = path.read_text(encoding="utf-8")
        has_sorry = "sorry" in content
        return GateResult(
            name=f"no_sorry:{rel_path}",
            passed=not has_sorry,
            details="no sorry found" if not has_sorry else "contains sorry",
            evidence={"path": str(path)},
        )

    def run_formal_gates(self) -> Dict[str, Any]:
        gates: List[GateResult] = [
            self._check_required_file("formalization/lean/lean-toolchain"),
            self._check_required_file("formalization/lean/sabio/elan_omega_pure_validation.lean"),
            self._check_required_file("formalization/lean/RiemannAdelic/Coronacion_Final.lean"),
            self._check_no_sorry("formalization/lean/sabio/elan_omega_pure_validation.lean"),
            self._check_no_sorry("formalization/lean/QCAL_Hadamard/GAP1_log_holomorphic_of_entire_never_zero.lean"),
            self._check_no_sorry("formalization/lean/QCAL_Hadamard/GAP2_affine_log_of_order_one.lean"),
            self._check_no_sorry("formalization/lean/QCAL_Hadamard/GAP3_quotient_entire_never_zero.lean"),
            self._check_no_sorry("formalization/lean/QCAL_Hadamard/GAP4_order_atMostOne_of_quotient.lean"),
        ]
        passed = all(g.passed for g in gates)
        return {
            "passed": passed,
            "gates": [asdict(g) for g in gates],
            "summary": "formal gates passed" if passed else "formal gates failed",
        }

    def run_numeric_gates(self) -> Dict[str, Any]:
        validator = RiemannHypothesisValidator(precision=self.precision)
        critical_line = validator.validate_critical_line_zeros(max_zeros=self.max_zeros)
        ds_equiv = validator.validate_ds_equiv_xi()
        non_vanishing = validator.validate_non_vanishing_property()
        rh_core_passed = all(
            r.status == ValidationStatus.PASSED for r in (critical_line, ds_equiv, non_vanishing)
        )

        weil, spectral, bridge_passed = run_bridge_validation(
            repo_root=self.repo_root,
            max_zeros=max(200, self.max_zeros),
            max_primes=1000,
            precision=self.precision,
            fourier_a=0.05,
            sigma=250.0,
            max_prime_power=10,
            modes=10,
            tolerance=0.1,
            tail_compensation=True,
        )

        sabio = SABIO_Infinity4(precision=max(30, self.precision))
        matrix = sabio.validacion_matriz_simbiosis(
            test_aritmetico=True,
            test_geometrico=True,
            test_vibracional=True,
            test_cuantico=False,
            test_consciente=False,
        )
        sabio_core_error = None
        try:
            sabio.assert_core_invariants()
            sabio_core_passed = True
        except RuntimeError as exc:
            sabio_core_passed = False
            sabio_core_error = str(exc)

        sat_latest_report = self.repo_root / "certificates" / "sat" / "validation_report.json"
        sat_latest_available = sat_latest_report.exists()

        numeric_passed = rh_core_passed and bridge_passed and sabio_core_passed and sat_latest_available
        return {
            "passed": numeric_passed,
            "summary": "numeric gates passed" if numeric_passed else "numeric gates failed",
            "rh_core": {
                "passed": rh_core_passed,
                "critical_line": critical_line.to_dict(),
                "ds_equivalence": ds_equiv.to_dict(),
                "non_vanishing": non_vanishing.to_dict(),
            },
            "weil_weyl_bridge": {
                "passed": bridge_passed,
                "weil_audit": asdict(weil),
                "spectral_audit": asdict(spectral),
            },
            "sabio_core": {
                "passed": sabio_core_passed,
                "nivel_lean": matrix.nivel_lean,
                "nivel_sabio": matrix.nivel_sabio,
                "error": sabio_core_error,
            },
            "sat_latest_only": {
                "passed": sat_latest_available,
                "validation_report": str(sat_latest_report),
            },
        }

    def run(self) -> Dict[str, Any]:
        formal = self.run_formal_gates()
        numeric = self.run_numeric_gates()
        overall = bool(formal["passed"] and numeric["passed"])
        return {
            "timestamp": datetime.utcnow().isoformat() + "Z",
            "precision": self.precision,
            "max_zeros": self.max_zeros,
            "formal": formal,
            "numeric": numeric,
            "overall_passed": overall,
            "status": "PASSED" if overall else "FAILED",
        }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run irrefutable formal+numeric protocol")
    parser.add_argument("--precision", type=int, default=30)
    parser.add_argument("--max-zeros", type=int, default=200)
    parser.add_argument(
        "--output",
        type=str,
        default="data/validation/irrefutable_protocol_report.json",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    protocol = IrrefutableProtocol(repo_root=repo_root, precision=args.precision, max_zeros=args.max_zeros)
    report = protocol.run()
    output_path = repo_root / args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Irrefutable protocol report: {output_path}")
    return 0 if report["overall_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
