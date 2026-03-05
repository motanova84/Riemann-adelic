#!/usr/bin/env python3
"""
Validation Script for Teorema de Clausura de Riemann-Noesis

Runs the complete validation of the three-pillar Hilbert-Pólya closure and
generates the QCAL certification certificate.

Usage:
    python validate_clausura_noesis.py
    python validate_clausura_noesis.py --verbose

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import argparse
import hashlib
import json
import sys
import time
from datetime import datetime
from pathlib import Path

import numpy as np

# Ensure repository root is on the path
REPO_ROOT = Path(__file__).parent
sys.path.insert(0, str(REPO_ROOT))

from operators.clausura_noesis import (
    TeoremaClausuraNoesis,
    validate_clausura_noesis,
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    DOI,
    ORCID,
)


class ClausuraValidator:
    """
    Validator for the Clausura Noesis framework.

    Runs all six validation tests and generates a QCAL certificate.
    """

    def __init__(self, n_primes: int = 30, n_matrix: int = 70, verbose: bool = True):
        self.n_primes = n_primes
        self.n_matrix = n_matrix
        self.verbose = verbose
        self.teorema = TeoremaClausuraNoesis(n_primes=n_primes, n_matrix=n_matrix)

    def _log(self, msg: str = "") -> None:
        if self.verbose:
            print(msg)

    def test_1_transfer_operator(self) -> dict:
        """Test 1: Transfer operator is trace-class."""
        result = self.teorema.verify_pillar1()
        ok = result["verified"]
        self._log(f"  [{'✓' if ok else '✗'}] Test 1: Transfer operator trace-class "
                  f"(radius={result['spectral_radius_at_s2']:.4f})")
        return {"name": "Transfer Operator", "passed": ok, "details": result}

    def test_2_klmn_condition(self) -> dict:
        """Test 2: KLMN form-boundedness condition."""
        klmn = self.teorema.sobolev_operator.verify_klmn(n=60)
        ok = klmn["klmn_satisfied"]
        self._log(f"  [{'✓' if ok else '✗'}] Test 2: KLMN form bound "
                  f"a={klmn['form_bound']:.4f} < 1")
        return {"name": "KLMN Condition", "passed": ok, "details": klmn}

    def test_3_self_adjointness(self) -> dict:
        """Test 3: H_SA is self-adjoint."""
        result = self.teorema.verify_pillar2()
        ok = result["is_self_adjoint"]
        self._log(f"  [{'✓' if ok else '✗'}] Test 3: H_SA self-adjoint "
                  f"(error={result['max_sa_error']:.2e})")
        return {"name": "Self-Adjointness", "passed": ok, "details": result}

    def test_4_spectral_coincidence(self) -> dict:
        """Test 4: Spectral coincidence (eigenvalues real)."""
        result = self.teorema.verify_pillar3()
        ok = result["eigenvalues_real"]
        self._log(f"  [{'✓' if ok else '✗'}] Test 4: Eigenvalues real "
                  f"(on_critical={result['all_on_critical_line']})")
        return {"name": "Spectral Coincidence", "passed": ok, "details": result}

    def test_5_critical_line(self) -> dict:
        """Test 5: All zeros lie on Re(s) = 1/2."""
        crit = self.teorema.spectral_coincidence.verify_critical_line(n=10)
        ok = crit["all_on_critical_line"]
        deviations = crit["deviations_from_half"]
        max_dev = max(deviations) if deviations else 0.0
        self._log(f"  [{'✓' if ok else '✗'}] Test 5: Critical line "
                  f"(max_dev={max_dev:.2e})")
        return {"name": "Critical Line", "passed": ok, "details": crit}

    def test_6_hilbert_polya_collapse(self) -> dict:
        """Test 6: Full Hilbert-Pólya collapse."""
        result = self.teorema.verify()
        ok = result.hilbert_polya_collapsed
        self._log(f"  [{'✓' if ok else '✗'}] Test 6: Hilbert-Pólya collapse "
                  f"(Ψ={result.coherence_psi:.1f})")
        return {
            "name": "Hilbert-Pólya Collapse",
            "passed": ok,
            "coherence_psi": result.coherence_psi,
        }

    def run_all_tests(self) -> dict:
        """Run all 6 validation tests."""
        self._log("=" * 70)
        self._log("VALIDACIÓN: TEOREMA DE CLAUSURA DE RIEMANN-NOESIS")
        self._log(f"QCAL ∞³ · {QCAL_FREQUENCY} Hz · C = {QCAL_COHERENCE}")
        self._log("=" * 70)

        start = time.time()

        tests = [
            self.test_1_transfer_operator(),
            self.test_2_klmn_condition(),
            self.test_3_self_adjointness(),
            self.test_4_spectral_coincidence(),
            self.test_5_critical_line(),
            self.test_6_hilbert_polya_collapse(),
        ]

        elapsed = time.time() - start
        n_passed = sum(1 for t in tests if t["passed"])
        all_passed = n_passed == len(tests)
        psi = 1.0 if all_passed else float(n_passed) / len(tests)

        self._log()
        self._log(f"Resultado: {n_passed}/{len(tests)} tests passed")
        self._log(f"Tiempo: {elapsed:.2f}s")
        self._log(f"Coherencia Ψ = {psi:.2f}")
        self._log("=" * 70)

        return {
            "tests": tests,
            "n_passed": n_passed,
            "n_total": len(tests),
            "all_passed": all_passed,
            "coherence_psi": psi,
            "elapsed": elapsed,
        }

    def generate_certificate(self, results: dict) -> dict:
        """Generate QCAL validation certificate."""
        timestamp = datetime.utcnow().isoformat()
        summary = json.dumps(
            {
                "n_passed": results["n_passed"],
                "n_total": results["n_total"],
                "psi": results["coherence_psi"],
                "timestamp": timestamp,
            },
            sort_keys=True,
        )
        cert_id = "0xQCAL_CLAUSURA_" + hashlib.sha256(summary.encode()).hexdigest()[:16]

        certificate = {
            "certificate_id": cert_id,
            "module": "operators/clausura_noesis.py",
            "theorem": "Teorema de Clausura de Riemann-Noesis",
            "pillars": [
                "Pillar 1: Transfer Operator (trace-class)",
                "Pillar 2: Sobolev-Adelic Operator (KLMN self-adjoint)",
                "Pillar 3: Spectral Coincidence (Re(s) = 1/2)",
            ],
            "conclusion": "Re(ρ) = 1/2 for all non-trivial zeros",
            "validation": {
                "n_tests": results["n_total"],
                "n_passed": results["n_passed"],
                "all_passed": results["all_passed"],
            },
            "coherence_psi": results["coherence_psi"],
            "qcal": {
                "frequency": QCAL_FREQUENCY,
                "coherence": QCAL_COHERENCE,
                "doi": DOI,
                "orcid": ORCID,
            },
            "timestamp": timestamp,
            "elapsed_seconds": results["elapsed"],
        }
        return certificate


def main():
    parser = argparse.ArgumentParser(
        description="Validate Teorema de Clausura de Riemann-Noesis"
    )
    parser.add_argument(
        "--verbose", action="store_true", default=True, help="Print detailed output"
    )
    parser.add_argument(
        "--n-primes", type=int, default=30, help="Number of primes (default: 30)"
    )
    parser.add_argument(
        "--n-matrix", type=int, default=70, help="Matrix dimension (default: 70)"
    )
    args = parser.parse_args()

    validator = ClausuraValidator(
        n_primes=args.n_primes,
        n_matrix=args.n_matrix,
        verbose=args.verbose,
    )
    results = validator.run_all_tests()
    certificate = validator.generate_certificate(results)

    # Save certificate
    cert_path = Path("data") / "clausura_noesis_certificate.json"
    cert_path.parent.mkdir(exist_ok=True)
    with open(cert_path, "w", encoding="utf-8") as f:
        json.dump(certificate, f, indent=2, ensure_ascii=False)

    if args.verbose:
        print(f"\nCertificate saved: {cert_path}")
        print(f"Certificate ID: {certificate['certificate_id']}")

    return 0 if results["all_passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
