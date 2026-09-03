#!/usr/bin/env python3
"""
Audit latest SAT certificates (one per theorem) against closure checklist.
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


def _latest_by_theorem(cert_dir: Path) -> Dict[str, Tuple[Path, Dict[str, Any]]]:
    latest: Dict[str, Tuple[str, Path, Dict[str, Any]]] = {}
    for cert_file in sorted(cert_dir.glob("SAT_*.json")):
        try:
            cert = json.loads(cert_file.read_text(encoding="utf-8"))
        except Exception:
            continue
        theorem = cert.get("theorem_name")
        if not theorem:
            continue
        key = cert.get("timestamp") or cert_file.stem
        prev = latest.get(theorem)
        if prev is None or key >= prev[0]:
            latest[theorem] = (key, cert_file, cert)
    return {k: (v[1], v[2]) for k, v in latest.items()}


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit latest SAT certificates")
    parser.add_argument(
        "--cert-dir",
        default="certificates/sat",
        help="Directory containing SAT certificates",
    )
    parser.add_argument(
        "--expected-theorems",
        type=int,
        default=10,
        help="Expected number of latest certificates (one per theorem)",
    )
    args = parser.parse_args()

    cert_dir = Path(args.cert_dir)
    if not cert_dir.exists():
        print(f"❌ Directory not found: {cert_dir}")
        return 1

    latest = _latest_by_theorem(cert_dir)
    print(f"Auditing {len(latest)} latest certificates in {cert_dir}")

    failures_total: List[str] = []

    for theorem, (path, cert) in sorted(latest.items()):
        failures: List[str] = []

        compiles = cert.get("verification", {}).get("compilation", {}).get("compiles")
        error_message = cert.get("verification", {}).get("compilation", {}).get("error_message")
        content_found = cert.get("verification", {}).get("theorem_content_found")
        theorem_compiles = cert.get("sat_formula", {}).get("variables", {}).get("theorem_compiles")
        no_sorry = cert.get("sat_formula", {}).get("variables", {}).get("no_sorry")
        satisfied = cert.get("sat_formula", {}).get("satisfied")
        sorry_count = cert.get("proof_status", {}).get("sorry_count")
        file_exists = cert.get("file_info", {}).get("exists")
        file_sha = cert.get("file_info", {}).get("sha256")
        cert_hash = cert.get("cryptographic_proof", {}).get("certificate_hash")
        f0 = cert.get("qcal_signature", {}).get("base_frequency")

        if compiles is not True:
            failures.append("verification.compilation.compiles != true")
        if error_message is not None:
            failures.append("verification.compilation.error_message != null")
        if theorem_compiles is not True:
            failures.append("sat_formula.variables.theorem_compiles != true")
        if content_found is not True:
            failures.append("verification.theorem_content_found != true")
        if no_sorry is not True:
            failures.append("sat_formula.variables.no_sorry != true")
        if satisfied is not True:
            failures.append("sat_formula.satisfied != true")
        if sorry_count != 0:
            failures.append("proof_status.sorry_count != 0")
        if file_exists is not True:
            failures.append("file_info.exists != true")
        if not isinstance(file_sha, str) or len(file_sha) != 64:
            failures.append("file_info.sha256 invalid")
        if not isinstance(cert_hash, str) or len(cert_hash) != 64:
            failures.append("cryptographic_proof.certificate_hash missing/invalid")
        if f0 != "141.7001 Hz":
            failures.append('qcal_signature.base_frequency != "141.7001 Hz"')

        if failures:
            print(f"❌ {theorem}: {path.name}")
            for failure in failures:
                print(f"   - {failure}")
            failures_total.extend([f"{theorem}: {f}" for f in failures])
        else:
            print(f"✅ {theorem}: {path.name}")

    if len(latest) != args.expected_theorems:
        failures_total.append(
            f"latest certificate set size mismatch: expected {args.expected_theorems}, got {len(latest)}"
        )

    print("-" * 70)
    if failures_total:
        print(f"❌ SAT audit failed ({len(failures_total)} issue(s))")
        return 1

    print("✅ SAT audit passed: all latest certificates satisfy closure checklist")
    return 0


if __name__ == "__main__":
    sys.exit(main())
