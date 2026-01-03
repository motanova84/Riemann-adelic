"""Entry point for the extended RH & D≡Ξ validation workflow."""
from __future__ import annotations

import argparse
import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict

from validation.certification_system import CertificationSystem
from validation.rh_ds_core import RiemannHypothesisValidator, ValidationResult, ValidationStatus


def run_validation(precision: int, max_zeros: int) -> Dict[str, ValidationResult]:
    validator = RiemannHypothesisValidator(precision=precision)
    results = {
        "critical_line": validator.validate_critical_line_zeros(max_zeros=max_zeros),
        "ds_equivalence": validator.validate_ds_equiv_xi(),
        "non_vanishing": validator.validate_non_vanishing_property(),
    }
    return results


def serialise_results(results: Dict[str, ValidationResult], precision: int, max_zeros: int) -> Dict[str, Any]:
    summary = {name: result.to_dict() for name, result in results.items()}
    all_passed = all(res.status == ValidationStatus.PASSED for res in results.values())
    payload = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "precision": precision,
        "max_zeros": max_zeros,
        "overall_status": "PASSED" if all_passed else "FAILED",
        "all_passed": all_passed,
        "components": summary,
    }
    payload["critical_line_samples"] = summary.get("critical_line", {}).get("metrics", {}).get(
        "imaginary_parts", []
    )
    return payload


def save_results(payload: Dict[str, Any]) -> Path:
    output_dir = Path("data/validation/results")
    output_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    path = output_dir / f"rh_ds_validation_{timestamp}.json"
    path.write_text(json.dumps(payload, indent=2), encoding="utf8")
    return path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run the RH & D≡Ξ validation workflow")
    parser.add_argument("--precision", type=int, default=30, help="Decimal precision for mpmath")
    parser.add_argument("--max-zeros", type=int, default=200, help="Number of zeros to sample")
    parser.add_argument("--generate-certificates", action="store_true", help="Emit JSON certificates")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    results = run_validation(args.precision, args.max_zeros)
    payload = serialise_results(results, args.precision, args.max_zeros)
    output_path = save_results(payload)

    print("\nValidation summary:")
    for name, result in results.items():
        icon = "✅" if result.status == ValidationStatus.PASSED else "❌"
        print(f"  {icon} {name}: {result.status.value}")
        print(f"     {result.details}")

    print(f"\nResults stored at {output_path}")

    if args.generate_certificates:
        certification = CertificationSystem(precision=args.precision)
        certification.generate_certificate("CRITICAL_LINE", payload["components"]["critical_line"])
        certification.generate_certificate("DS_EQUIVALENCE", payload["components"]["ds_equivalence"])
        certification.generate_certificate("NON_VANISHING", payload["components"]["non_vanishing"])
        certification.generate_combined_certificate(payload)
        print("Certificates generated in data/validation/certificates")

    return 0 if payload["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
