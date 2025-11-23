"""Certificate helpers for the RH & D≡Ξ validation suite."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Dict


@dataclass
class MathematicalCertificate:
    certificate_id: str
    validation_type: str
    timestamp: str
    payload: Dict[str, Any]
    cryptographic_hash: str
    precision_used: int
    validator_signature: str

    def to_json(self) -> str:
        return json.dumps(asdict(self), indent=2)


class CertificationSystem:
    """Generate lightweight certificates describing validation outcomes."""

    def __init__(self, validator_name: str = "Riemann-Adelic-Validator", precision: int = 50) -> None:
        self.validator_name = validator_name
        self.precision = precision
        self.output_dir = Path("data/validation/certificates")
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def generate_certificate(self, validation_type: str, payload: Dict[str, Any]) -> MathematicalCertificate:
        timestamp = datetime.utcnow().isoformat() + "Z"
        certificate_id = f"{validation_type}_{timestamp.replace(':', '').replace('-', '')}"

        data_string = json.dumps(
            {
                "validator": self.validator_name,
                "timestamp": timestamp,
                "payload": payload,
            },
            sort_keys=True,
            default=str,
        )
        digest = hashlib.sha256(data_string.encode("utf8")).hexdigest()
        signature = hashlib.sha256(f"{self.validator_name}:{digest}".encode("utf8")).hexdigest()[:16]

        certificate = MathematicalCertificate(
            certificate_id=certificate_id,
            validation_type=validation_type,
            timestamp=timestamp,
            payload=payload,
            cryptographic_hash=digest,
            precision_used=self.precision,
            validator_signature=signature,
        )

        self._persist_certificate(certificate)
        return certificate

    def generate_combined_certificate(self, results: Dict[str, Any]) -> MathematicalCertificate:
        payload = {
            "overall_status": results.get("overall_status"),
            "all_passed": results.get("all_passed"),
            "components": results.get("components", {}),
            "timestamp": results.get("timestamp"),
        }
        return self.generate_certificate("COMPLETE_RH_DS_VALIDATION", payload)

    def _persist_certificate(self, certificate: MathematicalCertificate) -> None:
        path = self.output_dir / f"{certificate.certificate_id}.json"
        path.write_text(certificate.to_json())


__all__ = ["CertificationSystem", "MathematicalCertificate"]
