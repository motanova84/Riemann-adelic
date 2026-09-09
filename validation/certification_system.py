"""Certificate helpers for the RH & D≡Ξ validation suite."""
from __future__ import annotations

import hashlib
import json
import subprocess
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Optional

from validation.zero_blockchain import build_and_persist_zero_chain


@dataclass
class MathematicalCertificate:
    certificate_id: str
    validation_type: str
    timestamp: str
    payload: Dict[str, Any]
    evidence: Dict[str, Any]
    cryptographic_hash: str
    cryptographic_hash_sha512: str
    precision_used: int
    validator_signature: str
    certificate_kind: str = "generic"

    def to_json(self) -> str:
        return json.dumps(asdict(self), indent=2)


class CertificationSystem:
    """Generate lightweight certificates describing validation outcomes."""

    def __init__(self, validator_name: str = "Riemann-Adelic-Validator", precision: int = 50) -> None:
        self.validator_name = validator_name
        self.precision = precision
        self.output_dir = Path("data/validation/certificates")
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.repo_root = Path(__file__).resolve().parents[1]

    def _file_sha256(self, relative_path: str) -> Optional[str]:
        path = self.repo_root / relative_path
        if not path.exists():
            return None
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(65536), b""):
                digest.update(chunk)
        return digest.hexdigest()

    def _git_commit(self) -> str:
        try:
            result = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                check=False,
            )
            return result.stdout.strip() if result.returncode == 0 else "unknown"
        except Exception:
            return "unknown"

    def _build_evidence(self, extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        zero_chain = build_and_persist_zero_chain(
            self.repo_root,
            max_zeros=256,
            precision=max(30, self.precision),
            residual_tolerance=1e-7,
        )
        evidence = {
            "git_commit": self._git_commit(),
            "lean_toolchain_sha256": self._file_sha256("formalization/lean/lean-toolchain"),
            "lake_manifest_sha256": self._file_sha256("formalization/lean/lake-manifest.json"),
            "requirements_sha256": self._file_sha256("requirements.txt"),
            "sat_summary_sha256": self._file_sha256("certificates/sat/certificates_summary.json"),
            "critical_line_zero_source": zero_chain["source"],
            "critical_line_zero_count": zero_chain["zero_count"],
            "critical_line_zero_real_part": zero_chain["critical_line_real_part"],
            "critical_line_zero_seal_sha512": zero_chain["chain_hash_sha512"],
            "critical_zero_tip_hash_sha512": zero_chain["tip_hash_sha512"],
            "critical_zero_chain_file": zero_chain["output_path"],
            "critical_zero_chain_valid": bool(zero_chain.get("chain_verification", {}).get("valid")),
            "critical_zero_max_residual": zero_chain.get("max_residual"),
            "generated_at_utc": datetime.utcnow().isoformat() + "Z",
        }
        if extra:
            evidence.update(extra)
        return evidence

    def generate_certificate(
        self,
        validation_type: str,
        payload: Dict[str, Any],
        *,
        certificate_kind: str = "generic",
        extra_evidence: Optional[Dict[str, Any]] = None,
    ) -> MathematicalCertificate:
        timestamp = datetime.utcnow().isoformat() + "Z"
        certificate_id = f"{validation_type}_{timestamp.replace(':', '').replace('-', '')}"
        evidence = self._build_evidence(extra=extra_evidence)

        data_string = json.dumps(
            {
                "validator": self.validator_name,
                "timestamp": timestamp,
                "payload": payload,
                "evidence": evidence,
                "kind": certificate_kind,
            },
            sort_keys=True,
            default=str,
        )
        digest = hashlib.sha256(data_string.encode("utf8")).hexdigest()
        digest_sha512 = hashlib.sha512(data_string.encode("utf8")).hexdigest()
        signature = hashlib.sha256(f"{self.validator_name}:{digest_sha512}".encode("utf8")).hexdigest()[:16]

        certificate = MathematicalCertificate(
            certificate_id=certificate_id,
            validation_type=validation_type,
            timestamp=timestamp,
            payload=payload,
            evidence=evidence,
            cryptographic_hash=digest,
            cryptographic_hash_sha512=digest_sha512,
            precision_used=self.precision,
            validator_signature=signature,
            certificate_kind=certificate_kind,
        )

        self._persist_certificate(certificate)
        return certificate

    def generate_formal_certificate(self, payload: Dict[str, Any]) -> MathematicalCertificate:
        return self.generate_certificate(
            "FORMAL_VALIDATION",
            payload,
            certificate_kind="formal",
            extra_evidence={"certificate_scope": "lean_axioms_and_structure"},
        )

    def generate_numeric_certificate(self, payload: Dict[str, Any]) -> MathematicalCertificate:
        return self.generate_certificate(
            "NUMERIC_VALIDATION",
            payload,
            certificate_kind="numeric",
            extra_evidence={"certificate_scope": "rh_v5_sat_weil_weyl"},
        )

    def generate_combined_certificate(self, results: Dict[str, Any]) -> MathematicalCertificate:
        payload = {
            "overall_status": results.get("overall_status"),
            "all_passed": results.get("all_passed"),
            "components": results.get("components", {}),
            "timestamp": results.get("timestamp"),
        }
        return self.generate_certificate(
            "COMPLETE_RH_DS_VALIDATION",
            payload,
            certificate_kind="combined",
            extra_evidence={"certificate_scope": "aggregated"},
        )

    def generate_dual_certificates(
        self,
        *,
        formal_payload: Dict[str, Any],
        numeric_payload: Dict[str, Any],
    ) -> Dict[str, MathematicalCertificate]:
        formal = self.generate_formal_certificate(formal_payload)
        numeric = self.generate_numeric_certificate(numeric_payload)
        return {"formal": formal, "numeric": numeric}

    def _persist_certificate(self, certificate: MathematicalCertificate) -> None:
        path = self.output_dir / f"{certificate.certificate_id}.json"
        path.write_text(certificate.to_json())


__all__ = ["CertificationSystem", "MathematicalCertificate"]
