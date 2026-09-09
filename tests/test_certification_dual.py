"""Tests for dual certification (formal + numeric)."""

from __future__ import annotations

import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from validation.certification_system import CertificationSystem


def test_dual_certificates_are_generated_with_evidence(tmp_path):
    cert = CertificationSystem(precision=30)
    cert.output_dir = tmp_path
    cert.repo_root = PROJECT_ROOT

    generated = cert.generate_dual_certificates(
        formal_payload={"passed": True, "gates": []},
        numeric_payload={"passed": True, "rh_core": {}, "weil_weyl_bridge": {}},
    )

    assert set(generated.keys()) == {"formal", "numeric"}
    assert generated["formal"].certificate_kind == "formal"
    assert generated["numeric"].certificate_kind == "numeric"
    assert "git_commit" in generated["formal"].evidence
    assert "lean_toolchain_sha256" in generated["formal"].evidence
    assert "requirements_sha256" in generated["numeric"].evidence
    assert "critical_line_zero_seal_sha512" in generated["numeric"].evidence
    assert len(generated["numeric"].evidence["critical_line_zero_seal_sha512"]) == 128
    assert generated["numeric"].evidence["critical_zero_chain_valid"] is True
    assert generated["numeric"].evidence["critical_zero_chain_file"].endswith(
        "data/validation/critical_zero_immutable_chain.json"
    )
    assert generated["formal"].cryptographic_hash_sha512
    assert len(generated["formal"].cryptographic_hash_sha512) == 128
