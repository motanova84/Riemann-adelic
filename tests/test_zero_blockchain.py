"""Tests for immutable critical-line zero blockchain."""

from __future__ import annotations

import json
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from validation.zero_blockchain import (
    build_and_persist_zero_chain,
    build_zero_chain,
    verify_zero_chain,
)


def test_build_zero_chain_anchors_critical_line():
    chain = build_zero_chain(PROJECT_ROOT, max_zeros=8, precision=30, residual_tolerance=1e-6)
    assert chain["zero_count"] == 8
    assert chain["critical_line_real_part"] == 0.5
    assert len(chain["chain_hash_sha512"]) == 128
    assert len(chain["tip_hash_sha512"]) == 128
    assert all(block["critical_real"] == 0.5 for block in chain["blocks"])


def test_verify_zero_chain_detects_tampering():
    chain = build_zero_chain(PROJECT_ROOT, max_zeros=5, precision=30, residual_tolerance=1e-6)
    assert verify_zero_chain(chain)["valid"] is True

    tampered = json.loads(json.dumps(chain))
    tampered["blocks"][2]["zero_imag"] += 1e-6
    result = verify_zero_chain(tampered)
    assert result["valid"] is False
    assert "hash mismatch" in result["error"]


def test_build_and_persist_zero_chain_writes_artifact():
    relpath = "data/validation/_tmp_critical_chain_test.json"
    chain = build_and_persist_zero_chain(
        PROJECT_ROOT,
        max_zeros=6,
        precision=30,
        residual_tolerance=1e-6,
        output_relpath=relpath,
    )
    output_path = Path(chain["output_path"])
    assert output_path.exists()
    assert chain["chain_verification"]["valid"] is True
    output_path.unlink(missing_ok=True)
