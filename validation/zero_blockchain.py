#!/usr/bin/env python3
"""Immutable SHA-512 chain of critical-line zeta zeros."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Tuple

import mpmath as mp


@dataclass
class ZeroBlock:
    index: int
    critical_real: float
    zero_imag: float
    zeta_abs_residual: float
    residual_tolerance: float
    source: str
    previous_hash: str
    block_hash_sha512: str


def _block_payload(block: ZeroBlock) -> Dict[str, Any]:
    data = asdict(block).copy()
    data.pop("block_hash_sha512", None)
    return data


def _hash_payload(payload: Dict[str, Any]) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha512(canonical.encode("utf-8")).hexdigest()


def _load_zero_values(repo_root: Path, max_zeros: int) -> Tuple[List[float], str]:
    candidates = [
        repo_root / "data" / "external" / "zeros_t1e8.txt",
        repo_root / "zeros" / "zeros_t1e8.txt",
        repo_root / "data" / "validation" / "known_zeros.txt",
    ]
    zeros: List[float] = []
    for path in candidates:
        if not path.exists():
            continue
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                if len(zeros) >= max_zeros:
                    break
                token = line.strip()
                if not token:
                    continue
                try:
                    zeros.append(float(token))
                except ValueError:
                    continue
        if zeros:
            return zeros, str(path.relative_to(repo_root))

    for idx in range(1, max_zeros + 1):
        zeros.append(float(mp.zetazero(idx)))
    return zeros, "mpmath.zetazero:fallback"


def build_zero_chain(
    repo_root: Path,
    *,
    max_zeros: int = 128,
    precision: int = 50,
    residual_tolerance: float = 1e-7,
) -> Dict[str, Any]:
    mp.mp.dps = precision
    zeros, source = _load_zero_values(repo_root, max_zeros=max_zeros)

    blocks: List[ZeroBlock] = []
    prev_hash = "GENESIS"
    for idx, imag in enumerate(zeros):
        s = mp.mpc("0.5", imag)
        residual = float(abs(mp.zeta(s)))
        block = ZeroBlock(
            index=idx,
            critical_real=0.5,
            zero_imag=float(imag),
            zeta_abs_residual=residual,
            residual_tolerance=residual_tolerance,
            source=source,
            previous_hash=prev_hash,
            block_hash_sha512="",
        )
        block.block_hash_sha512 = _hash_payload(_block_payload(block))
        blocks.append(block)
        prev_hash = block.block_hash_sha512

    max_residual = max((b.zeta_abs_residual for b in blocks), default=0.0)
    chain_payload = {
        "type": "QCAL_CRITICAL_ZERO_IMMUTABLE_CHAIN",
        "timestamp_utc": datetime.utcnow().isoformat() + "Z",
        "critical_line_real_part": 0.5,
        "precision_dps": precision,
        "residual_tolerance": residual_tolerance,
        "zero_count": len(blocks),
        "source": source,
        "blocks": [asdict(b) for b in blocks],
        "tip_hash_sha512": prev_hash,
        "max_residual": max_residual,
    }
    chain_payload["chain_hash_sha512"] = _hash_payload(
        {
            "type": chain_payload["type"],
            "critical_line_real_part": chain_payload["critical_line_real_part"],
            "precision_dps": chain_payload["precision_dps"],
            "residual_tolerance": chain_payload["residual_tolerance"],
            "zero_count": chain_payload["zero_count"],
            "source": chain_payload["source"],
            "tip_hash_sha512": chain_payload["tip_hash_sha512"],
            "blocks": chain_payload["blocks"],
        }
    )
    return chain_payload


def verify_zero_chain(chain_payload: Dict[str, Any]) -> Dict[str, Any]:
    blocks = chain_payload.get("blocks", [])
    expected_prev = "GENESIS"
    for raw in blocks:
        block = ZeroBlock(**raw)
        if block.critical_real != 0.5:
            return {"valid": False, "error": f"block {block.index} not on Re(s)=1/2"}
        if block.previous_hash != expected_prev:
            return {"valid": False, "error": f"block {block.index} previous hash mismatch"}
        recomputed = _hash_payload(_block_payload(block))
        if recomputed != block.block_hash_sha512:
            return {"valid": False, "error": f"block {block.index} hash mismatch"}
        expected_prev = block.block_hash_sha512

    if chain_payload.get("tip_hash_sha512") != expected_prev:
        return {"valid": False, "error": "tip hash mismatch"}
    return {"valid": True, "error": None}


def build_and_persist_zero_chain(
    repo_root: Path,
    *,
    max_zeros: int = 128,
    precision: int = 50,
    residual_tolerance: float = 1e-7,
    output_relpath: str = "data/validation/critical_zero_immutable_chain.json",
) -> Dict[str, Any]:
    payload = build_zero_chain(
        repo_root,
        max_zeros=max_zeros,
        precision=precision,
        residual_tolerance=residual_tolerance,
    )
    output_path = repo_root / output_relpath
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    verification = verify_zero_chain(payload)
    payload["chain_verification"] = verification
    output_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    payload["output_path"] = str(output_path)
    return payload

