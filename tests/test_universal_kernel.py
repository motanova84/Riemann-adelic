from __future__ import annotations

import json
from pathlib import Path

import pytest

from tools import universal_kernel
from tools.universal_kernel import UniversalKernelError


CONTEXT = {
    "dc": "http://purl.org/dc/elements/1.1/",
    "formal": "https://qcal.example/formal#",
    "sem": "https://qcal.example/semantic#",
    "hash": "https://qcal.example/hash#",
    "freq": "https://qcal.example/frequency#",
    "prov": "http://www.w3.org/ns/prov#",
}


def load_sample_descriptor(tmp_path: Path) -> Path:
    template = Path("schema/riemann_zeta.jsonld")
    data = json.loads(template.read_text(encoding="utf-8"))
    copy = tmp_path / template.name
    copy.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return copy


def compute_reference_hash() -> str:
    proof_path = Path("formalization/lean/RH_final.lean")
    proof_content = proof_path.read_text(encoding="utf-8")
    return universal_kernel.compute_sha256(proof_content)


def build_descriptor(
    target: Path,
    *,
    identifier: str,
    proof_path: Path,
    depends_on: list[str],
    axioms: list[str],
    kernel: str = "Dedukti",
) -> None:
    proof_text = proof_path.read_text(encoding="utf-8")
    proof_hash = universal_kernel.compute_sha256(proof_text)
    frequency = universal_kernel.hash_to_frequency(proof_hash)
    payload = {
        "@context": CONTEXT,
        "@id": identifier,
        "dc:title": f"Test descriptor for {identifier.split(':')[-1]}",
        "formal:kernel": kernel,
        "formal:proof": str(proof_path),
        "formal:axioms": axioms,
        "sem:dependsOn": depends_on,
        "hash:sha256": proof_hash,
        "freq:Hz": frequency,
        "freq:tolerance": universal_kernel.FREQUENCY_TOLERANCE,
    }
    target.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def test_compute_sha256_matches_python_hash():
    text = "theorem sample : True := trivial"
    digest = universal_kernel.compute_sha256(text)
    assert digest.startswith(universal_kernel.HASH_PREFIX)
    assert len(digest) == len(universal_kernel.HASH_PREFIX) + 64


def test_hash_to_frequency_is_deterministic():
    proofhash = "sha256-" + "0" * 64
    first = universal_kernel.hash_to_frequency(proofhash)
    second = universal_kernel.hash_to_frequency(proofhash)
    assert pytest.approx(first, rel=0, abs=1e-9) == second


def test_run_validation_accepts_sample_descriptor(tmp_path: Path):
    descriptor = load_sample_descriptor(tmp_path)
    results = universal_kernel.run_validation(
        [descriptor],
        baseline=universal_kernel.BASELINE_FREQUENCY,
        tolerance=universal_kernel.FREQUENCY_TOLERANCE,
        allowed_kernels=["Lean4"],
        update=False,
    )
    assert len(results) == 1
    result = results[0]
    assert result.all_ok()
    assert pytest.approx(result.frequency, rel=0, abs=1e-9) == result.computed_frequency
    assert result.declared_hash == compute_reference_hash()


def test_run_validation_updates_hash_and_frequency(tmp_path: Path):
    descriptor = load_sample_descriptor(tmp_path)
    data = json.loads(descriptor.read_text(encoding="utf-8"))
    data["hash:sha256"] = "sha256-" + "0" * 64
    data["freq:Hz"] = 140.0
    descriptor.write_text(json.dumps(data, indent=2), encoding="utf-8")

    universal_kernel.run_validation(
        [descriptor],
        baseline=universal_kernel.BASELINE_FREQUENCY,
        tolerance=universal_kernel.FREQUENCY_TOLERANCE,
        allowed_kernels=None,
        update=True,
    )

    updated = json.loads(descriptor.read_text(encoding="utf-8"))
    expected_hash = compute_reference_hash()
    expected_frequency = universal_kernel.hash_to_frequency(expected_hash)
    assert updated["hash:sha256"] == expected_hash
    assert pytest.approx(expected_frequency, rel=0, abs=1e-9) == updated["freq:Hz"]


def test_semantic_cycle_detection_raises(tmp_path: Path):
    proof = tmp_path / "alpha.dk"
    proof.write_text("theorem alpha : True := trivial", encoding="utf-8")

    descriptor_a = tmp_path / "a.jsonld"
    descriptor_b = tmp_path / "b.jsonld"

    build_descriptor(
        descriptor_a,
        identifier="urn:qcal:test:alpha",
        proof_path=proof,
        depends_on=["urn:qcal:test:beta"],
        axioms=["AxiomA"],
    )
    build_descriptor(
        descriptor_b,
        identifier="urn:qcal:test:beta",
        proof_path=proof,
        depends_on=["urn:qcal:test:alpha"],
        axioms=["AxiomB"],
    )

    with pytest.raises(UniversalKernelError, match="Semantic dependency cycle detected"):
        universal_kernel.run_validation(
            [descriptor_a, descriptor_b],
            baseline=universal_kernel.BASELINE_FREQUENCY,
            tolerance=universal_kernel.FREQUENCY_TOLERANCE,
            allowed_kernels=["Dedukti"],
            update=False,
        )


def test_logical_layer_requires_structured_proof(tmp_path: Path):
    proof = tmp_path / "ill_formed.dk"
    proof.write_text("This is not a theorem.", encoding="utf-8")

    descriptor = tmp_path / "ill.jsonld"
    build_descriptor(
        descriptor,
        identifier="urn:qcal:test:ill",
        proof_path=proof,
        depends_on=["urn:qcal:base:nat:axioms"],
        axioms=["IllFormed"],
    )

    with pytest.raises(UniversalKernelError, match="fallback validation failed"):
        universal_kernel.run_validation(
            [descriptor],
            baseline=universal_kernel.BASELINE_FREQUENCY,
            tolerance=universal_kernel.FREQUENCY_TOLERANCE,
            allowed_kernels=["Dedukti"],
            update=False,
        )
