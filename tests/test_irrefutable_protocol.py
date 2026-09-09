"""Tests for strict irrefutable formal+numeric protocol."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from core.validate_weil_spectral_bridge import SpectralAuditResult, WeilAuditResult
from sabio_infinity4 import SABIO_Infinity4
from validation.irrefutable_protocol import IrrefutableProtocol
from validation.rh_ds_core import ValidationResult, ValidationStatus


def test_sabio_core_invariant_fails_if_lean_structure_is_missing(monkeypatch):
    sabio = SABIO_Infinity4()
    monkeypatch.setattr(sabio, "_validar_formalizacion_lean_elan_omega", lambda: False)
    with pytest.raises(RuntimeError, match="Lean ELAN OMEGA"):
        sabio.assert_core_invariants()


def test_sabio_core_invariant_fails_if_beacon_programming_breaks(monkeypatch):
    sabio = SABIO_Infinity4()
    monkeypatch.setattr(sabio, "_validar_formalizacion_lean_elan_omega", lambda: True)
    monkeypatch.setattr(sabio, "_validar_programacion_sabio", lambda: False)
    with pytest.raises(RuntimeError, match="beacon/coherence/DOI"):
        sabio.assert_core_invariants()


def test_formal_gates_fail_when_required_lean_file_missing(tmp_path):
    repo = tmp_path
    (repo / "formalization" / "lean" / "QCAL_Hadamard").mkdir(parents=True)
    (repo / "formalization" / "lean" / "lean-toolchain").write_text("leanprover/lean4:4.5.0")
    # Create GAP files with no sorry to isolate missing ELAN OMEGA file failure.
    for gap in [
        "GAP1_log_holomorphic_of_entire_never_zero.lean",
        "GAP2_affine_log_of_order_one.lean",
        "GAP3_quotient_entire_never_zero.lean",
        "GAP4_order_atMostOne_of_quotient.lean",
    ]:
        (repo / "formalization" / "lean" / "QCAL_Hadamard" / gap).write_text("theorem t : True := by trivial")
    (repo / "formalization" / "lean" / "RiemannAdelic").mkdir(parents=True)
    (repo / "formalization" / "lean" / "RiemannAdelic" / "Coronacion_Final.lean").write_text("theorem t : True := by trivial")

    protocol = IrrefutableProtocol(repo_root=repo, precision=20, max_zeros=20)
    report = protocol.run_formal_gates()
    assert report["passed"] is False
    assert any("elan_omega_pure_validation.lean" in gate["name"] and not gate["passed"] for gate in report["gates"])


def test_numeric_gates_fail_without_sat_latest_report(monkeypatch, tmp_path):
    protocol = IrrefutableProtocol(repo_root=tmp_path, precision=20, max_zeros=20)

    ok_result = ValidationResult(
        test_name="x",
        status=ValidationStatus.PASSED,
        metrics={},
        details="ok",
        timestamp="t",
    )

    monkeypatch.setattr(
        "validation.irrefutable_protocol.RiemannHypothesisValidator.validate_critical_line_zeros",
        lambda self, max_zeros: ok_result,
    )
    monkeypatch.setattr(
        "validation.irrefutable_protocol.RiemannHypothesisValidator.validate_ds_equiv_xi",
        lambda self: ok_result,
    )
    monkeypatch.setattr(
        "validation.irrefutable_protocol.RiemannHypothesisValidator.validate_non_vanishing_property",
        lambda self: ok_result,
    )

    monkeypatch.setattr(
        "validation.irrefutable_protocol.run_bridge_validation",
        lambda **kwargs: (
            WeilAuditResult(10, 100, 3, 0.05, 250.0, 1.0, 1.0, 0.01, True),
            SpectralAuditResult(10, 0.1, 1.0, 10.0, 0.95, True),
            True,
        ),
    )
    monkeypatch.setattr(
        "validation.irrefutable_protocol.build_and_persist_zero_chain",
        lambda *args, **kwargs: {
            "source": "mock",
            "zero_count": 20,
            "residual_tolerance": 1e-7,
            "max_residual": 0.0,
            "chain_hash_sha512": "a" * 128,
            "tip_hash_sha512": "b" * 128,
            "chain_verification": {"valid": True, "error": None},
            "output_path": "data/validation/critical_zero_immutable_chain.json",
        },
    )
    numeric = protocol.run_numeric_gates()
    assert numeric["sat_latest_only"]["passed"] is False
    assert numeric["critical_zero_chain"]["passed"] is True
    assert numeric["passed"] is False
