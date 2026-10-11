"""Small mocked evidence regressions, never assertions of a mathematical proof."""

import json
from pathlib import Path
from types import SimpleNamespace

import pytest
import mpmath as mp

import validate_v5_coronacion as v5
from scripts.validate_sat_certificates import SATCertificateValidator
from verify_environment_integrity import EnvironmentVerifier


@pytest.mark.parametrize("value", [None, float("nan"), float("inf"), float("-inf"), "invalid"])
def test_missing_or_nonfinite_step5_is_unavailable(value) -> None:
    """No threshold or Step 4 may substitute for a Step 5 measurement."""
    evidence = v5.step5_coherence_evidence(SimpleNamespace(step5_coherence=value, step4_coherence=1))
    assert evidence["psi"] is None
    assert evidence["status"] == "UNAVAILABLE" and not evidence["passed"]
    assert "step5" in evidence["source"]
    assert v5.step5_coherence_evidence(None)["psi"] is None


@pytest.mark.parametrize("late_status", ["FAILED", "SKIPPED", "PARTIAL", "UNAVAILABLE"])
def test_required_late_failure_overrides_initial_success(late_status: str) -> None:
    """All counters reflect the final result, including required omitted checks."""
    results = {"early": {"status": "PASSED"}}
    assert v5.summarize_final_results(results, ["early"])["success"]
    results["late"] = {"status": late_status}
    final = v5.summarize_final_results(results, ["early", "late"])
    assert not final["success"] and final["summary"]["total"] == 2
    assert final["unmet_required_checks"] == ["late"]


def test_optional_diagnostics_are_deliberately_separate() -> None:
    """Optional skips/partials do not gate closure, but explicit failures do."""
    results = {"required": {"status": "PASSED"}, "diagnostic": {"status": "SKIPPED"}}
    assert v5.summarize_final_results(results, ["required"])["success"]
    results["diagnostic"]["status"] = "FAILED"
    assert not v5.summarize_final_results(results, ["required"])["success"]


@pytest.mark.parametrize("lean_status", ["SKIPPED", "FAILED", "PASSED"])
def test_ab_numeric_success_is_not_formal_rh_completeness(monkeypatch, lean_status: str) -> None:
    """Actual RH files assume localization; compiling them cannot prove RH."""
    monkeypatch.setattr(v5, "run_lean_file_check", lambda *args: {"status": lean_status})
    monkeypatch.setattr(v5, "compute_141hz_reproducibility_metrics",
                        lambda *args: {"reproducibility_passed": True})
    report = v5.build_ab_operational_report(
        Path(v5.__file__).parent, SimpleNamespace(step5_coherence=1),
        {"Calibrated Explicit Formula Audit": {
            "relative_error_raw": 0.01, "tail_compensation_applied": False,
        }, "Spectral Identification Theorem": {"match_rate": 1},
         "SAT Certificates Verification": {"certificates_validated": 10, "certificates_satisfied": 10}},
    )
    assert report["section_C_numeric_closure"]["numeric_closure_criterion_met"]
    assert not report["formal_criterion_met"] and not report["overall_passed"]
    assert not report["riemann_hypothesis_proven"]
    assert report["section_A_formal_lean"]["conditional_on_axioms"]


def test_consistent_false_sat_is_not_satisfaction(tmp_path: Path, monkeypatch) -> None:
    """Keep the existing consistency API while requiring positive proof evidence."""
    cert = {
        "theorem_name": "example", "timestamp": "2026",
        "sat_formula": {"variables": {"theorem_compiles": None, "no_sorry": True},
                        "satisfied": False},
        "verification": {"compilation": {"compiles": None}},
        "proof_status": {"sorry_count": 0},
    }
    (tmp_path / "SAT_latest.json").write_text(json.dumps(cert))
    validator = SATCertificateValidator(tmp_path, latest_only=True)
    assert validator.verify_sat_formula(cert)[0]
    evidence = v5.sat_satisfaction_evidence(validator, [{"theorem": "example", "all_checks_passed": True}])
    assert evidence[0]["integrity_passed"] and not evidence[0]["satisfied"]
    cert["sat_formula"]["satisfied"] = True
    cert["sat_formula"]["variables"]["theorem_compiles"] = True
    cert["verification"]["compilation"]["compiles"] = True
    (tmp_path / "SAT_latest.json").write_text(json.dumps(cert))
    assert v5.sat_satisfaction_evidence(validator, [{"theorem": "example", "all_checks_passed": True}])[0]["satisfied"]
    cert["timestamp"] = "2025"
    cert["sat_formula"]["satisfied"] = False
    cert["sat_formula"]["variables"]["theorem_compiles"] = False
    (tmp_path / "SAT_older.json").write_text(json.dumps(cert))
    assert len(validator._select_certificate_files()) == 1


def test_raw_formula_audit_does_not_fit_residual(monkeypatch) -> None:
    """The V5 gate must pass compensation=False even though legacy callers can opt in."""
    import validate_explicit_formula as explicit

    def formula(**kwargs):
        assert kwargs["apply_tail_compensation"] is False
        assert kwargs["apply_gaussian_zero_weight"] is False
        assert kwargs["max_zeros"] == 5  # No hidden convergence floor.
        assert abs(kwargs["spectral_transform"](mp.j / 2) -
                   mp.sqrt(mp.pi) * mp.exp(mp.mpf(1) / 16)) < mp.mpf("1e-20")
        return 10, 0.75, 2, 12, [1]

    monkeypatch.setattr(explicit, "weil_explicit_formula", formula)
    audit = v5.run_calibrated_explicit_formula_audit(5, 5, 30)
    assert not audit["criterion_passed"] and audit["relative_error_raw"] == 0.75
    assert not audit["tail_compensation_applied"]


def test_corrupt_latest_sat_cannot_fall_back_to_old(tmp_path: Path) -> None:
    """A tolerant consistency selector must not conceal missing required evidence."""
    (tmp_path / "SAT_corrupt.json").write_text("{")
    validator = SATCertificateValidator(tmp_path, latest_only=True)
    with pytest.raises(ValueError, match="Failed to load certificate"):
        v5.sat_satisfaction_evidence(validator, [])


@pytest.mark.parametrize("psi,lean_status", [(None, "PASSED"), (1, "SKIPPED"), (1, "FAILED")])
def test_ab_requires_psi_and_lean_evidence(tmp_path: Path, monkeypatch, psi, lean_status: str) -> None:
    """Missing Step 5 or required compilation fails even with other successes."""
    lean = tmp_path / "formalization/lean/QCAL"
    lean.mkdir(parents=True)
    for name in ("RH_Equivalence.lean", "QCAL_RH_Complete_Formalization.lean"):
        (lean / name).write_text("theorem example : True := by trivial\n")
    monkeypatch.setattr(v5, "run_lean_file_check", lambda *args: {"status": lean_status})
    monkeypatch.setattr(v5, "compute_141hz_reproducibility_metrics",
                        lambda *args: {"reproducibility_passed": True})
    report = v5.build_ab_operational_report(tmp_path, SimpleNamespace(step5_coherence=psi), {
        "Calibrated Explicit Formula Audit": {"relative_error_raw": 0, "tail_compensation_applied": False},
        "Spectral Identification Theorem": {"match_rate": 1},
        "SAT Certificates Verification": {"certificates_validated": 10, "certificates_satisfied": 10},
    })
    assert report["formal_criterion_met"] == (lean_status == "PASSED")
    assert report["section_C_numeric_closure"]["numeric_closure_criterion_met"]
    assert report["section_B_observational_reproducibility"]["psi_coherence"]["psi"] == psi
    assert not report["overall_passed"]


def test_missing_tracked_checksum_file_fails(tmp_path: Path) -> None:
    """A ledger entry is required even if it isn't a standard lock filename."""
    (tmp_path / "environment_checksums.json").write_text(json.dumps({"missing.txt": "0" * 64}))
    verifier = EnvironmentVerifier()
    verifier.repo_root = tmp_path
    assert not verifier.verify_checksums()
    assert any("Required file not found" in error for error in verifier.errors)


def test_missing_recorded_dataset_fails(tmp_path: Path) -> None:
    """Recorded dataset evidence must not silently disappear."""
    (tmp_path / "ENV.lock").write_text(
        "# DATASET CHECKSUMS\n# missing.csv:\n#   " + "0" * 64 + "\n"
    )
    verifier = EnvironmentVerifier()
    verifier.repo_root = tmp_path
    assert not verifier.verify_dataset_checksums()
    assert verifier.errors
