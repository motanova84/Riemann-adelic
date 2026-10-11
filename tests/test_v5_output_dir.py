"""Artifact-routing regressions, not evidence for mathematical validation."""

import builtins
import importlib
import json
import os
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock

import pytest

import validate_v5_coronacion as v5
from scripts.validate_sat_certificates import SATCertificateValidator
from utils import qcal_spectral_certificate as spectral

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("save_certificate", [False, True])
@pytest.mark.parametrize("override", [False, True])
@pytest.mark.parametrize("refresh", [False, True])
def test_v5_artifact_routes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, save_certificate: bool, override: bool, refresh: bool,
) -> None:
    """Exercise all saving branches without running or claiming numerical proofs."""
    framework = importlib.import_module("tests.test_coronacion_v5")
    for cls in (framework.TestCoronacionV5, framework.TestV5Integration):
        for name in dir(cls):
            if name.startswith("test_"):
                monkeypatch.setattr(cls, name, lambda self: None)
    monkeypatch.setattr(framework.TestCoronacionV5, "_generate_v5_proof_certificate", lambda self: {})
    real_import = builtins.__import__
    allowed = {
        "tests.test_coronacion_v5", "scripts.validate_sat_certificates",
        "utils.qcal_spectral_certificate",
    }

    def routing_import(name: str, *args, **kwargs):
        """Keep supplemental numerical validations out of a filesystem unit test."""
        if (
            name.startswith(("utils.", "operators.", "physics"))
            or name in {"zeta_quantum_wave", "rh_proved_framework"}
        ) and name not in allowed:
            raise ImportError("supplemental numerical validation excluded from routing test")
        return real_import(name, *args, **kwargs)

    monkeypatch.setattr(builtins, "__import__", routing_import)
    monkeypatch.setattr(importlib.util, "spec_from_file_location", Mock(side_effect=ImportError("routing test")))
    monkeypatch.setattr(v5, "include_yolo_verification", lambda: True)
    monkeypatch.setattr(v5, "run_calibrated_explicit_formula_audit", lambda **kwargs: {
        "criterion_passed": True, "relative_error_raw": 0.01, "target_relative_error": 0.05,
        "tail_compensation_applied": False, "zeros_used": 5, "zero_weight_sigma": 50,
    })
    monkeypatch.setattr(v5, "__file__", str(tmp_path / "validate_v5_coronacion.py"))
    (tmp_path / "verify_environment_integrity.py").write_text("# Mocked checker\n")
    monkeypatch.setattr(v5.subprocess, "run", Mock(return_value=SimpleNamespace(
        returncode=1, stdout="warning: integrity failure", stderr="",
    )))
    monkeypatch.chdir(tmp_path)
    input_dir = tmp_path / "certificates" / "sat"
    input_dir.mkdir(parents=True)
    (input_dir / "SAT_example.json").write_text('{"theorem_name": "routing"}')
    monkeypatch.setattr(SATCertificateValidator, "validate_certificate", lambda self, cert: {
        "theorem": cert["theorem_name"], "all_checks_passed": False,
    })
    spectral_call = Mock(return_value=SimpleNamespace(
        all_criteria_satisfied=False, ontological_precision_achieved=False,
        hilbert_polya_confirmed=False, coherence_verified=False,
    ))
    monkeypatch.setattr(spectral, "generate_spectral_certificate", spectral_call)
    ab_call = Mock(return_value={
        "overall_passed": False, "formal_criterion_met": False,
        "section_B_observational_reproducibility": {
            "spectral_metrics_141hz": {"reproducibility_passed": False},
            "psi_coherence": {"passed": False},
        },
    })
    monkeypatch.setattr(v5, "build_ab_operational_report", ab_call)
    output_dir = tmp_path / "nested" / "outputs" if override else None
    # Exercise the actual logger with isolated legacy and override destinations.
    real_logger = v5.ValidationLogger
    logger_call = Mock(side_effect=lambda script, **options: real_logger(
        script, **(options or {"log_dir": tmp_path / "logs" / "validation"}),
    ))
    monkeypatch.setattr(v5, "ValidationLogger", logger_call)

    # An isolated refresh must be audited instead of the original SAT directory.
    refreshed_dir = output_dir / "sat" if override and refresh else None
    if refreshed_dir is not None:
        refreshed_dir.mkdir(parents=True)
        (refreshed_dir / "SAT_refreshed.json").write_text('{"theorem_name": "refreshed"}')
    result = v5.validate_v5_coronacion(30, False, save_certificate, 5, 5, output_dir, refreshed_dir)
    assert result["success"] is False
    assert result["results"]["Step 1: Axioms → Lemmas"]["status"] == "PASSED"
    assert result["results"]["Environment Integrity"]["status"] == "FAILED"
    assert result["results"]["Environment Integrity"]["returncode"] == 1
    assert result["results"]["SAT Certificates Verification"]["status"] == "FAILED"
    assert result["results"]["A+B Operational Report"]["status"] == "FAILED"
    assert result["summary"]["total"] == len(result["results"])
    assert result["summary"]["failed"] == sum(
        item["status"] == "FAILED" for item in result["results"].values()
    )

    destination = output_dir if override else tmp_path / "data"
    assert (destination / "validation_results.csv").is_file()
    assert (destination / "qcal_ab_operational_report.json").is_file()
    assert (destination / "v5_coronacion_certificate.json").exists() == save_certificate
    if save_certificate:
        saved = json.loads((destination / "v5_coronacion_certificate.json").read_text())
        assert saved["success"] is False
        assert saved["riemann_hypothesis_status"] == "NOT_PROVEN"
        assert saved["validation_results"]["A+B Operational Report"]["status"] == "FAILED"
        assert saved["summary"] == result["summary"]
    assert spectral_call.call_args.kwargs["save_to_file"] == save_certificate
    assert spectral_call.call_args.kwargs["output_dir"] == output_dir
    assert ab_call.call_args.kwargs["repo_root"] == tmp_path
    report_dir = output_dir / "sat" if override else input_dir
    assert (report_dir / "validation_report.json").is_file()
    assert json.loads((report_dir / "validation_report.json").read_text())["results"][0]["theorem"] == (
        "refreshed" if refreshed_dir is not None else "routing"
    )
    log_dir = (output_dir if override else tmp_path) / "logs" / "validation"
    assert list(log_dir.glob("validate_v5_coronacion_*.log"))
    assert list(log_dir.glob("*.json"))
    if override:
        assert not (tmp_path / "data").exists()
        assert not (input_dir / "validation_report.json").exists()
        assert logger_call.call_args.kwargs["log_dir"] == log_dir
    else:
        assert logger_call.call_args.kwargs == {}


@pytest.mark.parametrize("override", [False, True])
def test_sat_separate_inputs_and_reports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, override: bool,
) -> None:
    """Report routing must not change which SAT files are selected."""
    inputs = tmp_path / "inputs"
    inputs.mkdir()
    source = inputs / "SAT_example.json"
    source.write_text('{"theorem_name": "input", "timestamp": "2026"}')
    reports = tmp_path / "nested" / "reports" if override else None
    validator = SATCertificateValidator(inputs, True, reports)
    monkeypatch.setattr(validator, "validate_certificate", lambda cert: {
        "theorem": cert["theorem_name"], "all_checks_passed": True,
    })
    assert validator._select_certificate_files() == [source]
    assert validator.validate_all_certificates()[0]["theorem"] == "input"
    report = (reports if override else inputs) / "validation_report.json"
    assert json.loads(report.read_text())["total_certificates"] == 1
    assert source.read_text() == '{"theorem_name": "input", "timestamp": "2026"}'
    if override:
        assert not (inputs / "validation_report.json").exists()


@pytest.mark.parametrize("update_manifest", [False, True])
@pytest.mark.parametrize("override", [False, True])
def test_v5_cli_routes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, update_manifest: bool, override: bool,
) -> None:
    """Refresh generation, post-refresh validation and V5 share the new SAT input."""
    output = tmp_path / "nested" / "cli"
    argv = ["validate_v5_coronacion.py", "--precision", "30", "--save-certificate"]
    if override:
        argv += ["--output-dir", str(output)]
    if update_manifest:
        argv += ["--update-manifest"]
    monkeypatch.setattr(sys, "argv", argv)
    run = Mock(return_value=SimpleNamespace(returncode=0, stdout="", stderr=""))
    monkeypatch.setattr(v5.subprocess, "run", run)
    validate = Mock(return_value={"success": False})
    monkeypatch.setattr(v5, "validate_v5_coronacion", validate)
    with pytest.raises(SystemExit) as exit_info:
        v5.main()
    assert exit_info.value.code == 1
    assert validate.call_args.kwargs["output_dir"] == (output if override else None)
    expected_inputs = output / "sat" if update_manifest and override else None
    assert validate.call_args.kwargs["sat_certificates_dir"] == expected_inputs
    assert validate.call_args.kwargs["save_certificate"] is True
    assert run.call_count == (2 if update_manifest else 0)
    if expected_inputs is not None:
        generate, audit = [call.args[0] for call in run.call_args_list]
        assert generate[-2:] == ["--output-dir", str(expected_inputs)]
        assert audit[-4:] == [
            "--certificates-dir", str(expected_inputs),
            "--report-output-dir", str(expected_inputs),
        ]
    elif update_manifest:
        assert "--output-dir" not in run.call_args_list[0].args[0]
        assert "--certificates-dir" not in run.call_args_list[1].args[0]


@pytest.mark.parametrize("failure_stage", [0, 1])
def test_manifest_failure_stops_before_v5(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure_stage: int,
) -> None:
    """Do not run V5 against stale inputs after a failed refresh."""
    monkeypatch.setattr(sys, "argv", [
        "validate_v5_coronacion.py", "--update-manifest", "--output-dir", str(tmp_path),
    ])
    success = SimpleNamespace(returncode=0, stdout="", stderr="")
    failure = SimpleNamespace(returncode=2, stdout="", stderr="refresh/audit failed")
    monkeypatch.setattr(v5.subprocess, "run", Mock(side_effect=[success] * failure_stage + [failure]))
    validate = Mock()
    monkeypatch.setattr(v5, "validate_v5_coronacion", validate)
    with pytest.raises(SystemExit, match="2"):
        v5.main()
    validate.assert_not_called()


def test_explicit_formula_import_does_not_write(tmp_path: Path) -> None:
    """Importing the formula from a directory without data must create no CSV."""
    env = dict(os.environ, PYTHONPATH=str(ROOT), MPLCONFIGDIR=str(tmp_path / "matplotlib"))
    result = subprocess.run(
        [sys.executable, "-c", "import validate_explicit_formula"],
        cwd=tmp_path, env=env, capture_output=True, text=True, timeout=60,
    )
    assert result.returncode == 0, result.stderr
    assert not (tmp_path / "data").exists()


def test_spectral_cli_output_dir(tmp_path: Path) -> None:
    """The actual standalone spectral CLI saves only to the nested destination."""
    output = tmp_path / "nested" / "spectral"
    result = subprocess.run(
        [sys.executable, "-m", "utils.qcal_spectral_certificate", "--precision", "30",
         "--n-zeros", "3", "--quiet", "--output-dir", str(output)],
        cwd=ROOT, capture_output=True, text=True, timeout=60,
    )
    # A partial mathematical certificate may legitimately exit with status 1.
    assert result.returncode in (0, 1), result.stderr
    cert = json.loads((output / "qcal_spectral_certificate.json").read_text())
    assert cert["title"].startswith("QCAL-∞³-SPECTRAL")


def test_sat_cli_separate_report_output(tmp_path: Path) -> None:
    """The actual SAT CLI never writes its report into the specified input dir."""
    inputs = tmp_path / "inputs"
    inputs.mkdir()
    source = inputs / "SAT_invalid.json"
    source.write_text('{"theorem_name": "invalid", "file_info": {"path": "missing"}}')
    output = tmp_path / "nested" / "reports"
    result = subprocess.run(
        [sys.executable, "scripts/validate_sat_certificates.py", "--all", "--latest-only",
         "--certificates-dir", str(inputs), "--report-output-dir", str(output)],
        cwd=ROOT, capture_output=True, text=True, timeout=60,
    )
    assert result.returncode == 1, result.stderr
    assert json.loads((output / "validation_report.json").read_text())["failed"] == 1
    assert not (inputs / "validation_report.json").exists()


@pytest.mark.parametrize("save", [False, True])
def test_spectral_legacy_destination(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, save: bool,
) -> None:
    """Default saving remains module-relative; disabling saving creates nothing."""
    monkeypatch.setattr(spectral, "__file__", str(tmp_path / "utils" / "certificate.py"))
    spectral.generate_spectral_certificate(30, 3, save, False)
    assert (tmp_path / "data" / "qcal_spectral_certificate.json").exists() == save
