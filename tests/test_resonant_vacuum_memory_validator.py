from pathlib import Path
from unittest.mock import Mock, patch

from validate_resonant_vacuum_memory import _validate_lean_formalization


def test_lean_formalization_runs_lake_compiler(tmp_path: Path) -> None:
    lean_file = tmp_path / "QCAL" / "ResonantVacuumMemory.lean"
    lean_file.parent.mkdir()
    lean_file.touch()
    compiler_result = Mock(returncode=0, stdout="", stderr="")

    with patch(
        "validate_resonant_vacuum_memory.subprocess.run",
        return_value=compiler_result,
    ) as run:
        passed, detail = _validate_lean_formalization(lean_file)

    assert passed
    assert detail == "Lean module compiled successfully"
    run.assert_called_once_with(
        ["lake", "env", "lean", "QCAL/ResonantVacuumMemory.lean"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )


def test_lean_formalization_fails_on_compilation_error(tmp_path: Path) -> None:
    lean_file = tmp_path / "QCAL" / "ResonantVacuumMemory.lean"
    lean_file.parent.mkdir()
    lean_file.touch()

    with patch(
        "validate_resonant_vacuum_memory.subprocess.run",
        return_value=Mock(returncode=1, stdout="", stderr="type mismatch"),
    ):
        passed, detail = _validate_lean_formalization(lean_file)

    assert not passed
    assert detail == "type mismatch"


def test_lean_formalization_fails_on_proof_placeholder_warning(
    tmp_path: Path,
) -> None:
    lean_file = tmp_path / "QCAL" / "ResonantVacuumMemory.lean"
    lean_file.parent.mkdir()
    lean_file.touch()

    with patch(
        "validate_resonant_vacuum_memory.subprocess.run",
        return_value=Mock(
            returncode=0,
            stdout="",
            stderr="warning: declaration uses 'sorry'",
        ),
    ):
        passed, detail = _validate_lean_formalization(lean_file)

    assert not passed
    assert "forbidden proof placeholder" in detail


def test_lean_formalization_fails_when_lake_is_unavailable(
    tmp_path: Path,
) -> None:
    lean_file = tmp_path / "QCAL" / "ResonantVacuumMemory.lean"
    lean_file.parent.mkdir()
    lean_file.touch()

    with patch(
        "validate_resonant_vacuum_memory.subprocess.run",
        side_effect=FileNotFoundError("lake"),
    ):
        passed, detail = _validate_lean_formalization(lean_file)

    assert not passed
    assert "Lean compilation could not be completed" in detail
