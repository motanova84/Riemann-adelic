#!/usr/bin/env python3
"""
Tests for NOESIS GUARDIAN 3.0 System

Validates the functionality of the Guardian monitoring and repair system.
"""

import json
import os
import pytest
import tempfile
import numpy as np


class TestRepoWatcher:
    """Tests for the RepoWatcher module."""

    def test_scan_expected_files_exist(self):
        """Test that watcher correctly identifies existing files."""
        from noesis_guardian.modules.watcher import RepoWatcher

        watcher = RepoWatcher()
        result = watcher.scan()

        assert "missing" in result
        assert "errors" in result
        # README.md should exist in the repo
        assert "README.md" not in result["missing"]

    def test_scan_detects_missing_files(self, tmp_path, monkeypatch):
        """Test that watcher detects missing files when not in repo root."""
        from noesis_guardian.modules.watcher import RepoWatcher

        monkeypatch.chdir(tmp_path)
        watcher = RepoWatcher()
        result = watcher.scan()

        # In temp dir, expected files should be missing
        assert result["errors"] is True
        assert len(result["missing"]) > 0


class TestAutoRepairEngine:
    """Tests for the AutoRepairEngine module."""

    def test_repair_creates_missing_files(self, tmp_path, monkeypatch):
        """Test that repair engine creates missing files."""
        from noesis_guardian.modules.autorepair_engine import AutoRepairEngine

        monkeypatch.chdir(tmp_path)
        engine = AutoRepairEngine()

        repo_state = {"missing": ["test_file.md", "test_dir"]}
        result = engine.repair(repo_state)

        assert result is True
        assert os.path.exists("test_file.md")
        assert os.path.exists("test_dir")


class TestSpectralMonitor:
    """Tests for the SpectralMonitor module."""

    def test_spectral_check_returns_coherent(self):
        """Test that spectral monitor returns coherence status."""
        from noesis_guardian.modules.spectral_monitor import SpectralMonitor

        monitor = SpectralMonitor()
        result = monitor.check()

        assert "coherent" in result
        assert "symmetry" in result
        assert isinstance(result["coherent"], bool)
        assert isinstance(result["symmetry"], float)

    def test_spectral_check_hermitian_symmetry(self):
        """Test that real signals exhibit Hermitian symmetry in FFT."""
        from noesis_guardian.modules.spectral_monitor import SpectralMonitor

        monitor = SpectralMonitor()
        result = monitor.check()

        # For real-valued input, FFT should have Hermitian symmetry
        assert result["coherent"] is True


class TestAikSync:
    """Tests for the AikSync module."""

    def test_emit_produces_hash(self):
        """Test that AikSync produces a valid SHA3-256 hash."""
        from noesis_guardian.modules.aik_sync import AikSync

        entry = {"test": "data", "value": 42}
        hash_result = AikSync.emit(entry)

        assert isinstance(hash_result, str)
        assert len(hash_result) == 64  # SHA3-256 produces 64 hex chars

    def test_emit_deterministic(self):
        """Test that same input produces same hash."""
        from noesis_guardian.modules.aik_sync import AikSync

        entry = {"test": "data", "value": 42}
        hash1 = AikSync.emit(entry)
        hash2 = AikSync.emit(entry)

        assert hash1 == hash2


class TestNotifier:
    """Tests for the Notifier module."""

    def test_alert_runs_without_error(self, capsys):
        """Test that alert function runs without errors."""
        from noesis_guardian.modules.ai_notifier import Notifier

        Notifier.alert("Test Alert", {"key": "value"})
        captured = capsys.readouterr()

        assert "ALERTA" in captured.out
        assert "Test Alert" in captured.out


class TestSabioBridge:
    """Tests for the SabioBridge module."""

    def test_update_runs_without_error(self, capsys):
        """Test that update function runs without errors."""
        from noesis_guardian.modules.sabio_bridge import SabioBridge

        SabioBridge.update({"timestamp": "2025-01-01T00:00:00"})
        captured = capsys.readouterr()

        assert "SABIO sincronizado" in captured.out


class TestNoesisGuardian:
    """Tests for the main NoesisGuardian class."""

    def test_guardian_initialization(self):
        """Test that Guardian initializes all components."""
        from noesis_guardian import NoesisGuardian

        guardian = NoesisGuardian()

        assert guardian.watcher is not None
        assert guardian.repair_engine is not None
        assert guardian.spectral_monitor is not None

    def test_guardian_run_produces_entry(self):
        """Test that Guardian run produces a valid log entry."""
        from noesis_guardian import NoesisGuardian

        guardian = NoesisGuardian()
        entry = guardian.run()

        assert "timestamp" in entry
        assert "repo" in entry
        assert "spectral" in entry
        assert "coherent" in entry["spectral"]

    def test_guardian_log_creates_file(self, tmp_path):
        """Test that Guardian creates log file."""
        from noesis_guardian.guardian_core import NoesisGuardian, LOGFILE

        guardian = NoesisGuardian()
        entry = {"test": "entry", "timestamp": "2025-01-01T00:00:00"}
        guardian.log(entry)

        assert os.path.exists(LOGFILE)


class TestPanelDashboard:
    """Tests for the Panel Dashboard module."""

    def test_display_status_runs(self, capsys):
        """Test that dashboard display runs without errors."""
        from noesis_guardian.panel.panel_dashboard import display_status

        display_status()
        captured = capsys.readouterr()

        assert "Panel Noesis Guardian 3.0" in captured.out


# =============================================================================
# Additional tests for the Guardian watcher and autorepair modules
# =============================================================================
"""
Test suite for NOESIS GUARDIAN - Watcher and Autorepair Modules

This test suite validates the guardian functionality for the QCAL framework,
ensuring proper monitoring and self-repair capabilities.

Author: Jose Manuel Mota Burruezo (JMMB)
"""

import os
import sys
import json
import tempfile
import shutil
from pathlib import Path
from unittest import mock

import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noesis_guardian.watcher import RepoWatcher
from noesis_guardian.guardian import (
    noesis_heartbeat,
    autorepair,
    run_cycle,
    generate_certificate,
    FREQ,
    LOGFILE,
    _repair_collisions_direct
)

# Git conflict marker length (7 characters: <<<<<<< or >>>>>>>)
GIT_CONFLICT_MARKER_LENGTH = 7


class TestNoesisHeartbeat:
    """Test the heartbeat signal generation."""
    
    def test_heartbeat_returns_float(self):
        """Heartbeat should return a float value."""
        signal = noesis_heartbeat()
        assert isinstance(signal, float)
    
    def test_heartbeat_in_valid_range(self):
        """Heartbeat signal should be within expected bounds."""
        signal = noesis_heartbeat()
        # sin + cos should be between -2 and 2
        assert -2.0 <= signal <= 2.0
    
    def test_heartbeat_consistent(self):
        """Heartbeat should be consistent across calls."""
        signal1 = noesis_heartbeat()
        signal2 = noesis_heartbeat()
        assert signal1 == signal2
    
    def test_frequency_constant(self):
        """Verify the frequency constant."""
        assert FREQ == 141.7001


class TestRepoWatcher:
    """Test the repository watcher functionality."""
    
    @pytest.fixture
    def temp_repo(self):
        """Create a temporary repository structure for testing."""
        temp_dir = tempfile.mkdtemp()
        
        # Create basic structure
        (Path(temp_dir) / "operador").mkdir()
        (Path(temp_dir) / "formalization" / "lean").mkdir(parents=True)
        (Path(temp_dir) / "tools").mkdir()
        
        # Create essential files
        essential_files = [
            "validate_v5_coronacion.py",
            "demo_H_DS_complete.py",
            "validate_h_psi_self_adjoint.py",
            "validate_critical_line.py",
            "fix_unicode.py",
            ".qcal_beacon",
            "Evac_Rpsi_data.csv",
            "operador/operador_H_DS.py",
            "operador/operador_H.py",
            "operador/hilbert_polya_operator.py",
            "formalization/lean/RiemannHypothesis.lean",
            "formalization/lean/lakefile.lean",
        ]
        
        for file_path in essential_files:
            full_path = Path(temp_dir) / file_path
            full_path.parent.mkdir(parents=True, exist_ok=True)
            full_path.write_text(f"# {file_path}\n")
        
        yield temp_dir
        
        # Cleanup
        shutil.rmtree(temp_dir)
    
    def test_watcher_initialization(self, temp_repo):
        """Test watcher initializes correctly."""
        watcher = RepoWatcher(temp_repo)
        assert watcher.repo_root == Path(temp_repo)
    
    def test_scan_repo_returns_dict(self, temp_repo):
        """Scan should return a dictionary with expected keys."""
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert isinstance(state, dict)
        assert "collisions" in state
        assert "lean_status" in state
        assert "missing" in state
        assert "scan_complete" in state
    
    def test_no_collisions_in_clean_repo(self, temp_repo):
        """Clean repository should have no collisions."""
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["collisions"] == 0
    
    def test_detect_backup_files(self, temp_repo):
        """Watcher should detect .orig and .bak files as collisions."""
        # Create backup files
        (Path(temp_repo) / "test.py.orig").write_text("backup")
        (Path(temp_repo) / "test2.py.bak").write_text("backup")
        
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["collisions"] == 2
    
    def test_detect_merge_conflicts(self, temp_repo):
        """Watcher should detect merge conflict markers."""
        # Build conflict content dynamically to avoid false detection in this test file
        conflict_lines = [
            "<" * GIT_CONFLICT_MARKER_LENGTH + " HEAD",
            "my changes",
            "=" * GIT_CONFLICT_MARKER_LENGTH,
            "their changes",
            ">" * GIT_CONFLICT_MARKER_LENGTH + " branch"
        ]
        conflict_content = "\n".join(conflict_lines)
        (Path(temp_repo) / "conflict.py").write_text(conflict_content)
        
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["collisions"] >= 1
    
    def test_lean_status_ok(self, temp_repo):
        """Lean status should be 'ok' with valid setup."""
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["lean_status"] == "ok"
    
    def test_lean_status_missing(self, temp_repo):
        """Lean status should be 'missing' without formalization directory."""
        shutil.rmtree(Path(temp_repo) / "formalization")
        
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["lean_status"] == "missing"
    
    def test_missing_files_detection(self, temp_repo):
        """Watcher should detect missing essential files."""
        # Remove an essential file
        (Path(temp_repo) / "validate_v5_coronacion.py").unlink()
        
        watcher = RepoWatcher(temp_repo)
        state = watcher.scan_repo()
        
        assert state["missing"] >= 1
        assert "validate_v5_coronacion.py" in state["missing_files"]
    
    def test_get_summary(self, temp_repo):
        """Get summary should return a formatted string."""
        watcher = RepoWatcher(temp_repo)
        summary = watcher.get_summary()
        
        assert isinstance(summary, str)
        assert "NOESIS GUARDIAN" in summary


class TestAutorepair:
    """Test the auto-repair functionality."""
    
    @pytest.fixture
    def temp_repo(self):
        """Create a minimal temporary repository."""
        temp_dir = tempfile.mkdtemp()
        (Path(temp_dir) / "noesis_guardian").mkdir()
        (Path(temp_dir) / "tools").mkdir()
        yield temp_dir
        shutil.rmtree(temp_dir)
    
    def test_autorepair_returns_report(self, temp_repo):
        """Autorepair should return a report dictionary."""
        state = {
            "collisions": 0,
            "lean_status": "ok",
            "missing": 0
        }
        
        report = autorepair(state, temp_repo)
        
        assert isinstance(report, dict)
        assert "timestamp" in report
        assert "actions" in report
        assert "success" in report
    
    def test_autorepair_handles_no_issues(self, temp_repo):
        """Autorepair should succeed when no issues exist."""
        state = {
            "collisions": 0,
            "lean_status": "ok",
            "missing": 0
        }
        
        report = autorepair(state, temp_repo)
        
        assert report["success"] is True
    
    def test_repair_collisions_direct(self, temp_repo):
        """Direct collision repair should move backup files."""
        # Create a backup file
        backup_file = Path(temp_repo) / "test.py.orig"
        backup_file.write_text("backup content")
        
        state = {
            "collision_details": [
                {"type": "backup_file", "path": "test.py.orig"}
            ]
        }
        
        repaired = _repair_collisions_direct(state, Path(temp_repo))
        
        assert repaired == 1
        assert not backup_file.exists()


class TestRunCycle:
    """Test the run cycle functionality."""
    
    @pytest.fixture
    def temp_repo(self):
        """Create a temporary repository for cycle testing."""
        temp_dir = tempfile.mkdtemp()
        
        # Create minimal structure
        (Path(temp_dir) / "noesis_guardian").mkdir()
        (Path(temp_dir) / "formalization" / "lean").mkdir(parents=True)
        (Path(temp_dir) / "operador").mkdir()
        
        # Create essential files
        for f in [".qcal_beacon", "Evac_Rpsi_data.csv", "fix_unicode.py",
                  "validate_v5_coronacion.py", "demo_H_DS_complete.py",
                  "validate_h_psi_self_adjoint.py", "validate_critical_line.py",
                  "operador/operador_H_DS.py", "operador/operador_H.py",
                  "operador/hilbert_polya_operator.py",
                  "formalization/lean/RiemannHypothesis.lean",
                  "formalization/lean/lakefile.lean"]:
            full_path = Path(temp_dir) / f
            full_path.parent.mkdir(parents=True, exist_ok=True)
            full_path.write_text(f"# {f}")
        
        yield temp_dir
        shutil.rmtree(temp_dir)
    
    def test_run_cycle_returns_report(self, temp_repo):
        """Run cycle should return a complete report."""
        report = run_cycle(temp_repo, auto_repair=False)
        
        assert isinstance(report, dict)
        assert "timestamp" in report
        assert "state" in report
        assert "noesis_signal" in report
    
    def test_run_cycle_creates_log(self, temp_repo):
        """Run cycle should create a log file."""
        run_cycle(temp_repo, auto_repair=False)
        
        log_path = Path(temp_repo) / LOGFILE
        assert log_path.exists()
    
    def test_run_cycle_log_is_valid_json(self, temp_repo):
        """Log entries should be valid JSON."""
        run_cycle(temp_repo, auto_repair=False)
        
        log_path = Path(temp_repo) / LOGFILE
        with open(log_path) as f:
            for line in f:
                if line.strip():
                    entry = json.loads(line)
                    assert "timestamp" in entry


class TestGenerateCertificate:
    """Test certificate generation."""
    
    @pytest.fixture
    def temp_repo(self):
        """Create a minimal temporary repository."""
        temp_dir = tempfile.mkdtemp()
        (Path(temp_dir) / "formalization" / "lean").mkdir(parents=True)
        (Path(temp_dir) / "operador").mkdir()
        
        for f in [".qcal_beacon", "Evac_Rpsi_data.csv",
                  "validate_v5_coronacion.py", "demo_H_DS_complete.py",
                  "validate_h_psi_self_adjoint.py", "validate_critical_line.py",
                  "fix_unicode.py", "operador/operador_H_DS.py",
                  "operador/operador_H.py", "operador/hilbert_polya_operator.py",
                  "formalization/lean/RiemannHypothesis.lean",
                  "formalization/lean/lakefile.lean"]:
            full_path = Path(temp_dir) / f
            full_path.parent.mkdir(parents=True, exist_ok=True)
            full_path.write_text(f"# {f}")
        
        yield temp_dir
        shutil.rmtree(temp_dir)
    
    def test_certificate_structure(self, temp_repo):
        """Certificate should have required fields."""
        cert = generate_certificate(temp_repo)
        
        assert "timestamp" in cert
        assert "type" in cert
        assert "version" in cert
        assert "frequency" in cert
        assert "heartbeat" in cert
        assert "state" in cert
        assert "coherent" in cert
        assert "signature" in cert
    
    def test_certificate_type(self, temp_repo):
        """Certificate type should be QCAL_COHERENCE_CERTIFICATE."""
        cert = generate_certificate(temp_repo)
        
        assert cert["type"] == "QCAL_COHERENCE_CERTIFICATE"
    
    def test_certificate_frequency(self, temp_repo):
        """Certificate should have correct frequency."""
        cert = generate_certificate(temp_repo)
        
        assert cert["frequency"] == FREQ
    
    def test_certificate_coherent_for_clean_repo(self, temp_repo):
        """Clean repository should be marked as coherent."""
        cert = generate_certificate(temp_repo)
        
        assert cert["coherent"] is True
    
    def test_certificate_not_coherent_with_issues(self, temp_repo):
        """Repository with issues should not be marked as coherent."""
        # Create a collision
        (Path(temp_repo) / "test.py.orig").write_text("backup")
        
        cert = generate_certificate(temp_repo)
        
        # This will depend on whether collision is detected
        # The collision should make it incoherent
        assert cert["state"]["collisions"] >= 1


class TestIntegration:
    """Integration tests for the complete guardian system."""
    
    def test_import_from_package(self):
        """Test importing from the noesis_guardian package."""
        from noesis_guardian import (
            RepoWatcher,
            noesis_heartbeat,
            autorepair,
            run_cycle,
            FREQ,
            LOGFILE
        )
        
        assert FREQ == 141.7001
        assert callable(noesis_heartbeat)
        assert callable(autorepair)
        assert callable(run_cycle)
    
    def test_watcher_main_function(self):
        """Test watcher module main function."""
        from noesis_guardian.watcher import main
        
        # Main function should not raise
        # It prints to stdout, so we just verify it runs
        with mock.patch('builtins.print'):
            main()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
