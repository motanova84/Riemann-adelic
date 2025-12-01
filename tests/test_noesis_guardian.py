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
