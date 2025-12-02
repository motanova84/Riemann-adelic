#!/usr/bin/env python3
"""
Tests for NOESIS GUARDIAN 2.0
=============================

Test suite for the NOESIS Guardian monitoring and auto-repair system.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
import os
import sys
import tempfile
from pathlib import Path

import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))


class TestRepoWatcher:
    """Tests for the RepoWatcher module."""

    def test_watcher_import(self):
        """Test that watcher can be imported."""
        from noesis_guardian.watcher import RepoWatcher
        assert RepoWatcher is not None

    def test_watcher_scan_repo(self):
        """Test repository scanning."""
        from noesis_guardian.watcher import RepoWatcher
        watcher = RepoWatcher()
        state = watcher.scan_repo()

        assert "timestamp" in state
        assert "collisions" in state
        assert "missing" in state
        assert "lean_status" in state
        assert "critical_files" in state
        assert "critical_dirs" in state

    def test_watcher_critical_files(self):
        """Test critical files detection."""
        from noesis_guardian.watcher import RepoWatcher
        watcher = RepoWatcher()

        # Check that critical files list is defined
        assert len(watcher.CRITICAL_FILES) > 0
        assert ".qcal_beacon" in watcher.CRITICAL_FILES

    def test_watcher_git_status(self):
        """Test git status detection."""
        from noesis_guardian.watcher import RepoWatcher
        watcher = RepoWatcher()
        state = watcher.scan_repo()

        git_status = state.get("git_status", {})
        assert "branch" in git_status
        assert "uncommitted" in git_status
        assert "untracked" in git_status


class TestSpectralMonitor:
    """Tests for the SpectralMonitor module."""

    def test_spectral_import(self):
        """Test that spectral monitor can be imported."""
        from noesis_guardian.spectral_monitor import SpectralMonitor
        assert SpectralMonitor is not None

    def test_spectral_constants(self):
        """Test spectral constants."""
        from noesis_guardian.spectral_monitor import SpectralMonitor
        monitor = SpectralMonitor()

        assert monitor.F0_HZ == 141.7001
        assert monitor.COHERENCE_CONSTANT == 244.36
        assert abs(monitor.FRACTAL_RATIO - 68/81) < 1e-10

    def test_spectral_coherence_check(self):
        """Test spectral coherence checking."""
        from noesis_guardian.spectral_monitor import SpectralMonitor
        monitor = SpectralMonitor()
        coherence = monitor.check_spectral_coherence()

        assert "timestamp" in coherence
        assert "coherent" in coherence
        assert "f0_status" in coherence
        assert "xi_symmetry" in coherence
        assert "fractal_status" in coherence
        assert "h_psi_status" in coherence

    def test_noesis_signal(self):
        """Test NOESIS signal computation."""
        from noesis_guardian.spectral_monitor import SpectralMonitor
        monitor = SpectralMonitor()
        signal = monitor.compute_noesis_signal()

        assert "timestamp" in signal
        assert "heartbeat_hz" in signal
        assert signal["heartbeat_hz"] == 141.7001
        assert "state" in signal
        assert signal["state"] in ["vivo", "parcial", "crítico"]
        assert "vitality" in signal
        assert 0 <= signal["vitality"] <= 1
        assert "equation" in signal

    def test_spectral_metrics(self):
        """Test spectral metrics."""
        from noesis_guardian.spectral_monitor import SpectralMonitor
        monitor = SpectralMonitor()
        metrics = monitor.get_spectral_metrics()

        assert metrics["f0_hz"] == 141.7001
        assert metrics["coherence_constant"] == 244.36
        assert metrics["fractal_period"] == 9


class TestAutoRepairEngine:
    """Tests for the AutoRepairEngine module."""

    def test_repair_import(self):
        """Test that repair engine can be imported."""
        from noesis_guardian.autorepair_engine import AutoRepairEngine
        assert AutoRepairEngine is not None

    def test_repair_full_repair(self):
        """Test full repair execution."""
        from noesis_guardian.autorepair_engine import AutoRepairEngine
        engine = AutoRepairEngine()

        # Test with clean state
        test_state = {
            "collisions": 0,
            "missing": 0,
            "lean_status": "ok",
            "critical_files": {},
        }

        report = engine.full_repair(test_state)
        assert "timestamp" in report
        assert "actions" in report
        assert "success" in report
        assert report["success"] is True

    def test_repair_operators(self):
        """Test operator repair check."""
        from noesis_guardian.autorepair_engine import AutoRepairEngine
        engine = AutoRepairEngine()
        result = engine.repair_operators()

        assert "action" in result
        assert result["action"] == "repair_operators"
        assert "status" in result
        assert "operators" in result

    def test_repair_spectral_coherence(self):
        """Test spectral coherence repair."""
        from noesis_guardian.autorepair_engine import AutoRepairEngine
        engine = AutoRepairEngine()
        result = engine.repair_spectral_coherence()

        assert "action" in result
        assert result["action"] == "repair_spectral_coherence"
        assert "status" in result


class TestNotifier:
    """Tests for the Notifier module."""

    def test_notifier_import(self):
        """Test that notifier can be imported."""
        from noesis_guardian.ai_notifier import Notifier
        assert Notifier is not None

    def test_notifier_alert(self):
        """Test alert sending."""
        from noesis_guardian.ai_notifier import Notifier
        result = Notifier.alert("Test alert", {"test": True})

        assert "timestamp" in result
        assert "message" in result
        assert "channels" in result
        assert "console" in result["channels"]

    def test_notifier_logging(self):
        """Test logging functions."""
        from noesis_guardian.ai_notifier import Notifier

        # These should not raise exceptions
        Notifier.info("Test info message")
        Notifier.warning("Test warning message")
        Notifier.error("Test error message")


class TestSabioBridge:
    """Tests for the SabioBridge module."""

    def test_sabio_import(self):
        """Test that SABIO bridge can be imported."""
        from noesis_guardian.sabio_bridge import SabioBridge
        assert SabioBridge is not None

    def test_sabio_constants(self):
        """Test SABIO constants."""
        from noesis_guardian.sabio_bridge import SabioBridge

        assert SabioBridge.SABIO_FREQUENCY == 141.7001
        assert SabioBridge.SABIO_COHERENCE == 244.36
        assert SabioBridge.SABIO_VERSION == "∞⁴"

    def test_sabio_status(self):
        """Test SABIO status retrieval."""
        from noesis_guardian.sabio_bridge import SabioBridge
        status = SabioBridge.get_sabio_status()

        assert "version" in status
        assert "frequency" in status
        assert "coherence" in status
        assert "status" in status

    def test_sabio_update_state(self):
        """Test state update."""
        from noesis_guardian.sabio_bridge import SabioBridge
        result = SabioBridge.update_state({"test": True})

        assert result["success"] is True
        assert "timestamp" in result

    def test_sabio_insert_seed(self):
        """Test seed insertion."""
        from noesis_guardian.sabio_bridge import SabioBridge
        result = SabioBridge.insert_seed("test", {"value": 42})

        assert result["success"] is True
        assert "seed_id" in result

    def test_sabio_sync_infinity(self):
        """Test infinity synchronization."""
        from noesis_guardian.sabio_bridge import SabioBridge
        result = SabioBridge.sync_with_infinity()

        assert "infinity_level" in result
        assert result["infinity_level"] == 3
        assert result["symbol"] == "∞³"


class TestAikSync:
    """Tests for the AikSync module."""

    def test_aik_import(self):
        """Test that AIK sync can be imported."""
        from noesis_guardian.aik_sync import AikSync
        assert AikSync is not None

    def test_aik_constants(self):
        """Test AIK constants."""
        from noesis_guardian.aik_sync import AikSync

        assert AikSync.F0_HZ == 141.7001
        assert AikSync.ALGORITHM == "SHA3-256"

    def test_aik_sync_certificate(self):
        """Test certificate synchronization."""
        from noesis_guardian.aik_sync import AikSync
        result = AikSync.sync_certificate({
            "timestamp": "2025-01-01T00:00:00Z",
            "spectral": {"coherent": True},
        })

        assert result["success"] is True
        assert "certificate" in result
        cert = result["certificate"]
        assert "id" in cert
        assert "hash" in cert
        assert "algorithm" in cert
        assert cert["algorithm"] == "SHA3-256"
        assert "symbolic_signature" in cert
        assert cert["symbolic_signature"].startswith("∞³-")

    def test_aik_verify_certificate(self):
        """Test certificate verification."""
        from noesis_guardian.aik_sync import AikSync

        # Generate a certificate
        result = AikSync.sync_certificate({"test": True})
        cert = result["certificate"]

        # Verify it
        verification = AikSync.verify_certificate(cert)
        assert verification["valid"] is True


class TestGuardianCore:
    """Tests for the GuardianCore module."""

    def test_guardian_import(self):
        """Test that guardian core can be imported."""
        from noesis_guardian.guardian_core import NoesisGuardian
        assert NoesisGuardian is not None

    def test_guardian_constants(self):
        """Test guardian constants."""
        from noesis_guardian.guardian_core import NoesisGuardian

        assert NoesisGuardian.F0_HZ == 141.7001
        assert NoesisGuardian.COHERENCE_CONSTANT == 244.36

    def test_guardian_initialization(self):
        """Test guardian initialization."""
        from noesis_guardian.guardian_core import NoesisGuardian
        guardian = NoesisGuardian()

        assert guardian.watcher is not None
        assert guardian.repair is not None
        assert guardian.spectral is not None

    def test_guardian_quick_check(self):
        """Test quick check functionality."""
        from noesis_guardian.guardian_core import NoesisGuardian
        guardian = NoesisGuardian()
        result = guardian.quick_check()

        assert "timestamp" in result
        assert "healthy" in result
        assert "coherent" in result
        assert "signal_state" in result
        assert "vitality" in result

    def test_guardian_noesis_signal(self):
        """Test NOESIS signal from guardian."""
        from noesis_guardian.guardian_core import NoesisGuardian
        guardian = NoesisGuardian()
        signal = guardian.noesis_signal()

        assert "heartbeat_hz" in signal
        assert signal["heartbeat_hz"] == 141.7001
        assert "state" in signal

    def test_guardian_status(self):
        """Test guardian status retrieval."""
        from noesis_guardian.guardian_core import NoesisGuardian
        guardian = NoesisGuardian()
        status = guardian.get_status()

        assert "running" in status
        assert "cycles" in status
        assert "f0_hz" in status
        assert status["f0_hz"] == 141.7001


class TestDashboard:
    """Tests for the Dashboard module."""

    def test_dashboard_import(self):
        """Test that dashboard can be imported."""
        from noesis_guardian.panel.dashboard import Dashboard
        assert Dashboard is not None

    def test_dashboard_data(self):
        """Test dashboard data retrieval."""
        from noesis_guardian.panel.dashboard import Dashboard
        dashboard = Dashboard()
        data = dashboard.get_dashboard_data()

        assert "timestamp" in data
        assert "heartbeat" in data
        assert "spectral" in data
        assert "repository" in data
        assert "lean" in data
        assert "metrics" in data

    def test_dashboard_heartbeat(self):
        """Test heartbeat data."""
        from noesis_guardian.panel.dashboard import Dashboard
        dashboard = Dashboard()
        heartbeat = dashboard.get_heartbeat()

        assert heartbeat["frequency_hz"] == 141.7001
        assert heartbeat["status"] == "active"

    def test_dashboard_text_render(self):
        """Test text dashboard rendering."""
        from noesis_guardian.panel.dashboard import Dashboard
        dashboard = Dashboard()
        text = dashboard.render_text_dashboard()

        assert "NOESIS GUARDIAN" in text
        assert "141.7001" in text
        assert "HEARTBEAT" in text


class TestRuleset:
    """Tests for the ruleset configuration."""

    def test_ruleset_exists(self):
        """Test that ruleset.json exists."""
        ruleset_path = Path(__file__).resolve().parents[1] / "noesis_guardian" / "ruleset.json"
        assert ruleset_path.exists()

    def test_ruleset_valid_json(self):
        """Test that ruleset is valid JSON."""
        ruleset_path = Path(__file__).resolve().parents[1] / "noesis_guardian" / "ruleset.json"
        with open(ruleset_path, "r", encoding="utf-8") as f:
            ruleset = json.load(f)

        assert "version" in ruleset
        assert "constants" in ruleset
        assert "monitoring" in ruleset
        assert "repair" in ruleset

    def test_ruleset_constants(self):
        """Test ruleset constants."""
        ruleset_path = Path(__file__).resolve().parents[1] / "noesis_guardian" / "ruleset.json"
        with open(ruleset_path, "r", encoding="utf-8") as f:
            ruleset = json.load(f)

        constants = ruleset["constants"]
        assert constants["f0_hz"] == 141.7001
        assert constants["coherence_constant"] == 244.36
        assert constants["fractal_period"] == 9


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
