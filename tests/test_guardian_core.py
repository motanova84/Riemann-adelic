#!/usr/bin/env python3
"""
Tests for Guardian Core Module

Tests the central orchestration module for QCAL ∞³ ecosystem monitoring.

Author: José Manuel Mota Burruezo
Date: December 2025
"""

import pytest
import json
import os
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noesis_guardian.guardian_core import GuardianCore, Notifier


class TestNotifier:
    """Test Notifier class."""

    def test_alert_does_not_raise(self):
        """Test that alert method runs without error."""
        # Should not raise
        Notifier.alert("Test alert", {"key": "value"})

    def test_info_does_not_raise(self):
        """Test that info method runs without error."""
        Notifier.info("Test info")

    def test_success_does_not_raise(self):
        """Test that success method runs without error."""
        Notifier.success("Test success")


class TestGuardianCoreConstants:
    """Test GuardianCore class constants."""

    def test_qcal_coherence_constant(self):
        """Test that QCAL coherence constant is 244.36."""
        assert GuardianCore.QCAL_COHERENCE == 244.36

    def test_fundamental_frequency(self):
        """Test that fundamental frequency is 141.7001 Hz."""
        assert GuardianCore.FUNDAMENTAL_FREQUENCY == 141.7001


class TestGuardianCoreInit:
    """Test GuardianCore initialization."""

    def test_init_default_log_dir(self):
        """Test initialization with default log directory."""
        guardian = GuardianCore()
        assert guardian.log_dir == "data"
        assert guardian.results_log == []

    def test_init_custom_log_dir(self):
        """Test initialization with custom log directory."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)
            assert guardian.log_dir == tmpdir


class TestGuardianCoreCalabiyauCheck:
    """Test Calabi-Yau resonance check."""

    def test_run_calabi_yau_check_missing_data(self):
        """Test CY check with missing data."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)
            result = guardian.run_calabi_yau_check(
                os.path.join(tmpdir, 'nonexistent.json')
            )
            assert result['status'] == 'missing_data'

    def test_run_calabi_yau_check_with_data(self):
        """Test CY check with valid data."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            # Create test spectrum file
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {
                'eigenvalues': [14.13, 21.02, 25.01, 30.42, 32.94]
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = guardian.run_calabi_yau_check(test_file)
            assert result['status'] in ['ok', '⚠️ anomaly']


class TestGuardianCoreFullCheck:
    """Test full guardian check."""

    def test_run_full_check_returns_expected_keys(self):
        """Test that full check returns all expected keys."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            # Create test spectrum file
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {
                'eigenvalues': [14.13, 21.02, 25.01]
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = guardian.run_full_check(test_file)

            expected_keys = [
                'timestamp', 'guardian_version', 'qcal_constants',
                'calabi_yau_resonance', 'overall_status', 'message'
            ]
            for key in expected_keys:
                assert key in result, f"Missing key: {key}"

    def test_run_full_check_updates_results_log(self):
        """Test that full check updates results log."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            assert len(guardian.results_log) == 0
            guardian.run_full_check(test_file)
            assert len(guardian.results_log) == 1

    def test_run_full_check_timestamp_format(self):
        """Test that timestamp is in ISO format with Z suffix."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = guardian.run_full_check(test_file)
            assert result['timestamp'].endswith('Z')


class TestGuardianCoreSaveReport:
    """Test report saving functionality."""

    def test_save_report_creates_file(self):
        """Test that save_report creates a JSON file."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)
            report = {
                'timestamp': '2025-01-01T00:00:00Z',
                'status': 'ok'
            }

            filepath = guardian.save_report(report, 'test_report.json')
            assert os.path.exists(filepath)

            with open(filepath) as f:
                saved = json.load(f)
            assert saved['status'] == 'ok'

    def test_save_report_default_filename(self):
        """Test that save_report generates timestamp-based filename."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)
            report = {
                'timestamp': '2025-01-01T00:00:00Z',
                'status': 'ok'
            }

            filepath = guardian.save_report(report)
            assert os.path.exists(filepath)
            assert 'guardian_report' in filepath


class TestGuardianCoreGetLatestReport:
    """Test latest report retrieval."""

    def test_get_latest_report_empty(self):
        """Test getting latest report when no reports exist."""
        guardian = GuardianCore()
        result = guardian.get_latest_report()
        assert result is None

    def test_get_latest_report_after_check(self):
        """Test getting latest report after running a check."""
        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            guardian.run_full_check(test_file)
            result = guardian.get_latest_report()

            assert result is not None
            assert 'timestamp' in result


class TestGuardianCoreIntegration:
    """Integration tests with actual data."""

    @pytest.fixture
    def spectrum_file(self):
        """Get path to the spectrum file if it exists."""
        path = 'data/spectrum_Hpsi.json'
        if os.path.exists(path):
            return path
        return None

    def test_full_workflow(self, spectrum_file):
        """Test complete workflow with real data."""
        if spectrum_file is None:
            pytest.skip("spectrum_Hpsi.json not found")

        with TemporaryDirectory() as tmpdir:
            guardian = GuardianCore(log_dir=tmpdir)

            # Run full check
            report = guardian.run_full_check(spectrum_file)

            # Verify report structure
            assert report['overall_status'] in ['ok', 'anomaly']
            assert 'calabi_yau_resonance' in report
            assert report['qcal_constants']['C'] == 244.36
            assert report['qcal_constants']['f0_hz'] == 141.7001

            # Save report
            filepath = guardian.save_report(report, 'integration_test.json')
            assert os.path.exists(filepath)

            # Get latest report
            latest = guardian.get_latest_report()
            assert latest == report


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])
